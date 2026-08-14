(ns urd.consensus.node
  "The core consensus abstraction: a node is a pure state machine.

  A `Node` maps (state, input) to a new state plus a vector of *effects* --
  data describing side effects for a runtime or simulator to interpret. No
  algorithm here performs I/O, reads a clock, or draws a random number; all
  three are effects, which is what makes runs deterministic and replayable.

  ## Why the core is a DAG and not a log

  The obvious shape -- \"a log of decided values at increasing heights\" -- cannot
  express three of the algorithms we target, so we do not use it. The core is
  fork choice over a vertex DAG plus a finality predicate:

    - vertices carry parent links and a payload;
    - a fork-choice rule maps known vertices and votes to the current head;
    - a finality rule identifies the irreversible prefix;
    - an eligibility rule says who may extend, and with what weight.

  Crucially, `:commit` is *revocable*. That is not a proof-of-work concession:
  Raft needs it too, because a new leader forces followers to truncate a
  conflicting uncommitted suffix (Raft thesis 5.3) -- which is a revert. Bitcoin
  reorgs, and Bullshark retroactively commits earlier anchors. Only Tendermint
  has absolute finality, and it is the degenerate case rather than the model.

  ## Purity rules

  1. No `println`, no clock, no RNG, no I/O inside `init` or `step`.
  2. Signature verification happens OUTSIDE the state machine. ClojureScript's
     Web Crypto is promise-based, so `geheimnis` Ed25519 verification returns a
     channel and cannot be called from a pure function. Events therefore arrive
     already authenticated, carrying `:verified-by`. (Hashing is different:
     `hasch/sha256` is synchronous on both platforms, so proof-of-work checks
     CAN run inline.)
  3. Effects are values. Two runs with the same inputs produce equal effects."
  (:require [clojure.set :as set]))

;; ============================================================
;; The protocol
;; ============================================================

(defprotocol Node
  "A consensus algorithm as a pure state machine."

  (init [this config]
    "Create the initial state.

    Returns {:state s :effects fx}. Returning effects matters: a node may need
    to persist hard state or arm a timer before it can safely do anything else.")

  (step [this state input]
    "Advance the machine by one input.

    `input` is an event map (see below) or a tick. Returns {:state s' :effects fx}.

    An implementation MAY run an internal fixpoint -- applying its own rules
    repeatedly until none fires, accumulating effects. Stellar SCP requires
    this: accepting one statement can unlock several further checks, so
    one-transition-per-event is not expressive enough. The loop runs over
    immutable state inside a pure function, so determinism is preserved.

    An implementation MAY return no effects and still commit. Bullshark's
    ordering layer sends zero messages -- the total order is a deterministic
    function of the DAG -- so a runtime that assumes \"a decision is preceded by
    a vote round\" would not fit it."))

;; ============================================================
;; Events -- what a node reacts to
;; ============================================================

(defn message-received
  "A message from a peer that has ALREADY been authenticated.

  `verified-by` is the set of peer-ids whose signatures were checked at the
  edge. The state machine must never see an unverified signature; see the
  namespace docstring.

  Note `(vote -> signature)` is NOT a function: signatures from remote signers
  can be non-deterministic (CometBFT carries an explicit
  ErrVoteNonDeterministicSignature for exactly this). So the raw signature is
  retained and equality of votes must not be inferred from equality of bytes."
  [from msg verified-by]
  {:type :message-received :from from :msg msg :verified-by verified-by})

(defn timer-fired
  "A logical timer expired. Timers are counted in ticks, never milliseconds."
  [timer-id]
  {:type :timer-fired :timer-id timer-id})

(defn sampled
  "Response to a `sample` effect.

  `peers` is a BAG (a map of peer-id -> multiplicity), not a set. Avalanche
  samples stake weight without replacement, which means node indices CAN
  repeat, and the multiplicity is that node's vote weight in the poll. Treating
  it as a set silently changes the protocol."
  [request-id peers]
  {:type :sampled :request-id request-id :peers peers})

(defn persisted
  "Response to a `persist-then` effect: the write is durable.

  `epoch` is the witness the effect was issued under. A completion whose epoch
  no longer matches the node's current epoch MUST be treated as a no-op, not an
  error -- this defeats an ABA hazard where two in-flight writes cover the same
  indices across a leader change (etcd-raft solves it the same way, by
  attaching the term to the storage response and dropping stale ones)."
  [token epoch]
  {:type :persisted :token token :epoch epoch})

(defn value-ready
  "Response to a `request-value` effect: the application supplied a payload."
  [value]
  {:type :value-ready :value value})

(defn vertex-received
  "A vertex (block / certificate / proposal) arrived and was authenticated."
  [vertex]
  {:type :vertex-received :vertex vertex})

(defn instance-event
  "Route an event to a named sub-machine.

  One HoneyBadger ACS round runs N reliable-broadcasts and N binary-agreements
  concurrently, each ABA with an unbounded sequence of internal rounds. Without
  instance addressing that protocol is not expressible at all, which is why it
  is in the core from the start rather than retrofitted. Raft's per-peer
  progress and Snowman's per-block instances are the degenerate one-level case."
  [instance-id inner]
  {:type :instance :instance-id instance-id :inner inner})

(defn tick
  "Logical clock advance. Distinct from a timer firing: some algorithms (notably
  HoneyBadger, which is fully asynchronous) never set a timer at all."
  [n]
  {:type :tick :n n})

;; ============================================================
;; Effects -- what a node asks the world to do
;; ============================================================

(defn send-to
  "UNICAST a message to one peer.

  Absent from the previous design, which had only broadcast. Raft's AppendEntries
  is per-peer with per-peer progress state, and Snowman queries exactly the k
  sampled peers. This was the single biggest structural gap."
  [to msg]
  [:send {:to to :msg msg}])

(defn broadcast
  "Send a message to all peers on a topic."
  [topic msg]
  [:broadcast {:topic topic :msg msg}])

(defn persist-then
  "Durably write `writes`, THEN emit `then`.

  This is the durability barrier, and the rule for what belongs behind it was
  arrived at independently by two reference implementations:

    - etcd-raft gates exactly {MsgAppResp, MsgVoteResp, MsgPreVoteResp};
    - CometBFT fsyncs exactly the messages this node SIGNS, plus the
      end-height marker.

  Stated once: gate exactly the messages that constitute this node's binding
  commitment; send everything else immediately.

  `durable?` distinguishes fsync from a buffered write. Not everything needs
  fsync -- etcd-raft's MustSync is (entries non-empty OR vote changed OR term
  changed); a commit-index change alone is recoverable by replay and does not.

  `truncate-from`, when present, says the log must drop entries at or above that
  index before appending. etcd-raft leaves this IMPLICIT -- the storage layer has
  to infer a truncation from an append at a lower index -- which is a classic
  source of storage bugs. We make it explicit.

  `epoch` is echoed back in the `persisted` event; see that function."
  [{:keys [writes durable? epoch truncate-from then]
    :or {durable? true then []}}]
  [:persist-then (cond-> {:writes writes :durable? durable? :epoch epoch :then then}
                   truncate-from (assoc :truncate-from truncate-from))])

(defn sample
  "Ask for `k` peers, drawn by the runtime/simulator.

  Randomness is an effect so the simulator owns the seed and a failing run is
  reproducible. The reply is a BAG -- see `sampled`."
  [request-id k from]
  [:sample {:request-id request-id :k k :from from}])

(defn set-timer
  "Arm a logical timer, measured in ticks.

  Deliberately not milliseconds: wall-clock timers make timeout behaviour
  unsimulatable, and timeouts are exactly where consensus bugs live."
  [timer-id after-ticks]
  [:set-timer {:timer-id timer-id :after-ticks after-ticks}])

(defn cancel-timer [timer-id]
  [:cancel-timer {:timer-id timer-id}])

(defn request-value
  "Ask the application for a payload to propose."
  [context]
  [:request-value {:context context}])

(defn commit
  "Commit an ORDERED SEQUENCE of vertices.

  Not one value at one height. Bullshark's commit rule can, on a single
  certificate, commit an anchor and then retroactively back-fill several
  earlier anchors together with their whole sub-DAGs -- potentially hundreds of
  vertices at once. `index` is a globally increasing consensus index, decoupled
  from round or height."
  [vertices index]
  [:commit {:vertices (vec vertices) :index index}])

(defn revert
  "Roll the committed prefix back to `to-vertex`.

  Cheap on a copy-on-write substrate: reverting is moving a branch pointer to an
  older commit, because the blocks are immutable and still in the store. btcd
  confirms the principle from the other side -- at the header layer its undo log
  is empty, since every consensus quantity is a fold over the ancestor path. All
  of Bitcoin's two-phase reorg machinery exists only because its UTXO set is a
  destructively mutated map."
  [to-vertex]
  [:revert {:to-vertex to-vertex}])

(defn report-equivocation
  "Report provable misbehaviour by a peer.

  A first-class protocol action, not a dropped message: in CometBFT a
  conflicting vote becomes evidence that is gossiped and slashed on, and
  HoneyBadger's reliable broadcast treats a caught equivocation as an outcome."
  [peer evidence]
  [:report-equivocation {:peer peer :evidence evidence}])

(defn log-effect
  "Emit a diagnostic. Note this is an EFFECT, so the state machine stays pure --
  the previous implementation called `println` inside its transition functions,
  which broke both replay determinism and ClojureScript output."
  [level message]
  [:log {:level level :message message}])

(defn instance-effect
  "Wrap an effect produced by a sub-machine. See `instance-event`."
  [instance-id inner]
  [:instance {:instance-id instance-id :inner inner}])

;; ============================================================
;; Working with results
;; ============================================================

(def empty-result {:state nil :effects []})

(defn result
  "Build a transition result."
  ([state] {:state state :effects []})
  ([state effects] {:state state :effects (vec effects)}))

(defn add-effects
  "Append effects to a result."
  [res & fx]
  (update res :effects into (remove nil? (flatten fx))))

(defn fixpoint
  "Apply `f` (state -> {:state :effects}) until the state stops changing.

  This is how an algorithm runs an internal fixpoint safely: `f` must be pure
  and monotone enough to terminate. SCP needs this because accepting one
  statement unlocks further checks.

  `max-iterations` guards against a non-converging rule set; exceeding it is a
  bug in the algorithm, so we surface it rather than looping forever."
  ([f state] (fixpoint f state 100))
  ([f state max-iterations]
   (loop [s state, acc [], i 0]
     (if (>= i max-iterations)
       (throw (ex-info "fixpoint did not converge"
                       {:iterations i :state s}))
       (let [{s' :state fx :effects} (f s)]
         (if (= s' s)
           {:state s :effects (into acc (or fx []))}
           (recur s' (into acc (or fx [])) (inc i))))))))

;; ============================================================
;; Instance addressing
;; ============================================================

(defn dispatch-instance
  "Run `inner-step` for one sub-machine and re-wrap its effects.

  `state` holds sub-machine states under [:instances instance-id]."
  [state instance-id inner-step inner-input]
  (let [sub (get-in state [:instances instance-id])
        {sub' :state fx :effects} (inner-step sub inner-input)]
    {:state (assoc-in state [:instances instance-id] sub')
     :effects (mapv #(instance-effect instance-id %) (or fx []))}))

;; ============================================================
;; Membership -- trust is protocol-supplied, not a number
;; ============================================================

(defprotocol Membership
  "How a node decides whether a set of peers is decisive.

  Deliberately NOT `(quorum-size validator-set)`. In Stellar SCP quorum-ness is
  not a cardinality at all: it is a greatest fixpoint over other nodes'
  advertised trust configurations, so it is transitive and subjective. Note also
  the asymmetry -- `v-blocking?` is local and cardinality-dual, while `quorum?`
  is transitive.

  Standard BFT supplies |S| > 2n/3; Raft supplies a majority; Nakamoto supplies
  a cumulative-work rule; SCP supplies the fixpoint. One protocol, four
  instantiations."

  (quorum? [this state statements pred]
    "Do the statements satisfying `pred` constitute a quorum?

    Takes a PREDICATE over statements, not a count: SCP's federated voting calls
    the same machinery with three different predicates (voted; voted-or-accepted;
    accepted).

    Returns true, false, or :unknown. The third case is real -- SCP routinely
    receives a statement whose quorum set it has never fetched, and cannot
    decide until it does. No classical BFT algorithm has an undecidable safety
    check; SCP does.")

  (v-blocking? [this state statements pred]
    "Can the statements satisfying `pred` block this node from ever reaching a
    quorum? Local; no other node's configuration is consulted.")

  (weight [this state peer-id]
    "This peer's weight: stake, work, or 1 for the uniform case."))

(defrecord ThresholdMembership [threshold-fn]
  Membership
  (quorum? [_ state statements pred]
    (let [n (count (:validators state))
          k (count (filter pred statements))]
      (>= k (threshold-fn n))))
  (v-blocking? [_ state statements pred]
    ;; A set blocks if its complement can no longer reach the threshold.
    (let [n (count (:validators state))
          k (count (filter pred statements))]
      (> k (- n (threshold-fn n)))))
  (weight [_ _ _] 1))

(defn byzantine-threshold
  "floor(2n/3) + 1 -- the Byzantine quorum.

  Its defining property is quorum intersection: any two quorums share strictly
  more than f members, hence at least one honest one. Machine-checked in ansatz
  as `quorum-intersection`."
  [n]
  (inc (quot (* 2 n) 3)))

(defn majority-threshold
  "floor(n/2) + 1 -- the crash-fault quorum.

  Weaker than `byzantine-threshold` for every n >= 5; they coincide only at
  n in #{1,2,4}."
  [n]
  (inc (quot n 2)))

(defn byzantine-tolerance
  "f = floor((n-1)/3), the number of Byzantine faults n validators tolerate.

  Note f=0 for n<4: three validators tolerate NO Byzantine faults, so a
  3-node cluster is a crash-fault configuration only."
  [n]
  (quot (max 0 (dec n)) 3))

(def bft-membership (->ThresholdMembership byzantine-threshold))
(def cft-membership (->ThresholdMembership majority-threshold))

;; ============================================================
;; Effect classification (used by runtimes and the simulator)
;; ============================================================

(def ^:private outbound-effects #{:send :broadcast})

(defn effect-kind [effect] (first effect))
(defn effect-params [effect] (second effect))

(defn outbound?
  "Does this effect put a message on the network?"
  [effect]
  (contains? outbound-effects (effect-kind effect)))

(defn deferred-effects
  "The effects an interpreter must hold until a `persist-then` completes."
  [effect]
  (when (= :persist-then (effect-kind effect))
    (:then (effect-params effect))))

(defn unwrap-instance
  "Peel instance wrappers off an effect, returning [path inner-effect]."
  [effect]
  (loop [e effect, path []]
    (if (= :instance (effect-kind e))
      (let [{:keys [instance-id inner]} (effect-params e)]
        (recur inner (conj path instance-id)))
      [path e])))
