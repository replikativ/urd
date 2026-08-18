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

  `:commit` is *revocable* -- but by ONE algorithm, and this paragraph used to
  claim otherwise. It said Raft needs revocation too, because a new leader makes
  followers truncate a conflicting suffix; that suffix is UNCOMMITTED, and
  discarding an uncommitted entry is not revoking a decision. It said Bullshark
  needs it, because it retroactively commits earlier anchors; that is a
  multi-vertex commit, not a revert. And it called Tendermint the degenerate
  case.

  Seven implementations later the capability declarations say what is true:
  Raft, Tendermint, SCP, Bullshark and Snowman declare no `:revert` at all.
  Nakamoto is the only one, and open membership is exactly why. Absolute
  finality is the common case and reorgs are the exception -- the reverse of
  what was assumed when the DAG shape was chosen.

  The DAG shape survives that correction, because it was never justified by
  revocation alone: Bullshark's ordering is over a certificate DAG, Nakamoto's
  fork choice is over a block tree, and Snowman's is over a block tree with a
  trie inside each node. A height-indexed log expresses none of the three.

  Note also that revocability and PROBABILISTIC finality are different axes,
  which is not the intuition. Snowman's safety is parameterised and its
  acceptance is absorbing: a consumer needs an assumption about k, alpha and
  beta, and no code for a decision being taken back. Only the second belongs in
  a type, which is what `capabilities` encodes.

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
    a vote round\" would not fit it.")

  (capabilities [this]
    "Which effects this algorithm may emit, as `{:emits #{...}}`.

    Required, not optional, and an interpreter refuses a node that will not say.
    Three things it buys, none of which is achievable by reading the code:

    1. **A consumer learns statically whether `:revert` can reach it.** That is
       the one question about finality that changes an interface. Whether a
       decision is FINAL-with-probability or final-given-a-threshold is an
       assumption a consumer reasons with; whether a decision can be TAKEN BACK
       is something it must have code for. Of the seven algorithms here, exactly
       one revokes -- see section 21 of the design doc for the table.

    2. **Undeclared effects are refused at the interpreter**, so the declaration
       is checked on every run rather than being a comment.

    3. **Dead vocabulary becomes visible.** An effect that no declaration
       mentions is one nothing uses, which is a fact about the protocol worth
       being able to see."))

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

(defn deliver-self
  "Hand an input back to this same node, without going through the network.

  Added after implementing Raft, which could not otherwise express etcd's
  self-addressed `MsgAppResp` (`raft.go:845`). That trick is worth having: the
  leader models its OWN durability as a message from itself to itself, delayed
  by the fsync, which removes the leader/follower asymmetry from commit-index
  advancement entirely -- the leader's entry counts toward the quorum only once
  its own write is durable, exactly like everyone else's.

  `[:send {:to self}]` is NOT a substitute. It traverses the network, where a
  configured drop rate can lose it, and etcd's own invariant is that a message
  in `msgs` may never be self-addressed (`raft.go:595-597`).

  Delivered at the next tick rather than inline, so a node cannot recurse into
  itself within a single step. Never dropped, never partitioned. Placed inside
  `persist-then`'s `:then` it gives exactly the etcd semantics."
  [input]
  [:deliver-self {:input input}])

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

  `epoch` is echoed back in the `persisted` event; see that function.

  `checkpoint`, when present, is a VECTOR OF RECORDS that REPLACES the log
  rather than extending it. Append-only storage is what makes replay a faithful
  reconstruction, and it is also what makes the log grow without bound: a node
  whose in-memory state is compacted still replays every write ever issued.
  A checkpoint is the escape: it says the log from here on is exactly these
  records, and the algorithm supplies them because only the algorithm knows
  what its own state compresses to.

  It is a key on the BARRIER rather than a fourteenth effect because it needs
  every property the barrier already has: fsync before anything gated goes out,
  an epoch, a token to correlate on, and a `then`. A separate effect would have
  had to restate all of them, and a checkpoint that is not durable before the
  old log is dropped is exactly the crash that loses the log.

  `:writes` is ignored when `checkpoint` is present -- the records carry their
  own. `store/checkpoint!` is responsible for making the swap atomic; see its
  docstring for why the manifest flip is the ordering that matters.

  `token` is supplied BY THE CALLER and echoed back unchanged. It was originally
  minted by the interpreter, which meant a node could not correlate a completion
  with the write that caused it -- so an algorithm with more than one write in
  flight had to assume the interpreter completes them in issue order, an
  ordering the protocol never promised. Raft surfaced this. Supply whatever
  correlates for you; it is opaque here."
  [{:keys [writes durable? epoch truncate-from then token checkpoint]
    :or {durable? true then []}}]
  [:persist-then (cond-> {:writes writes :durable? durable? :epoch epoch :then then}
                   truncate-from (assoc :truncate-from truncate-from)
                   token (assoc :token token)
                   checkpoint (assoc :checkpoint (vec checkpoint)))])

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
  vertices at once.

  There is NO index. There was one, and it never meant anything a consumer could
  use. Section 12 recorded that it could not be both a globally increasing
  consensus index and the position of these vertices in the committed prefix --
  Raft, Snowman and Tendermint make those coincide, a reorg pulls them apart --
  and resolved it by choosing position. That resolution was a guess about a
  consumer we did not have yet.

  Measured before removing it: the simulator never read the field, and the only
  test that did asserted the sequence was NOT monotone. Written by all six
  algorithms, read by none, and its sole test documented that it did not mean
  what it was defined to mean.

  Position is implicit -- these vertices go on the end of the committed prefix,
  and `revert` is what moves that end backwards. Where an algorithm has an index
  that IS meaningful in its own terms -- Raft's log index, SCP's slot,
  Nakamoto's height -- it belongs on the vertex, where a consumer can read it
  knowing which scheme it is in."
  [vertices]
  [:commit {:vertices (vec vertices)}])

(defn resync
  "Replace the committed prefix wholesale with `vertices`.

  NOT a revert, and separating the two is the point. A restarting node has to
  tell an interpreter what it now believes its committed prefix to be, and it
  cannot express that as a revocation: it does not know what the interpreter
  holds, so it has nothing to name as dropped and no vertex to revert TO.

  Bullshark did this with `(revert ::genesis [])` followed by a commit, relying
  on an empty `:dropped` meaning \"truncate to this vertex, whatever you hold\"
  and on a never-committed vertex truncating to nothing. That worked, and it
  made one effect mean two unrelated things -- I changed my mind about a
  decision, and ignore what you have, here is my state. An interpreter could not
  distinguish them, a consumer could not react differently to them, and the
  `:dropped` check that makes `revert` safe had to be disabled (by passing `[]`)
  for the case that is not a revert at all.

  So this is its own effect. `revert` now has exactly one user and exactly one
  meaning, and an algorithm that never revokes a decision can say so."
  [vertices]
  [:resync {:vertices (vec vertices)}])

(defn revert
  "Roll the committed prefix back to `to-vertex`, dropping `dropped`.

  REVOCATION, and nothing else -- a decision this node previously reported as
  committed is being taken back. A restarting node announcing its prefix wants
  `resync`.

  Cheap on a copy-on-write substrate: reverting is moving a branch pointer to an
  older commit, because the blocks are immutable and still in the store. btcd
  confirms the principle from the other side -- at the header layer its undo log
  is empty, since every consensus quantity is a fold over the ancestor path. All
  of Bitcoin's two-phase reorg machinery exists only because its UTXO set is a
  destructively mutated map.

  `dropped` is REQUIRED, and naming it is what makes the effect safe. Without it
  an interpreter holds only a flat sequence of committed vertices with no parent
  links, so it has to SEARCH for `to-vertex` and truncate -- and then a
  `to-vertex` that was never committed is indistinguishable from a mistyped one.
  Both would mean \"discard everything\", so a typo would silently wipe committed
  history. Nakamoto surfaced this: every reorg back to the root reverts to the
  genesis vertex, which is exactly the never-committed case.

  The algorithm already has the detached path -- it had to walk it to find the
  fork point -- so this costs nothing to supply and lets an interpreter verify
  rather than guess. An interpreter SHOULD reject a revert whose `dropped` does
  not match the tail it currently holds."
  [to-vertex dropped]
  [:revert {:to-vertex to-vertex :dropped (vec dropped)}])

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

(defn- validator-count
  "The validator-set size, insisting the key is actually there.

  Guarding this is not pedantry. `(count nil)` is 0, and every threshold
  function maps 0 to 1, so a state that merely FORGOT `:validators` would report
  that a single statement constitutes a quorum -- a silent safety failure that
  looks like normal operation. Failing loudly is the only safe behaviour."
  [state]
  (let [vs (:validators state)]
    (when (or (nil? vs) (zero? (count vs)))
      (throw (ex-info "membership needs a non-empty :validators in state"
                      {:state-keys (keys state)})))
    (count vs)))

(defn- total-weight
  "The universe the threshold is measured against.

  The head count when weights are uniform, the summed weight when they are not
  -- and the two must be the SAME quantity as the one being compared against
  it. Getting this wrong is a silent safety hole rather than an off-by-one:
  the original implementation summed per-validator STAKE on one side and
  applied `threshold-fn` to the HEAD COUNT on the other, so with four
  validators of power ten each, a single statement cleared
  `byzantine-threshold(4) = 3` and was reported as a Byzantine quorum. The
  correct threshold there is `byzantine-threshold(40) = 27`.

  It survived review because it is stated correctly in the docstring, tested by
  an assertion that encodes the bug as the expectation, and invisible while
  every algorithm using it happens to run uniform weights. Bullshark is the
  first algorithm whose thresholds are genuinely over stake, and it does not
  use `Membership` at all -- which is how this came out."
  [state validators]
  (let [powers (:voting-power state)]
    (if (seq powers)
      (reduce + 0 (map #(get powers % 0) validators))
      (count validators))))

(defn- distinct-voters
  "The DISTINCT senders among statements satisfying `pred`.

  Counting statements rather than senders is a safety hole, not a detail: three
  copies of one validator's vote would clear a quorum of four, so a single
  Byzantine validator could decide a height by repeating itself. Duplicate
  suppression cannot be left to callers, because every caller would have to
  remember, and the failure is silent.

  `voter-fn` extracts the sender; statements that do not identify one are
  rejected rather than counted, since an anonymous statement cannot be
  attributed and therefore cannot count toward a threshold."
  [voter-fn statements pred]
  (into #{}
        (comp (filter pred)
              (map voter-fn)
              (remove nil?))
        statements))

(defrecord ThresholdMembership [threshold-fn voter-fn]
  Membership
  (quorum? [this state statements pred]
    (validator-count state)
    (let [total (total-weight state (:validators state))
          voters (distinct-voters voter-fn statements pred)
          w (reduce + 0 (map #(weight this state %) voters))]
      (>= w (threshold-fn total))))
  (v-blocking? [this state statements pred]
    ;; A set blocks if its complement can no longer reach the threshold.
    (validator-count state)
    (let [total (total-weight state (:validators state))
          voters (distinct-voters voter-fn statements pred)
          w (reduce + 0 (map #(weight this state %) voters))]
      (> w (- total (threshold-fn total)))))
  (weight [_ state peer-id]
    ;; MUST mirror `total-weight`'s default, and did not.
    ;;
    ;; `total-weight` defaults a validator missing from `:voting-power` to 0;
    ;; this defaulted it to 1. So with a partial power map, an unlisted
    ;; validator contributed nothing to the denominator and a full unit to the
    ;; numerator -- the quorum bar dropped while the votes counted, in the
    ;; direction that reaches a quorum too easily. That is a safety hole, not
    ;; an off-by-one, and it is the same shape as the bug `total-weight`'s own
    ;; docstring was written about: two quantities that must be measured the
    ;; same way, measured differently.
    ;;
    ;; The conditional matters. With NO power map both sides use head count, so
    ;; the default has to be 1 there and 0 here; a single constant is wrong in
    ;; one regime or the other.
    (let [powers (:voting-power state)]
      (if (seq powers) (get powers peer-id 0) 1))))

(defn byzantine-threshold
  "floor(2n/3) + 1 -- the Byzantine quorum.

  Its defining property is quorum intersection: any two quorums share strictly
  more than f members, hence at least one honest one. Machine-checked over Nat
  in `proofs/urd/proofs/quorum_intersection.clj`; run it with `clj -M:proofs`,
  which also checks that this function and the verified one agree."
  [n]
  (inc (quot (* 2 n) 3)))

(defn majority-threshold
  "floor(n/2) + 1 -- the crash-fault quorum.

  Weaker than `byzantine-threshold` for every n >= 5; they coincide only at
  n in #{1,2,4}."
  [n]
  (inc (quot n 2)))

(defn validator-set
  "The validator set from a config, checked.

  Sorted for determinism -- every algorithm here already did that -- and
  REFUSED when it is empty or contains a duplicate. Both were accepted before,
  and both are quietly fatal:

  - **Empty.** Round-robin picks its proposer with `(mod height (count vs))`
    and divides by zero on the very first timer tick, killing the event loop
    before the node has done anything. The symptom is a validator that starts
    cleanly and is simply never heard from.

  - **Duplicated.** Quorum arithmetic counts POSITIONS, not identities. Raft's
    `vote-result` takes `[:a :a :b]`, computes `q = 2`, and then counts one
    grant from `:a` twice -- so `:a` elects itself leader alone, against a
    quorum rule that says it needs two of three. Every threshold in this
    library is `(count validators)` somewhere, so a duplicate under-counts the
    quorum everywhere at once.

  Neither is a state a deployment can be in on purpose, and both come from a
  config file. Refusing at `init` puts the error where the operator can read
  it, rather than several layers down as an ArithmeticException or as a
  cluster that agrees with itself too easily."
  [config]
  (let [vs (:validators config)]
    (when (empty? vs)
      (throw (ex-info "config needs a non-empty :validators"
                      {:peer-id (:peer-id config)})))
    (let [dups (->> vs frequencies (keep (fn [[v n]] (when (> n 1) v))) vec)]
      (when (seq dups)
        (throw (ex-info (str "duplicate validator ids: " (pr-str dups)
                             " -- quorum arithmetic counts positions, so a"
                             " duplicate lets one node vote more than once")
                        {:peer-id (:peer-id config) :duplicates dups}))))
    (vec (sort vs))))

(defn byzantine-tolerance
  "f = floor((n-1)/3), the number of Byzantine faults n validators tolerate.

  Note f=0 for n<4: three validators tolerate NO Byzantine faults, so a
  3-node cluster is a crash-fault configuration only."
  [n]
  (quot (max 0 (dec n)) 3))

(defn threshold-membership
  "Membership by a numeric threshold over DISTINCT senders.

  `voter-fn` extracts the sender from a statement; defaults to `:from`. Per
  validator voting power may be supplied as `:voting-power` in the state, in
  which case BOTH sides of the comparison move to weight: the threshold is
  computed from the total power of the validator set, not from its size. See
  `total-weight` for why that is spelled out rather than assumed."
  ([threshold-fn] (threshold-membership threshold-fn :from))
  ([threshold-fn voter-fn] (->ThresholdMembership threshold-fn voter-fn)))

(def bft-membership (threshold-membership byzantine-threshold))
(def cft-membership (threshold-membership majority-threshold))

;; ============================================================
;; Effect classification (used by runtimes and the simulator)
;; ============================================================

(def ^:private outbound-effects #{:send :broadcast})

(def all-effects
  "Every effect kind the protocol defines. A declaration is checked against this,
  so a typo in a capability set is refused rather than silently narrowing what a
  node is allowed to do."
  #{:send :broadcast :deliver-self :persist-then :sample :set-timer :cancel-timer
    :request-value :commit :revert :resync :report-equivocation :log})

(defn check-topics
  "Validate and return the set of topics this node broadcasts on.

  A node that emits `:broadcast` MUST declare them. The runtime subscribes to
  exactly what is declared, and it cannot guess: the topic vocabularies are
  per-algorithm and disjoint -- round-robin uses
  `#{:proposals :votes :finalizations :recovery}`, Tendermint `#{:consensus}`,
  SCP `#{:scp}`, Bullshark `#{:bullshark}`, Nakamoto `#{:headers}`, and Raft
  and Snowman do not broadcast at all.

  This exists because the runtime's subscription list was round-robin's
  vocabulary, hardcoded. Every other algorithm's broadcasts went to a topic
  nothing was subscribed to, so they were accepted, sent, and silently dropped.
  Tendermint on the real runtime started cleanly, reported no error, and sat at
  height 0 forever -- four nodes each waiting for votes that had been
  delivered to nobody. A declaration the interpreter reads is the difference
  between that and a startup failure."
  [node]
  (let [caps (capabilities node)
        topics (:topics caps)
        emits (:emits caps)]
    (when (and (contains? (or emits #{}) :broadcast)
               (not (and (set? topics) (seq topics))))
      (throw (ex-info "a Node that emits :broadcast must declare {:topics #{...}}"
                      {:node (type node) :capabilities caps})))
    (or topics #{})))

(defn check-capabilities
  "Validate a declaration and return its `:emits` set. Throws if it is missing,
  malformed, or names an effect the protocol does not define."
  [node]
  (let [caps (capabilities node)
        emits (:emits caps)]
    (when-not (set? emits)
      (throw (ex-info "a Node must declare {:emits #{...}}"
                      {:node (type node) :capabilities caps})))
    (when-let [unknown (seq (remove all-effects emits))]
      (throw (ex-info "capability declaration names effects that do not exist"
                      {:node (type node) :unknown (vec unknown)
                       :known all-effects})))
    emits))

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
