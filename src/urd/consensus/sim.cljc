(ns urd.consensus.sim
  "A deterministic discrete-event simulator for consensus algorithms.

  This is the primary way algorithms are tested. Everything that could vary
  between runs -- time, randomness, message delay, message loss, crash points --
  is drawn from an explicit seed and threaded through pure functions, so a
  failing run is fully reproducible from `(seed, config)` and can be replayed,
  forked, or stepped one tick at a time.

  The simulator is itself a value. `advance` takes a sim and returns a sim; no
  atoms, no threads, no wall clock. That is what makes shrinking work: a
  test.check failure hands you a seed, and the seed hands you the exact history.

  ## Time is logical

  A tick is the unit. Timers are armed for a number of ticks, message delays are
  a number of ticks. Nothing consults a real clock, so a timeout-dependent bug
  reproduces identically on a fast machine, a slow machine, and in a browser.

  ## Determinism rules

  Map iteration order is not guaranteed to be stable across platforms, so
  anywhere order could affect the result -- delivering to peers, breaking ties --
  we sort explicitly. Where a collection is drawn from, we sort before sampling.
  Violating this would make a run irreproducible in exactly the cases that
  matter most."
  (:require [urd.consensus.node :as node]
            [urd.consensus.rng :as rng]
            ;; For `merge-durable` only, so both interpreters fold landed
            ;; writes into the restored view by one rule rather than two.
            [urd.consensus.store :as store]))

;; Mutually recursive: interpreting an effect can step a node, and stepping a
;; node produces effects to interpret.
(declare interpret-effects interpret-effect deliver-local step-node)

;; ============================================================
;; Construction
;; ============================================================

(def default-config
  {:min-delay 1        ; ticks
   :max-delay 3
   :drop-rate 0.0      ; probability a message is lost
   :duplicate-rate 0.0 ; probability a message is delivered twice
   :persist-latency 1  ; ticks for a durable write to land
   :max-inflight 10000})

(defn make
  "Build a simulator.

  `nodes` is {peer-id node-impl}. Each node's `init` runs immediately and its
  effects are interpreted, so a node can persist hard state or arm a timer
  before the first tick."
  [{:keys [seed nodes node-config config]
    :or {seed 1 config {}}}]
  (let [cfg (merge default-config config)
        peer-ids (vec (sort (keys nodes)))
        base {:tick 0
              :rng (rng/make seed)
              :seed seed
              :peer-ids peer-ids
              ;; Kept so `restart` can rebuild a node with the same
              ;; configuration it was created with. Without this a restarted
              ;; node silently loses its per-node config, which is exactly the
              ;; kind of difference that makes a durability test lie.
              :node-config (or node-config {})
              :nodes {}
              :timers {}
              :inflight []
              :self-inbox []
              :next-msg-id 0
              :partitions nil
              :crashed #{}
              ;; Messages addressed to a peer the simulator does not have.
              ;; Counted rather than dropped silently: an algorithm addressing
              ;; a validator that is not reachable is a real condition once
              ;; sets can change, and a test asserting progress wants to know
              ;; whether it is happening.
              :undeliverable {}
              :storage {}
              :pending-persist {}
              :committed {}
              :reverted {}
              :equivocations []
              :bytes-sent {}
              :tick-bytes {}
              :peak-tick-bytes {}
              :trace []
              :config cfg}]
    (reduce (fn [sim peer-id]
              (let [impl (get nodes peer-id)
                    ;; Validated at REGISTRATION, so a node that will not say
                    ;; what it emits cannot be run at all. `check-capabilities`
                    ;; also rejects a declaration naming an effect the protocol
                    ;; does not define, which is what stops a typo from silently
                    ;; narrowing what a node is allowed to do.
                    emits (node/check-capabilities impl)
                    cfg' (merge {:peer-id peer-id :validators peer-ids}
                                (get node-config peer-id))
                    {:keys [state effects]} (node/init impl cfg')]
                (-> sim
                    (assoc-in [:nodes peer-id] {:impl impl :state state :emits emits})
                    (assoc-in [:storage peer-id] {:durable {} :writes [] :landed []})
                    (assoc-in [:committed peer-id] [])
                    (#(interpret-effects % peer-id (or effects []))))))
            base
            peer-ids)))

;; ============================================================
;; Network reachability
;; ============================================================

(defn- same-partition?
  "Can `from` reach `to` right now?"
  [sim from to]
  (let [parts (:partitions sim)]
    (or (nil? parts)
        (boolean (some #(and (contains? % from) (contains? % to)) parts)))))

(defn- live? [sim peer-id]
  (not (contains? (:crashed sim) peer-id)))

;; ============================================================
;; Effect interpretation
;; ============================================================

(def ^:private size-overhead
  "Bytes charged for a collection itself, on top of its contents."
  2)

(defn estimate-size
  "A portable, deterministic size estimate for a message, in notional bytes.

  Structural rather than `(count (pr-str x))`, and that is deliberate: printing
  is not guaranteed to agree between Clojure and ClojureScript for doubles or
  for records, and a simulator whose accounting differs between platforms is
  worse than one with no accounting. The absolute numbers mean nothing; what
  has to be true is that a bigger message costs more and that both platforms
  agree by how much.

  Depth-bounded, because a message is attacker-supplied data in several of
  these algorithms and a cyclic or absurdly nested one must not hang the
  simulator."
  ([x] (estimate-size x 0))
  ([x depth]
   (cond
     (> depth 32) 8
     (nil? x) 1
     (boolean? x) 1
     (number? x) 8
     (keyword? x) (+ size-overhead (count (name x))
                     (if-let [ns' (namespace x)] (count ns') 0))
     (string? x) (+ size-overhead (count x))
     (map? x) (reduce (fn [acc [k v]]
                        (+ acc (estimate-size k (inc depth))
                           (estimate-size v (inc depth))))
                      size-overhead x)
     (coll? x) (reduce (fn [acc v] (+ acc (estimate-size v (inc depth))))
                       size-overhead x)
     :else 16)))

(defn- charge-bandwidth
  "Account for `bytes` leaving `from` this tick.

  The simulator modelled message COUNT and ORDERING and neither SIZE nor
  BANDWIDTH, which made a whole class of defect free here and ruinous on a real
  transport. The state-sync storm is the case that proved it: a correct
  per-message fix -- a node one height behind now asks for a sync -- turned into
  every lagging node asking every peer, each answer carrying the responder's
  entire `:finalized` map. Five nodes over kabel went from ten heights
  finalized each to one, and the simulator reported nothing at all, because the
  message count had barely moved. A fix can be correct per message and wrong
  per second, and until now nothing here could express the difference."
  [sim from bytes]
  (-> sim
      (update-in [:bytes-sent from] (fnil + 0) bytes)
      (update-in [:tick-bytes from] (fnil + 0) bytes)))

(defn- over-budget?
  "Would this message exceed `from`'s per-tick byte budget?

  nil budget means unlimited, which is the default: existing tests describe
  schedules, not link capacities, and silently starting to drop their messages
  would change what they mean."
  [sim from bytes]
  (when-let [budget (get-in sim [:config :bandwidth-per-tick])]
    (> (+ (get-in sim [:tick-bytes from] 0) bytes) budget)))

(defn- enqueue
  "Schedule a message, applying delay / drop / duplication from the config."
  [sim from to msg]
  (let [{:keys [min-delay max-delay drop-rate duplicate-rate max-inflight]} (:config sim)
        bytes (estimate-size msg)]
    (cond
      ;; Partitioned or crashed: silently lost, which is what a real network
      ;; does. The trace records it so a test can assert on loss.
      (not (and (live? sim to) (same-partition? sim from to)))
      (update sim :trace conj {:tick (:tick sim) :event :dropped-unreachable
                               :from from :to to})

      (>= (count (:inflight sim)) max-inflight)
      (update sim :trace conj {:tick (:tick sim) :event :dropped-overflow
                               :from from :to to})

      ;; The link is full for this tick. Charged even though it is dropped:
      ;; the sender did try to put it on the wire, and a model in which
      ;; over-budget traffic is free would hide exactly the storms this exists
      ;; to expose.
      (over-budget? sim from bytes)
      (-> sim
          (charge-bandwidth from bytes)
          (update :trace conj {:tick (:tick sim) :event :dropped-bandwidth
                               :from from :to to :bytes bytes}))

      :else
      (let [sim (charge-bandwidth sim from bytes)
            [roll rng'] (rng/next-double (:rng sim))
            sim (assoc sim :rng rng')]
        (if (< roll drop-rate)
          (update sim :trace conj {:tick (:tick sim) :event :dropped-randomly
                                   :from from :to to})
          (let [[delay rng'] (rng/next-int (:rng sim)
                                           (inc (- max-delay min-delay)))
                sim (assoc sim :rng rng')
                at (+ (:tick sim) min-delay delay)
                id (:next-msg-id sim)
                entry {:id id :at at :from from :to to :msg msg}
                sim (-> sim
                        (update :inflight conj entry)
                        (update :next-msg-id inc))
                [dup-roll rng'] (rng/next-double (:rng sim))
                sim (assoc sim :rng rng')]
            (if (< dup-roll duplicate-rate)
              (-> sim
                  (update :inflight conj (assoc entry :id (:next-msg-id sim)
                                                :at (inc at) :duplicate? true))
                  (update :next-msg-id inc))
              sim)))))))

(defn- interpret-effect
  [sim peer-id effect]
  (let [kind (node/effect-kind effect)
        params (node/effect-params effect)]
    ;; An undeclared effect is refused. Without this the declaration would be a
    ;; comment: it is only a claim about the algorithm if something checks it on
    ;; every run. The `:then` of a `persist-then` is interpreted through this
    ;; same path, so gated effects are covered too.
    (when-let [emits (get-in sim [:nodes peer-id :emits])]
      (when-not (contains? emits kind)
        (throw (ex-info "node emitted an effect it did not declare"
                        {:peer peer-id :effect kind :declared emits}))))
    (case kind
      :send
      (enqueue sim peer-id (:to params) (:msg params))

      :broadcast
      ;; Sorted so delivery order is reproducible.
      (reduce (fn [s to] (if (= to peer-id) s (enqueue s peer-id to (:msg params))))
              sim
              (:peer-ids sim))

      :deliver-self
      ;; Delivered at the next tick, never dropped, never partitioned. Queued
      ;; rather than applied inline so a node cannot recurse into itself within
      ;; a single step.
      (update sim :self-inbox (fnil conj []) {:at (inc (:tick sim))
                                              :peer peer-id
                                              :input (:input params)})

      :persist-then
      (let [{:keys [writes durable? epoch then truncate-from checkpoint]} params
            ;; Caller-supplied token when present; the interpreter only invents
            ;; one as a fallback, because a node that cannot name its own write
            ;; cannot correlate the completion with it.
            token (or (:token params) (:next-msg-id sim))
            at (+ (:tick sim) (if durable? (get-in sim [:config :persist-latency]) 0))
            record (cond-> {:tick (:tick sim) :writes writes :durable? durable?
                            :truncate-from truncate-from}
                     checkpoint (assoc :checkpoint (vec checkpoint)))]
        (-> sim
            (update :next-msg-id inc)
            ;; `:writes` records every write that was ISSUED, whether or not it
            ;; landed. `:durable` (below, in complete-due-persists) records only
            ;; those that landed, and is the only thing a restart may see.
            (update-in [:storage peer-id :writes] conj record)
            (update-in [:pending-persist peer-id] (fnil conj [])
                       {:token token :epoch epoch :then then :at at
                        :record record})))

      :sample
      (let [{:keys [request-id k from]} params
            candidates (if (= from :validators)
                         (:peer-ids sim)
                         (vec (sort (remove #{peer-id} (:peer-ids sim)))))
            [bag rng'] (rng/sample-weighted-bag (:rng sim) candidates (constantly 1) k)]
        (-> sim
            (assoc :rng rng')
            (deliver-local peer-id (node/sampled request-id bag))))

      :set-timer
      (assoc-in sim [:timers peer-id (:timer-id params)]
                (+ (:tick sim) (:after-ticks params)))

      :cancel-timer
      (update-in sim [:timers peer-id] dissoc (:timer-id params))

      :commit
      (update-in sim [:committed peer-id] into (:vertices params))

      :resync
      ;; Wholesale replacement, and NOT routed through the revert path: there is
      ;; no tail to check `:dropped` against, because the node is telling us what
      ;; it holds rather than what it takes back. Overloading `:revert` for this
      ;; is exactly what forced the `:dropped` check to be skippable.
      (-> sim
          (assoc-in [:committed peer-id] (vec (:vertices params)))
          (update :trace conj {:tick (:tick sim) :event :resync
                               :peer peer-id :n (count (:vertices params))}))

      :revert
      ;; The committed prefix is TRUNCATED to end at `to-vertex`, not merely
      ;; noted. Until Nakamoto landed, no algorithm emitted a `:revert` at all,
      ;; and this branch only recorded one -- which meant `agreement?` could not
      ;; possibly have detected a reorg-induced divergence, because the two
      ;; nodes' committed vectors kept the abandoned branch and stayed unequal
      ;; forever regardless of whether they had actually converged.
      ;;
      ;; The effect now NAMES what it drops, so the interpreter can verify
      ;; rather than guess. Searching for `to-vertex` and truncating -- the only
      ;; option when the effect carried just a target -- could not tell a
      ;; never-committed target (genesis, where every reorg-to-root lands) from
      ;; a mistyped one, and both meant "discard everything", so a typo silently
      ;; wiped committed history.
      ;;
      ;; `:dropped` must match the tail we hold, EXACTLY, including when it is
      ;; empty. It used to be that an empty one meant "truncate to `to-vertex`,
      ;; whatever is there" -- the escape hatch a restarting node needed, because
      ;; it cannot know what we still hold. That is now `:resync`, so the escape
      ;; hatch is gone and the check is unconditional. Splitting the two effects
      ;; is what let this guard become total.
      (let [to (:to-vertex params)
            claimed (vec (:dropped params))
            committed (vec (get-in sim [:committed peer-id] []))
            at (last (keep-indexed (fn [i v] (when (= v to) i)) committed))
            keep-n (if at (inc at) 0)
            dropped (subvec committed keep-n)
            mismatch? (not= claimed dropped)]
        ;; THROW, do not merely note. `node/revert` says an interpreter should
        ;; reject a revert whose `dropped` does not match the tail it holds, and
        ;; recording the disagreement in `:trace` and then truncating anyway is
        ;; not rejecting it -- it is a green run with a broken invariant in the
        ;; log. Nakamoto is the only algorithm that reverts routinely and it was
        ;; the one algorithm whose tests never looked at `:trace`, so the field
        ;; the whole revocable-commit design exists to carry could be reversed,
        ;; truncated, or emptied with the suite still green.
        (when mismatch?
          (throw (ex-info "revert :dropped does not match the committed tail"
                          {:peer peer-id :to to :claimed claimed :actual dropped})))
        (-> sim
            (assoc-in [:committed peer-id] (subvec committed 0 keep-n))
            (update-in [:reverted peer-id] (fnil conj []) (:to-vertex params))
            (update :trace conj {:tick (:tick sim) :event :revert
                                 :peer peer-id :to (:to-vertex params)
                                 :dropped dropped})))

      :report-equivocation
      (update sim :equivocations conj
              (assoc params :reporter peer-id :tick (:tick sim)))

      :request-value
      (let [value-fn (get-in sim [:config :value-fn])
            v (if value-fn (value-fn sim peer-id (:context params)) {:payload :none})]
        (deliver-local sim peer-id (node/value-ready v)))

      :log
      (update sim :trace conj (assoc params :tick (:tick sim) :peer peer-id))

      ;; Unknown effects are recorded rather than silently dropped -- a typo in
      ;; an algorithm should be visible in the trace, not invisible.
      (update sim :trace conj {:tick (:tick sim) :event :unknown-effect
                               :peer peer-id :effect effect}))))

(defn interpret-effects [sim peer-id effects]
  (reduce #(interpret-effect %1 peer-id %2) sim effects))

;; ============================================================
;; Stepping a node
;; ============================================================

(defn- step-node
  "Feed one input to a node and interpret whatever it returns.

  A peer we have never heard of is UNDELIVERABLE, not an error. That case
  became reachable when validator sets became changeable: an algorithm may
  address a validator the transport cannot reach -- a node voted into the set
  before it has connected, or one whose address nobody has yet. In production
  that is a dropped packet. Here it used to be

      No implementation of method: :step of protocol: Node found for class: nil

  from `node/step` on a nil impl, several frames from the cause, which reads as
  a protocol bug rather than as a message to a peer that does not exist.

  This is the reachability-versus-authority split showing up in the simulator:
  `:peer-ids` is who can be reached, the validator set is who counts, and once
  the two can differ an algorithm can legitimately name a peer in one and not
  the other."
  [sim peer-id input]
  (if-not (and (live? sim peer-id) (get-in sim [:nodes peer-id :impl]))
    (cond-> sim
      (not (get-in sim [:nodes peer-id :impl]))
      (update-in [:undeliverable peer-id] (fnil inc 0)))
    (let [{:keys [impl state]} (get-in sim [:nodes peer-id])
          {new-state :state effects :effects} (node/step impl state input)]
      (-> sim
          (assoc-in [:nodes peer-id :state] new-state)
          (interpret-effects peer-id (or effects []))))))

(defn- deliver-local
  "Deliver an input to a node immediately, within the current tick.

  Used for effect responses (`sampled`, `value-ready`) that do not travel over
  the network."
  [sim peer-id input]
  (step-node sim peer-id input))

;; ============================================================
;; The main loop
;; ============================================================

(defn- deliver-due-messages [sim]
  (let [t (:tick sim)
        due (->> (:inflight sim)
                 (filter #(<= (:at %) t))
                 ;; Sort for reproducibility: arrival tick, then id.
                 (sort-by (juxt :at :id))
                 vec)
        remaining (vec (remove #(<= (:at %) t) (:inflight sim)))]
    (reduce (fn [s {:keys [from to msg]}]
              (if (and (live? s to) (same-partition? s from to))
                (step-node s to (node/message-received from msg #{from}))
                s))
            (assoc sim :inflight remaining)
            due)))

(defn- fire-due-timers
  "Fire every armed timer whose deadline has passed, in a reproducible order.

  Sorted by the PRINTED timer id rather than by the id itself. Sorting by the
  id directly silently constrains what a timer id may be: `compare` throws on
  two values of different types, so a node that armed `:gossip` and
  `[:anchor 3]` crashed the simulator from inside its own scheduling loop, with
  a ClassCastException naming neither the node nor the timer. Nothing in the
  effect API said timer ids had to be mutually comparable, and an algorithm
  that wants one timer per round -- Bullshark wants exactly that -- reaches for
  a compound id immediately. Printing first is a total order over any ids at
  all, and coincides with the old one for the keyword ids every algorithm here
  uses."
  [sim]
  (let [t (:tick sim)
        due (for [peer-id (:peer-ids sim)
                  [timer-id fire-at] (sort-by (comp pr-str key)
                                              (get-in sim [:timers peer-id] {}))
                  :when (<= fire-at t)]
              [peer-id timer-id])]
    (reduce (fn [s [peer-id timer-id]]
              (-> s
                  (update-in [:timers peer-id] dissoc timer-id)
                  (step-node peer-id (node/timer-fired timer-id))))
            sim
            due)))

(defn- complete-due-persists [sim]
  (let [t (:tick sim)]
    (reduce
     (fn [s peer-id]
       ;; A crashed node does not finish its writes. `crash` already discards
       ;; them, so this is belt and braces -- but it is the cheap half of a
       ;; guard whose absence let a dead node put a message on the wire.
       (let [pending (if (live? s peer-id) (get-in s [:pending-persist peer-id] []) [])
             due (filter #(<= (:at %) t) pending)
             remaining (vec (remove #(<= (:at %) t) pending))]
         (reduce (fn [s2 {:keys [token epoch then record]}]
                   (-> s2
                       ;; The write is now on disk and survives a crash. This is
                       ;; the ONLY place durable state grows; a write that was
                       ;; issued but never completed is genuinely lost, which is
                       ;; what makes a crash-before-fsync test mean anything.
                       ;; A checkpoint REPLACES what a restart may see. This
                       ;; is the whole reason the flag exists, and modelling it
                       ;; as anything else would make the simulator's crash
                       ;; tests pass over a log the real store no longer has.
                       (update-in [:storage peer-id :landed]
                                  (fn [ls]
                                    (if-let [cp (:checkpoint record)]
                                      (vec cp)
                                      (conj (or ls []) record))))
                       ;; A checkpoint REPLACES this too, and merging was
                       ;; wrong in a way that hid bugs rather than causing
                       ;; them. `:durable` models the last-write-wins view a
                       ;; restart reconstructs by folding the log; after
                       ;; `checkpoint!` the old log is GONE, so that fold sees
                       ;; only the checkpoint's own records. Merging kept every
                       ;; key any earlier write had ever set, so a checkpoint
                       ;; that forgot to carry something still restored it from
                       ;; a record the real store had deleted. Measured: two
                       ;; mutations that drop load-bearing keys from
                       ;; Tendermint's checkpoint passed the whole suite.
                       (update-in [:storage peer-id :durable]
                                  (fn [d]
                                    (if-let [cp (:checkpoint record)]
                                      (reduce merge {} (map :writes cp))
                                      (merge d (:writes record)))))
                       ;; The node learns the write landed...
                       (step-node peer-id (node/persisted token epoch))
                       ;; ...and only THEN do the gated effects go out. This is
                       ;; the whole point of the barrier.
                       (interpret-effects peer-id (or then []))))
                 (assoc-in s [:pending-persist peer-id] remaining)
                 due)))
     sim
     (:peer-ids sim))))

(defn- deliver-self-inbox
  "Deliver inputs a node addressed to itself.

  Runs BEFORE network delivery: a node's own conclusions about what it has
  already done should be visible to it before it processes anything new. Sorted
  for reproducibility."
  [sim]
  (let [t (:tick sim)
        inbox (:self-inbox sim)
        due (->> inbox (filter #(<= (:at %) t)) (sort-by (juxt :at :peer)) vec)
        remaining (vec (remove #(<= (:at %) t) inbox))]
    (reduce (fn [s {:keys [peer input]}] (step-node s peer input))
            (assoc sim :self-inbox remaining)
            due)))

(defn- roll-bandwidth
  "Fold this tick's byte counters into the per-peer peak, then reset them.

  The PEAK is what matters rather than the total: a storm is a spike, and a run
  long enough to average it away is a run that will not show it."
  [sim]
  (-> (reduce (fn [s [peer bytes]]
                (update-in s [:peak-tick-bytes peer] (fnil max 0) bytes))
              sim
              (:tick-bytes sim))
      (assoc :tick-bytes {})))

(defn advance
  "Advance the simulation by one tick."
  [sim]
  (-> sim
      roll-bandwidth
      (update :tick inc)
      deliver-self-inbox
      deliver-due-messages
      fire-due-timers
      complete-due-persists))

(defn run
  "Advance until `pred` holds or `max-ticks` elapse.

  Returns the sim. Check `(:tick sim)` against max-ticks to tell convergence
  from exhaustion."
  ([sim max-ticks] (run sim max-ticks (constantly false)))
  ([sim max-ticks pred]
   (loop [s sim, n 0]
     (if (or (>= n max-ticks) (pred s))
       s
       (recur (advance s) (inc n))))))

;; ============================================================
;; Fault injection
;; ============================================================

(defn partition-network
  "Split the network. `parts` is a collection of peer-id sets; messages only
  flow within a part."
  [sim parts]
  (assoc sim :partitions (mapv set parts)))

(defn heal [sim] (assoc sim :partitions nil))

(defn crash
  "Crash a node: it stops stepping, its in-memory state is lost, and any write
  that had not reached the platter is lost with it.

  ## Buffered writes did NOT used to be lost, and that blinded every crash test

  `complete-due-persists` lands every completed write in `:landed` --
  `durable? true` and `durable? false` alike -- under a comment asserting the
  write is now on disk and survives a crash. `restart` then replayed all of it.
  So a non-fsynced write ALWAYS survived a simulated crash, and no crash test in
  this repo could tell buffered state from durable state.

  That is the entire distinction `persist-then`'s `durable?` flag exists to
  draw, and the simulator was structurally blind to it: an algorithm could
  release a binding commitment against a write that never reached disk, and the
  whole suite would still pass. Three Raft findings live in exactly that gap --
  a follower acking `MsgAppResp` off an entry-less buffered write, a leader
  consuming its own vote and its own append the same way -- and none of them
  could be reproduced here, not because they were absent but because the oracle
  could not represent them.

  ## The model

  POSIX-shaped and no more: an fsync flushes everything written before it. So a
  buffered write that PRECEDES a durable one survives on its coat-tails, and
  only the buffered tail after the last fsync is lost. That distinction is not
  a detail to round off -- etcd-raft's `MustSync` is built on it, deliberately
  leaving a commit-index change unsynced because a later sync will carry it.

  `:writes` keeps every write ever ISSUED and is untouched, so a test can still
  see what was attempted; `:landed` is narrowed to what a restart may see."
  [sim peer-id]
  (let [landed (vec (get-in sim [:storage peer-id :landed] []))
        keep-n (loop [i (dec (count landed))]
                 (cond (neg? i) 0
                       (:durable? (nth landed i)) (inc i)
                       :else (recur (dec i))))
        survivors (subvec landed 0 keep-n)]
    (-> sim
        (assoc-in [:storage peer-id :landed] survivors)
        ;; A write still in flight never landed, and must not land afterwards.
        ;;
        ;; `restart` already discarded these, with exactly the right reasoning
        ;; -- and between the crash and the restart they completed anyway,
        ;; because `complete-due-persists` iterated every peer without asking
        ;; whether it was alive. So a crashed node went on writing to disk and,
        ;; worse, went on releasing the `:then` effects gated behind those
        ;; writes: it broadcast after it was dead.
        ;;
        ;; That defeats the whole point of the barrier under crash. The
        ;; question `persist-then` exists to answer is whether a node released
        ;; its binding commitment before the write was durable, and the answer
        ;; was being supplied by the corpse. It is also the path the durability
        ;; tests take -- `raft_test.clj` asserts a write is in flight and THEN
        ;; crashes the node.
        (assoc-in [:pending-persist peer-id] [])
        ;; Recomputed from the survivors rather than left as it was: `:durable`
        ;; is a fold over the landed log, and a fold that keeps summarising
        ;; records the crash destroyed is how a restart sees state it never had.
        (assoc-in [:storage peer-id :durable] (store/merge-durable survivors))
        (update :crashed conj peer-id)
        (update :trace conj {:tick (:tick sim) :event :crash :peer peer-id
                             :lost-buffered (- (count landed) keep-n)}))))

(defn add-peer
  "Add a peer that did not exist when the simulator was built.

  ## Why this is separate from the validator set

  `:peer-ids` is who is REACHABLE -- who can be sent a message and who gets a
  tick. It is NOT who counts toward a quorum: that is each node's own
  `:validators`, which an algorithm may now change through a decided value (see
  `urd.consensus.reconfig`). Before set changes existed the two were always
  equal, and `make` still derives one from the other for convenience, which
  made them easy to conflate.

  Keeping them apart is what lets a set change be simulated honestly:

    - A joining validator must be REACHABLE BEFORE it counts. The cluster has
      to be able to replicate to it while it is still not a voter, or it can
      never catch up enough to become one.
    - A removed validator stays REACHABLE AFTER it stops counting. It keeps
      receiving messages and must not be able to influence a quorum.

  Neither is expressible while the two are one list. It is the same distinction
  as discovery-versus-membership in a peer-to-peer transport: reachability is
  not authority.

  `config` is merged into the node's `init` config and stored as its
  `:node-config`, so a later `restart` rebuilds it the same way. A joiner is
  normally given `:validators` reflecting the set it is joining, and whatever
  state-sync register the algorithm uses to start above genesis."
  [sim peer-id impl config]
  (when (contains? (set (:peer-ids sim)) peer-id)
    (throw (ex-info "peer already exists" {:peer-id peer-id})))
  (let [cfg (merge {:peer-id peer-id :validators (:peer-ids sim)} config)
        emits (node/check-capabilities impl)
        {:keys [state effects]} (node/init impl cfg)]
    (-> sim
        ;; Sorted, because `:peer-ids` order is observable -- `sample` draws
        ;; from it and several algorithms sort their validator list. A joiner
        ;; appended at the end would give a different draw order than the same
        ;; cluster started with that peer from the beginning.
        (update :peer-ids (fn [ps] (vec (sort (conj ps peer-id)))))
        (assoc-in [:node-config peer-id] config)
        (assoc-in [:nodes peer-id] {:impl impl :state state :emits emits})
        (assoc-in [:storage peer-id] {:durable {} :writes [] :landed []})
        (assoc-in [:committed peer-id] [])
        (update :trace conj {:tick (:tick sim) :event :add-peer :peer peer-id})
        (interpret-effects peer-id (or effects [])))))

(defn restart
  "Restart a crashed node from its DURABLE state only.

  In-memory state is discarded and `init` runs again, so anything the algorithm
  failed to persist is genuinely lost -- which is the point. A node that keeps
  its term in memory but not on disk will fail here, exactly as it would in
  production.

  `:restored` carries two views of the same thing, because algorithms differ in
  what they need. `:durable` is the merge of every landed write, which suits an
  algorithm whose durable state is a small record. `:writes` is the ORDERED log
  of landed writes, which an algorithm with an append-only log must replay --
  merging cannot express `truncate-from`, and a later append at a lower index
  has to overwrite rather than union."
  [sim peer-id]
  (let [impl (get-in sim [:nodes peer-id :impl])
        storage (get-in sim [:storage peer-id] {})
        cfg (merge {:peer-id peer-id
                    :validators (:peer-ids sim)
                    :restored {:durable (:durable storage {})
                               :writes (:landed storage [])}}
                   (get-in sim [:node-config peer-id]))
        {:keys [state effects]} (node/init impl cfg)]
    (-> sim
        (update :crashed disj peer-id)
        (assoc-in [:nodes peer-id :state] state)
        (update :timers dissoc peer-id)
        ;; Writes that were in flight when the node died never landed, so they
        ;; must not land after it comes back.
        (assoc-in [:pending-persist peer-id] [])

        (update :trace conj {:tick (:tick sim) :event :restart :peer peer-id})
        (interpret-effects peer-id (or effects [])))))

;; ============================================================
;; External stimulus
;; ============================================================

(defn inject
  "Feed an input straight into a node, bypassing the network.

  This is the class of input that neither arrives over the network nor answers
  an effect: a client request, a newly mined block, an operator command. Needed
  by any algorithm that reacts to one, since `request-value` is node-INITIATED
  and offers no way to hand a proposal to a running node from outside."
  [sim peer-id input]
  (step-node sim peer-id input))

;; ============================================================
;; Inspection
;; ============================================================

(defn inject-all
  "Inject the same input into every live node."
  [sim input]
  (reduce #(inject %1 %2 input) sim (:peer-ids sim)))

(defn bytes-sent
  "Notional bytes each peer put on the wire over the whole run."
  [sim]
  (:bytes-sent sim {}))

(defn peak-tick-bytes
  "The most any peer sent in a SINGLE tick. A storm is a spike, so this is the
  measure that shows one; a total averages it away."
  [sim]
  (:peak-tick-bytes sim {}))

(defn bandwidth-drops
  "Messages the per-tick budget refused, if one was configured."
  [sim]
  (filterv #(= :dropped-bandwidth (:event %)) (:trace sim)))

(defn node-state [sim peer-id] (get-in sim [:nodes peer-id :state]))
(defn committed [sim peer-id] (get-in sim [:committed peer-id] []))
(defn all-committed [sim] (into {} (map (juxt identity #(committed sim %))) (:peer-ids sim)))
(defn quiet?
  "No messages in flight, no timers armed, nothing waiting on a write."
  [sim]
  (and (empty? (:inflight sim))
       (every? empty? (vals (:timers sim)))
       (every? empty? (vals (:pending-persist sim)))))

(defn agreement?
  "Do all live nodes agree on their committed prefix?

  The core safety property: no two nodes commit different values at the same
  position. Nodes may be at different lengths -- that is lag, not disagreement."
  [sim]
  (let [seqs (->> (:peer-ids sim)
                  (remove #(contains? (:crashed sim) %))
                  (map #(committed sim %)))]
    (every? (fn [[a b]]
              (let [n (min (count a) (count b))]
                (= (take n a) (take n b))))
            (for [a seqs b seqs] [a b]))))
