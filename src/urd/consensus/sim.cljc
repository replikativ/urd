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
            [urd.consensus.rng :as rng]))

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
              :storage {}
              :pending-persist {}
              :committed {}
              :reverted {}
              :equivocations []
              :trace []
              :config cfg}]
    (reduce (fn [sim peer-id]
              (let [impl (get nodes peer-id)
                    cfg' (merge {:peer-id peer-id :validators peer-ids}
                                (get node-config peer-id))
                    {:keys [state effects]} (node/init impl cfg')]
                (-> sim
                    (assoc-in [:nodes peer-id] {:impl impl :state state})
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

(defn- enqueue
  "Schedule a message, applying delay / drop / duplication from the config."
  [sim from to msg]
  (let [{:keys [min-delay max-delay drop-rate duplicate-rate max-inflight]} (:config sim)]
    (cond
      ;; Partitioned or crashed: silently lost, which is what a real network
      ;; does. The trace records it so a test can assert on loss.
      (not (and (live? sim to) (same-partition? sim from to)))
      (update sim :trace conj {:tick (:tick sim) :event :dropped-unreachable
                               :from from :to to})

      (>= (count (:inflight sim)) max-inflight)
      (update sim :trace conj {:tick (:tick sim) :event :dropped-overflow
                               :from from :to to})

      :else
      (let [[roll rng'] (rng/next-double (:rng sim))
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
  (let [[_path effect] (node/unwrap-instance effect)
        kind (node/effect-kind effect)
        params (node/effect-params effect)]
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
      (let [{:keys [writes durable? epoch then truncate-from]} params
            ;; Caller-supplied token when present; the interpreter only invents
            ;; one as a fallback, because a node that cannot name its own write
            ;; cannot correlate the completion with it.
            token (or (:token params) (:next-msg-id sim))
            at (+ (:tick sim) (if durable? (get-in sim [:config :persist-latency]) 0))
            record {:tick (:tick sim) :writes writes :durable? durable?
                    :truncate-from truncate-from}]
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
      ;; An empty `:dropped` means "truncate to `to-vertex`, whatever is there",
      ;; which a restarting node needs because it cannot know what we still
      ;; hold. A non-empty one that does not match our tail is a bug in the
      ;; algorithm and is surfaced rather than applied.
      (let [to (:to-vertex params)
            claimed (vec (:dropped params))
            committed (vec (get-in sim [:committed peer-id] []))
            at (last (keep-indexed (fn [i v] (when (= v to) i)) committed))
            keep-n (if at (inc at) 0)
            dropped (subvec committed keep-n)
            mismatch? (and (seq claimed) (not= claimed dropped))
            sim (if mismatch?
                  (update sim :trace conj
                          {:tick (:tick sim) :event :revert-mismatch :peer peer-id
                           :claimed claimed :actual dropped})
                  sim)]
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
  "Feed one input to a node and interpret whatever it returns."
  [sim peer-id input]
  (if-not (live? sim peer-id)
    sim
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
       (let [pending (get-in s [:pending-persist peer-id] [])
             due (filter #(<= (:at %) t) pending)
             remaining (vec (remove #(<= (:at %) t) pending))]
         (reduce (fn [s2 {:keys [token epoch then record]}]
                   (-> s2
                       ;; The write is now on disk and survives a crash. This is
                       ;; the ONLY place durable state grows; a write that was
                       ;; issued but never completed is genuinely lost, which is
                       ;; what makes a crash-before-fsync test mean anything.
                       (update-in [:storage peer-id :landed] (fnil conj []) record)
                       (update-in [:storage peer-id :durable]
                                  merge (:writes record))
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

(defn advance
  "Advance the simulation by one tick."
  [sim]
  (-> sim
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
  "Crash a node: it stops stepping and its in-memory state is frozen.

  Its durable storage survives, which is what makes `restart` meaningful."
  [sim peer-id]
  (-> sim
      (update :crashed conj peer-id)
      (update :trace conj {:tick (:tick sim) :event :crash :peer peer-id})))

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
