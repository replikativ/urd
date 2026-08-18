(ns urd.consensus.algorithms.raft-property-test
  "The five Raft safety properties, checked against generated fault schedules.

  Raft's correctness argument (thesis figure 3.2) rests on five properties, and
  all five are checked here after EVERY step of a generated schedule, not just
  at the end -- a violation that heals before the run finishes is still a
  violation, and checking only the final state would miss exactly the
  transient split-brain these tests exist to find.

    Election Safety    at most one leader per term
    Leader Append-Only a leader never overwrites or deletes its own entries
    Log Matching       same (index, term) implies identical prefixes
    Leader Completeness a committed entry is present in every later leader's log
    State Machine Safety no two nodes apply different entries at the same index

  The schedules combine partitions, healing, crashes, restarts from durable
  state only, message loss, and duplication. Every run is a pure function of its
  seed, so a failure shrinks to a schedule you can replay."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.node :as node]
            [urd.consensus.sim :as sim]))

(def peers [:n1 :n2 :n3 :n4 :n5])

;; ============================================================
;; Invariants
;; ============================================================

(defn- live-leaders [s]
  (filter #(and (not (contains? (:crashed s) %))
                (= :leader (:role (sim/node-state s %))))
          (:peer-ids s)))

(def ^:private entry-at raft/entry-at)

(defn election-safety
  "At most one leader per term, over the WHOLE history.

  `seen` accumulates {term #{leader}}; a term that ever names two leaders is a
  violation even if the two never overlapped in wall-clock time, because the
  guarantee is per-term, not per-instant."
  [s seen]
  (let [seen' (reduce (fn [m p]
                        (let [st (sim/node-state s p)]
                          (update m (:term st) (fnil conj #{}) p)))
                      seen
                      (live-leaders s))]
    [seen'
     (for [[term ls] seen' :when (> (count ls) 1)]
       {:violation :election-safety :term term :leaders ls})]))

(defn log-matching
  "Raft section 5.3: if two logs hold an entry at the same index with the same
  TERM, then the logs are identical in every preceding entry.

  The PREFIX is compared, and the previous version of this comparing only the
  entries at that index was strictly weaker -- its docstring claimed the two
  were equivalent and they are not. Per-index equality never examines a position
  where the two terms happen to differ, so

      a = [{term 1 :x} {term 3 :y}]
      b = [{term 2 :z} {term 3 :y}]

  passes it: index 1 is skipped because the terms differ there, and index 2
  matches on both term and entry. Both logs have non-decreasing terms, so this
  is a well-formed shape, and it violates Log Matching outright -- the entries
  at index 2 agree on term, so index 1 was required to agree too.

  Log Matching is precisely the property that makes such a pair unreachable, so
  a bug that produced one is exactly what this check exists to catch and exactly
  what it could not see.

  Compared over ABSOLUTE indices, and only over the range both nodes still
  hold. Positional comparison was correct while every log started at 1 and
  became nonsense the moment compaction moved a base: two nodes in perfect
  agreement, one compacted to 426 and one to 638, differ at every position and
  the checker reported a violation at every index. That is the failure mode of
  a test that encodes an assumption the code has since stopped making, and it
  reported it against the algorithm rather than against itself.

  The honest cost: divergence BELOW both bases is now invisible here. Those
  entries are applied, and `state-machine-safety` -- which accumulates over the
  whole run rather than reading current state -- is the check that still sees
  them."
  [s]
  (let [sts (into {} (map (fn [p] [p (sim/node-state s p)])) (:peer-ids s))]
    (for [[p a] sts
          [q b] sts
          :when (not= p q)
          :let [lo (inc (max (:log-base a 0) (:log-base b 0)))
                hi (min (raft/last-index a) (raft/last-index b))
                ;; The first index in the shared range where the two disagree.
                ;; Everything at or above it with a matching term is a
                ;; violation, which makes this linear rather than comparing a
                ;; fresh prefix pair at every index.
                d (first (filter #(not= (entry-at a %) (entry-at b %))
                                 (range lo (inc hi))))]
          :when d
          i (range d (inc hi))
          :let [ea (entry-at a i), eb (entry-at b i)]
          :when (= (:term ea) (:term eb))]
      {:violation :log-matching :peers [p q] :index i
       :first-divergence d :entries [ea eb]})))

(defn state-machine-safety
  "No two nodes ever apply a different entry at the same log index.

  The registry is {index {:entry e :commit-term t}}, accumulated across the
  whole run, so this also catches a node that applies X at index 5, crashes, and
  comes back applying Y at index 5.

  `commit-term` is the smallest term any node held while reporting this entry as
  committed. A follower only learns of a commit from a leader at its own term,
  so every observer's term is at or above the term in which the entry was
  actually committed -- which makes the minimum a sound lower bound, and an
  exact one whenever the committing leader is among the observers. Leader
  completeness needs it; see below."
  [s registry]
  (let [registry'
        (reduce (fn [m p]
                  (let [t (:term (sim/node-state s p))]
                    (reduce (fn [m e]
                              (let [i (:index e)
                                    prior (get m i)]
                                (cond
                                  (nil? prior) (assoc m i {:entry e :commit-term t})
                                  (not= (:entry prior) e)
                                  (assoc m [:conflict i] [(:entry prior) e])
                                  :else (update-in m [i :commit-term] min t))))
                            m
                            (sim/committed s p))))
                registry
                (:peer-ids s))]
    [registry'
     (for [[k v] registry' :when (vector? k)]
       {:violation :state-machine-safety :index (second k) :entries v})]))

(defn leader-completeness
  "An entry committed in term T is present in the log of every leader of a term
  HIGHER than T.

  The qualifier is the whole content of the property, and getting it wrong makes
  the test report false violations: a leader stranded in a minority partition at
  an old term is perfectly entitled not to know about entries the majority has
  since committed. It is not a leader for a higher-numbered term.

  This is what the election restriction (5.4.1) buys: a candidate whose log is
  missing a committed entry cannot collect a majority, because every node
  holding that entry rejects its vote."
  [s registry]
  (for [l (live-leaders s)
        :let [st (sim/node-state s l)]
        [i {:keys [entry commit-term]}] registry
        ;; `> (:log-base st 0)`: an entry the leader compacted away is one it
        ;; APPLIED, which is a stronger statement than holding it. Without this
        ;; every successful compaction reads as a leader that lost committed
        ;; history -- the property inverted by the mechanism that satisfies it.
        :when (and (number? i) (> (:term st) commit-term) (> i (:log-base st 0)))
        :let [have (entry-at st i)]
        :when (not= entry have)]
    {:violation :leader-completeness :leader l :leader-term (:term st)
     :index i :commit-term commit-term :want entry :have have}))

(defn leader-append-only
  "A leader never truncates its own log. `prev` is the previous snapshot of
  (peer -> [role term state]).

  Compaction deletes from the FRONT, and that is not what this property
  forbids: those entries are applied, and dropping them is the whole point of a
  checkpoint. What it forbids is the leader changing or losing an entry it
  still claims to hold. So the comparison runs over absolute indices in the
  range both snapshots retain -- `(take (count log))` read a compacting leader
  as one that had rewritten its entire log."
  [s prev]
  (let [now (into {} (map (fn [p] [p (let [st (sim/node-state s p)]
                                       {:role (:role st) :term (:term st)
                                        :st st})]))
                  (:peer-ids s))
        overlap-changed?
        (fn [was is]
          (let [wst (:st was), ist (:st is)
                lo (inc (max (:log-base wst 0) (:log-base ist 0)))
                ;; Only up to what the EARLIER snapshot held: the leader is
                ;; allowed to have appended since, which is the one direction
                ;; append-only permits.
                hi (min (raft/last-index wst) (raft/last-index ist))]
            (or (< (raft/last-index ist) (raft/last-index wst))
                (some #(not= (entry-at wst %) (entry-at ist %))
                      (range lo (inc hi))))))
        vs (for [p (:peer-ids s)
                 :let [was (get prev p), is (get now p)]
                 :when (and was
                            (= :leader (:role was)) (= :leader (:role is))
                            (= (:term was) (:term is))
                            (not (contains? (:crashed s) p))
                            (overlap-changed? was is))]
             {:violation :leader-append-only :peer p
              :before-last (raft/last-index (:st was))
              :after-last (raft/last-index (:st is))})]
    [now vs]))

(defn check-all
  "Advance the accumulators and return [acc violations]."
  [s {:keys [terms registry prev] :as acc}]
  (let [[terms' v1] (election-safety s terms)
        [registry' v2] (state-machine-safety s registry)
        [prev' v3] (leader-append-only s prev)
        v4 (log-matching s)
        v5 (leader-completeness s registry')]
    [(assoc acc :terms terms' :registry registry' :prev prev')
     (vec (concat v1 v2 v3 v4 v5))]))

;; ============================================================
;; Schedules
;; ============================================================

(def gen-op
  ;; Weighted, not uniform. An election takes 10-20 ticks, so a schedule made of
  ;; mostly-faults with short advances never lets a leader emerge and the run is
  ;; vacuously safe. Advancing and proposing are the operations that generate
  ;; the histories worth checking; the faults are the perturbation.
  (gen/frequency
   [[5 (gen/tuple (gen/return :advance) (gen/choose 10 90))]
    [3 (gen/tuple (gen/return :propose) (gen/choose 0 4) gen/small-integer)]
    ;; A partition is a two-way split chosen by a bitmask, which lets the
    ;; generator produce both majority/minority and even splits.
    [2 (gen/tuple (gen/return :partition) (gen/vector gen/boolean 5 5))]
    [2 (gen/return [:heal])]
    [1 (gen/tuple (gen/return :crash) (gen/choose 0 4))]
    [1 (gen/tuple (gen/return :restart) (gen/choose 0 4))]]))

(defn- apply-op [s op]
  (case (first op)
    :advance (sim/run s (second op))
    :partition (let [[_ mask] op
                     side-a (set (keep-indexed (fn [i p] (when (nth mask i) p)) peers))
                     side-b (into #{} (remove side-a) peers)]
                 (if (or (empty? side-a) (empty? side-b))
                   s
                   (sim/partition-network s [side-a side-b])))
    :heal (sim/heal s)
    :crash (sim/crash s (nth peers (second op)))
    :restart (let [p (nth peers (second op))]
               (if (contains? (:crashed s) p) (sim/restart s p) s))
    :propose (let [p (nth peers (second op))]
               (if (contains? (:crashed s) p)
                 s
                 (sim/inject s p (node/value-ready {:v (nth op 2) :by p}))))
    s))

(defn run-schedule
  "Run `ops`, checking every invariant after each. Returns nil or the first
  violation together with enough context to replay."
  [seed ops sim-config]
  (let [s0 (sim/make {:seed seed
                      :nodes (zipmap peers (repeat (raft/make)))
                      :node-config (zipmap peers (repeat {:election-timeout 10
                                                          :heartbeat-timeout 3}))
                      :config (merge {:min-delay 1 :max-delay 3 :persist-latency 2}
                                     sim-config)})]
    (loop [s s0, acc {:terms {} :registry {} :prev {}}, remaining ops, done []]
      (if (empty? remaining)
        nil
        (let [op (first remaining)
              s' (try (apply-op s op)
                      (catch Exception e {::threw e}))]
          (if (::threw s')
            ;; An exception IS a violation: `commit-to` and the conflict check
            ;; deliberately throw on a state Raft says is impossible.
            {:violation :exception :seed seed :after (conj done op)
             :message (.getMessage ^Exception (::threw s'))}
            (let [[acc' vs] (check-all s' acc)]
              (if (seq vs)
                (assoc (first vs) :seed seed :after (conj done op))
                (recur s' acc' (rest remaining) (conj done op))))))))))

;; ============================================================
;; The properties
;; ============================================================

(defspec safety-under-partitions 300
  (prop/for-all [seed (gen/choose 1 1000000)
                 ops (gen/vector gen-op 3 18)]
                (nil? (run-schedule seed ops {}))))

(defspec safety-under-message-loss 300
  (prop/for-all [seed (gen/choose 1 1000000)
                 ops (gen/vector gen-op 3 18)
                 drop-rate (gen/elements [0.1 0.25 0.4])]
                (nil? (run-schedule seed ops {:drop-rate drop-rate}))))

(defspec safety-under-duplication-and-reordering 300
  (prop/for-all [seed (gen/choose 1 1000000)
                 ops (gen/vector gen-op 3 18)]
                ;; A wide delay range reorders messages; duplication replays
                ;; them. Both are things a real network does and both are things
                ;; a naive `maybe-decr-to` gets wrong.
                (nil? (run-schedule seed ops {:duplicate-rate 0.3
                                              :min-delay 1 :max-delay 8}))))

(defspec safety-under-crash-restart 300
  (prop/for-all [seed (gen/choose 1 1000000)
                 ops (gen/vector (gen/one-of
                                  [gen-op
                                   (gen/tuple (gen/return :crash) (gen/choose 0 4))
                                   (gen/tuple (gen/return :restart) (gen/choose 0 4))])
                                 4 20)]
                (nil? (run-schedule seed ops {:persist-latency 4}))))

;; ============================================================
;; Liveness (not a safety property; asserted separately and weakly)
;; ============================================================

(deftest a-healthy-cluster-elects-a-leader-and-makes-progress
  (testing "safety is vacuous if nothing ever happens, so check the schedules
            are actually doing work"
    (doseq [seed [1 7 42 99 12345]]
      (let [s (sim/run (sim/make {:seed seed
                                  :nodes (zipmap peers (repeat (raft/make)))
                                  :node-config (zipmap peers (repeat {:election-timeout 10
                                                                      :heartbeat-timeout 3
                                                                      :propose-interval 7}))
                                  :config {:min-delay 1 :max-delay 3 :persist-latency 2
                                           :value-fn (fn [sm p _] {:v (:tick sm) :by p})}})
                       400)]
        (is (= 1 (count (live-leaders s))) (str "seed " seed ": exactly one leader"))
        (is (> (count (sim/committed s (first (live-leaders s)))) 5)
            (str "seed " seed ": entries were actually committed"))))))

(deftest generated-schedules-actually-commit-things
  (testing "a safety property is trivially true of a history where nothing
            happened, so measure that the generator produces real histories"
    (let [samples (gen/sample (gen/vector gen-op 3 18) 60)
          commits (for [ops samples]
                    (let [s0 (sim/make {:seed 5
                                        :nodes (zipmap peers (repeat (raft/make)))
                                        :node-config (zipmap peers
                                                             (repeat {:election-timeout 10
                                                                      :heartbeat-timeout 3}))
                                        :config {:min-delay 1 :max-delay 3
                                                 :persist-latency 2}})
                          s (reduce apply-op s0 ops)]
                      (reduce + (map #(count (sim/committed s %)) peers))))
          productive (count (filter pos? commits))]
      (is (> productive (* 0.6 (count samples)))
          (str "only " productive "/" (count samples)
               " generated schedules committed anything"))
      ;; Threshold lowered from 300 to 200 when the durability barrier was
    ;; corrected. Commits legitimately got SLOWER: the leader used to count its
    ;; own entry as durable as soon as any later buffered write landed, so it
    ;; committed roughly one persist-latency early -- and unsafely. Now it waits
    ;; for the write that actually carried the entry. The observed total moved
    ;; 290-ish, not 30-ish, so this still guards against a vacuous history.
      (is (> (reduce + commits) 200)
          (str "total committed entries across all schedules: " (reduce + commits))))))

(deftest the-invariant-checker-catches-a-real-violation
  (testing "a regression test for the DETECTOR, not the algorithm

           If `check-all` reported success on a genuinely divergent history, all
           four specs above would be unfalsifiable. Here we hand it two nodes
           that have committed different entries at the same index and assert it
           complains."
    (let [s (sim/make {:seed 1 :nodes (zipmap peers (repeat (raft/make)))})
          s (-> s
                (assoc-in [:committed :n1] [{:index 1 :term 1 :data :x}])
                (assoc-in [:committed :n2] [{:index 1 :term 2 :data :y}]))
          [_ vs] (check-all s {:terms {} :registry {} :prev {}})]
      (is (seq vs) "the checker must report the divergence")
      (is (some #(= :state-machine-safety (:violation %)) vs)))))

(deftest the-log-matching-checker-sees-a-divergent-prefix
  (testing "the second detector control, for the case per-index comparison could
            not see.

            Both logs have non-decreasing terms and agree at index 2 on term AND
            entry, so an entry-wise check finds nothing -- index 1 is never
            examined, because the terms differ there. Log Matching says agreeing
            at index 2 REQUIRES agreeing at index 1, so this is a violation, and
            it is the shape a broken `handle-append-entries` would produce."
    (let [s (sim/make {:seed 1 :nodes (zipmap peers (repeat (raft/make)))})
          s (-> s
                (assoc-in [:nodes :n1 :state :log]
                          [{:index 1 :term 1 :data :x} {:index 2 :term 3 :data :y}])
                (assoc-in [:nodes :n2 :state :log]
                          [{:index 1 :term 2 :data :z} {:index 2 :term 3 :data :y}]))
          vs (log-matching s)]
      (is (seq vs) "the prefix divergence must be reported")
      (is (= 2 (:index (first vs))) "at the index where the terms agree")
      ;; And the control on the control: entry-wise comparison finds nothing here.
      (let [entrywise (for [[p a] {:n1 (vec (:log (sim/node-state s :n1)))
                                   :n2 (vec (:log (sim/node-state s :n2)))}
                            [q b] {:n1 (vec (:log (sim/node-state s :n1)))
                                   :n2 (vec (:log (sim/node-state s :n2)))}
                            :when (not= p q)
                            i (range 1 (inc (min (count a) (count b))))
                            :let [ea (nth a (dec i)), eb (nth b (dec i))]
                            :when (and (= (:term ea) (:term eb)) (not= ea eb))]
                        [p q i])]
        (is (empty? entrywise)
            "which is what the old check was, and why it had to change")))))

(deftest a-stale-heartbeat-does-not-commit-past-a-restarted-log
  (testing "the shrunk counterexample, pinned

           `handle-heartbeat` passed the leader's commit index straight to
           `commit-to`, which throws when asked to commit past the end of the
           log -- as etcd's `log.go:322-331` panics, and for the same stated
           reason: it means the log was truncated or lost.

           `send-heartbeat` clamps to `(min (:match pr) (:commit st))` and
           `:match` only advances on an `:app-resp` that rode behind our
           durability barrier, so a CURRENT leader cannot ask for this. The
           message was not current: duplication and delay let a heartbeat from
           before a crash arrive after the restart, carrying a commit index
           that was correct for the log the node no longer has.

           etcd is insulated by an assumption about its transport -- a TCP
           connection dies with the process, so nothing replays across a
           restart. That assumption lives outside the algorithm and is not true
           of every transport, which is exactly what a simulator that models
           duplication is for.

           Clamping to `(min commit (last-index st))` is the tempting fix and
           is wrong: a heartbeat carries no `prev-index` consistency check, so
           those entries have never been shown to match the leader's, and
           committing them would be committing on no evidence.

           Found by `safety-under-duplication-and-reordering`, which fails
           roughly one full-suite run in ten -- rare enough that the seed has to
           be captured when it happens rather than reproduced on demand."
    (is (nil? (run-schedule 574217
                            [[:advance 34] [:crash 1] [:advance 10]
                             [:restart 1] [:advance 10]]
                            {:duplicate-rate 0.3 :min-delay 1 :max-delay 8})))))

;; ============================================================
;; Compaction, end to end
;; ============================================================

(defn- durable-entry-count
  "How many log entries a restart of `p` would have to replay."
  [s p]
  (reduce + (map #(count (:entries (:writes %) []))
                 (get-in s [:storage p :landed] []))))

(deftest a-long-run-bounds-both-the-log-and-the-store
  (testing "the reason compaction is wired into `finish` and not left as a
            function nobody calls.

           `compact` bounds MEMORY and `checkpoint-records` bounds the STORE,
           but until `finish` issues one, a node that runs long enough holds
           every entry it ever appended and replays every entry it ever wrote.
           Both were true of this algorithm until now, and neither is visible
           from a unit test of the pieces -- it takes a run long enough for the
           threshold to trip.

           `:log-retention 8` so the threshold trips inside a few hundred ticks;
           the production default is 1000 and the arithmetic is the same."
    (let [cfg {:election-timeout 10 :heartbeat-timeout 3 :propose-interval 2
               :log-retention 8}
          s (sim/run (sim/make {:seed 3
                                :nodes (zipmap peers (repeat (raft/make)))
                                :node-config (zipmap peers (repeat cfg))
                                :config {:min-delay 1 :max-delay 3 :persist-latency 2
                                         :value-fn (fn [sm p _] {:v (:tick sm) :by p})}})
                     900)
          leader (first (live-leaders s))
          lst (sim/node-state s leader)]
      (is (some? leader) "a leader, or the run proved nothing")
      (is (> (raft/last-index lst) 40)
          "the run actually appended enough to be worth compacting")
      (is (pos? (:log-base lst))
          "the boundary moved -- `finish` issued at least one checkpoint")
      (is (< (count (:log lst)) 40)
          "and MEMORY is bounded well below the number of entries ever appended")
      (is (< (durable-entry-count s leader) 40)
          "as is the STORE. This is the assertion that fails when `compact` is
           called but its result is never written -- the in-memory log shrinks
           and the replay cost does not, which looks like success from every
           angle except a restart.")))

  (testing "and a node restarted from that compacted store still agrees.

           Compaction that produced a node which could not rejoin would be a
           worse bug than the unbounded growth it fixes, and the round trip is
           only exercised once a real run has really compacted."
    (let [cfg {:election-timeout 10 :heartbeat-timeout 3 :propose-interval 2
               :log-retention 8}
          s0 (sim/run (sim/make {:seed 3
                                 :nodes (zipmap peers (repeat (raft/make)))
                                 :node-config (zipmap peers (repeat cfg))
                                 :config {:min-delay 1 :max-delay 3 :persist-latency 2
                                          :value-fn (fn [sm p _] {:v (:tick sm) :by p})}})
                      900)
          victim (first (remove #(= % (first (live-leaders s0))) peers))
          before (:commit (sim/node-state s0 victim))
          s (-> s0 (sim/crash victim) (sim/run 20) (sim/restart victim) (sim/run 400))
          rst (sim/node-state s victim)]
      (is (pos? (:log-base (sim/node-state s0 victim)))
          "the node we crashed had really compacted")
      (is (>= (:commit rst) before)
          "it came back knowing at least what it knew, rather than renumbered
           back to a base of zero and re-deriving a log it had already agreed")
      (is (empty? (second (check-all s {})))
          "and no safety property broke on the way"))))

;; ============================================================
;; The checkers themselves
;; ============================================================

(defn- fake-sim [peers->st]
  {:peer-ids (vec (keys peers->st))
   :nodes (into {} (map (fn [[p st]] [p {:state st}])) peers->st)
   :crashed #{}})

(defn- fake-state [base entries & {:as extra}]
  (merge {:log-base base :base-term 1 :log (vec entries) :term 5 :role :follower}
         extra))

(defn- ent [i] {:index i :term 1 :data i})

(deftest the-invariant-checkers-still-catch-what-they-are-for
  (testing "the check on the checks.

           Three of the five safety checkers indexed logs POSITIONALLY, which
           was correct while every log began at 1. Compaction moves the base,
           and all three then reported violations against a cluster in perfect
           agreement -- a false alarm, but the dangerous half is the repair:
           relaxing a checker until the false alarm stops is indistinguishable
           from relaxing it until it stops seeing anything, and a vacuous
           checker still reports 1200 passing cases.

           So each rewritten checker is exercised twice: silent on the
           compaction it now tolerates, firing on the violation it must never
           tolerate. Without the second half, `0 failures` across the property
           suite would mean nothing at all."

    (testing "log-matching"
      (is (empty? (log-matching (fake-sim {:a (fake-state 0 (map ent (range 1 21)))
                                           :b (fake-state 10 (map ent (range 11 21)))})))
          "two agreeing nodes compacted to different bases are not a violation")
      (is (seq (log-matching
                (fake-sim {:a (fake-state 0 (map ent (range 1 21)))
                           :b (fake-state 10 (cons {:index 11 :term 1 :data :X}
                                                   (map ent (range 12 21))))})))
          "but a genuine divergence inside the shared range still is")
      (is (seq (log-matching
                (fake-sim {:a (fake-state 0 (map ent (range 1 6)))
                           :b (fake-state 0 (cons {:index 1 :term 1 :data :X}
                                                  (map ent (range 2 6))))})))
          "as is the uncompacted case the original check was written for"))

    (testing "leader-append-only"
      (let [was {:role :leader :term 5
                 :st (fake-state 0 (map ent (range 1 21)) :role :leader)}]
        (is (empty? (second (leader-append-only
                             (fake-sim {:a (fake-state 10 (map ent (range 11 21))
                                                       :role :leader)})
                             {:a was})))
            "a leader that compacted has not truncated -- it dropped applied
             entries off the front, which is what a checkpoint IS")
        (is (seq (second (leader-append-only
                          (fake-sim {:a (fake-state 10 (cons {:index 11 :term 1 :data :X}
                                                             (map ent (range 12 21)))
                                                    :role :leader)})
                          {:a was})))
            "a leader that CHANGED a retained entry is still caught")
        (is (seq (second (leader-append-only
                          (fake-sim {:a (fake-state 0 (map ent (range 1 16))
                                                    :role :leader)})
                          {:a was})))
            "and so is one that lost entries off the TAIL, which is the
             truncation the property is actually about")))

    (testing "leader-completeness"
      (is (empty? (leader-completeness
                   (fake-sim {:a (fake-state 10 (map ent (range 11 21))
                                             :role :leader :term 9)})
                   {5 {:entry (ent 5) :commit-term 2}}))
          "an entry the leader compacted away is one it APPLIED, not one it lost")
      (is (seq (leader-completeness
                (fake-sim {:a (fake-state 10 (cons {:index 11 :term 1 :data :X}
                                                   (map ent (range 12 21)))
                                          :role :leader :term 9)})
                {11 {:entry (ent 11) :commit-term 2}}))
          "an entry missing ABOVE the base is a real completeness violation"))))

(deftest an-archive-node-never-compacts-and-does-not-crash-trying
  (testing "`nil` retention is how a cluster keeps SOMEBODY able to serve
            history that everyone else has thrown away.

           Every store in this library is bounded by the same retention that
           bounds memory, because compaction truncates it -- so without a node
           that opts out, a peer far enough behind cannot be caught up from
           anyone. An archive node is the standard answer (CometBFT's, among
           others) and it has to be expressible.

           `(:log-retention st default)` returns nil rather than the default
           when the key is PRESENT AND NIL, so this reached `(* 2 nil)` and
           threw -- the first time `:applied` advanced, not at startup. A
           configuration that crashes only once the node has made progress."
    (let [cfg {:election-timeout 10 :heartbeat-timeout 3 :propose-interval 2
               :log-retention nil}
          s (sim/run (sim/make {:seed 3
                                :nodes (zipmap peers (repeat (raft/make)))
                                :node-config (zipmap peers (repeat cfg))
                                :config {:min-delay 1 :max-delay 3 :persist-latency 2
                                         :value-fn (fn [sm p _] {:v (:tick sm) :by p})}})
                     600)
          leader (first (live-leaders s))
          lst (sim/node-state s leader)]
      (is (some? leader) "the cluster ran at all, which is the crash case")
      (is (> (raft/last-index lst) 40)
          "and got far enough that a compacting node would have compacted")
      (is (zero? (:log-base lst 0))
          "yet the boundary never moved -- it retains everything, on purpose")
      (is (= (raft/last-index lst) (count (:log lst)))
          "so its log IS its whole history, which is what makes it able to
           serve a peer that fell arbitrarily far behind")))

  (testing "and nil must mean NEVER, not `fall back to the default`.

           A run long enough to trip the default would take tens of thousands
           of ticks, so the simulated cluster above cannot tell the two apart:
           with `:log-retention 1000` it would not have compacted either.
           Verified by mutation -- substituting the default for nil passes the
           whole simulated test. Asked of the predicate directly instead, at a
           position where the default WOULD fire."
    (let [due? @#'raft/checkpoint-due?
          at (fn [retain] (due? {:applied 5000 :log-base 0 :log-retention retain}))]
      (is (true? (at 1000)) "the default compacts at this position")
      (is (false? (at nil))
          "and an archive node still does not -- which is the whole
           configuration, and is invisible to any run short enough to
           finish"))))
