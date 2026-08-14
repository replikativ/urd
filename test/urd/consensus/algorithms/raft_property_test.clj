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
  "If two logs hold an entry with the same index AND term, every preceding entry
  is identical. Checking the entries themselves is equivalent and stricter, so
  we compare the whole prefix."
  [s]
  (let [logs (into {} (map (fn [p] [p (:log (sim/node-state s p))])) (:peer-ids s))]
    (for [[p a] logs
          [q b] logs
          :when (not= p q)
          i (range 1 (inc (min (count a) (count b))))
          :let [ea (nth a (dec i)), eb (nth b (dec i))]
          :when (and (= (:term ea) (:term eb)) (not= ea eb))]
      {:violation :log-matching :peers [p q] :index i :entries [ea eb]})))

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
        :when (and (number? i) (> (:term st) commit-term))
        :let [have (entry-at st i)]
        :when (not= entry have)]
    {:violation :leader-completeness :leader l :leader-term (:term st)
     :index i :commit-term commit-term :want entry :have have}))

(defn leader-append-only
  "A leader never truncates its own log. `prev` is the previous snapshot of
  (peer -> [role term log])."
  [s prev]
  (let [now (into {} (map (fn [p] [p (let [st (sim/node-state s p)]
                                       {:role (:role st) :term (:term st)
                                        :log (:log st)})]))
                  (:peer-ids s))
        vs (for [p (:peer-ids s)
                 :let [was (get prev p), is (get now p)]
                 :when (and was
                            (= :leader (:role was)) (= :leader (:role is))
                            (= (:term was) (:term is))
                            (not (contains? (:crashed s) p))
                            (not= (take (count (:log was)) (:log is))
                                  (seq (:log was))))]
             {:violation :leader-append-only :peer p
              :before (mapv :term (:log was)) :after (mapv :term (:log is))})]
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
      (is (> (reduce + commits) 300)
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
