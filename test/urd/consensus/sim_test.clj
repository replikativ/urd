(ns urd.consensus.sim-test
  "Tests for the deterministic simulator and its PRNG.

  The property that matters most here is REPRODUCIBILITY: a run must be a pure
  function of its seed and configuration, including under faults. If that ever
  breaks, every algorithm test built on the simulator becomes unfalsifiable,
  because a failure could not be re-examined."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.rng :as rng]
            [urd.consensus.sim :as sim]))

;; ============================================================
;; RNG
;; ============================================================

(deftest rng-is-deterministic
  (testing "the same seed yields the same sequence"
    (let [draw (fn [seed k]
                 (loop [r (rng/make seed), acc [], i 0]
                   (if (= i k)
                     acc
                     (let [[w r'] (rng/next-word r)] (recur r' (conj acc w) (inc i))))))]
      (is (= (draw 42 20) (draw 42 20)))
      (is (not= (draw 42 20) (draw 43 20))))))

(deftest rng-stays-in-32-bits
  (testing "values are 32-bit unsigned, so clj and cljs agree bit-for-bit"
    (let [words (loop [r (rng/make 12345), acc [], i 0]
                  (if (= i 500)
                    acc
                    (let [[w r'] (rng/next-word r)] (recur r' (conj acc w) (inc i)))))]
      (is (every? #(and (>= % 0) (<= % 0xFFFFFFFF)) words))
      (is (> (count (distinct words)) 450) "should not cycle quickly"))))

(deftest rng-zero-seed-is-not-a-fixed-point
  (testing "xorshift has 0 as a fixed point; seed 0 must be remapped"
    (let [[w _] (rng/next-word (rng/make 0))]
      (is (pos? w) "seed 0 would otherwise emit only zeros"))))

(defspec rng-next-int-respects-bounds 200
  (prop/for-all [seed gen/nat
                 n (gen/choose 1 1000)]
                (let [[v _] (rng/next-int (rng/make seed) n)]
                  (and (>= v 0) (< v n)))))

(defspec rng-shuffle-is-a-permutation 200
  (prop/for-all [seed gen/nat
                 coll (gen/vector gen/small-integer 0 30)]
                (let [[shuffled _] (rng/shuffle (rng/make seed) coll)]
                  (= (frequencies coll) (frequencies shuffled)))))

(defspec rng-weighted-bag-totals-k 100
  (prop/for-all [seed gen/nat
                 k (gen/choose 1 40)]
                ;; The bag totals exactly k even though indices repeat -- this
                ;; is the Avalanche sampling semantics: stake weight is drawn
                ;; without replacement, so a node CAN be drawn more than once
                ;; and its multiplicity is its vote weight.
                (let [[bag _] (rng/sample-weighted-bag
                               (rng/make seed) [:a :b :c] {:a 1 :b 2 :c 5} k)]
                  (= k (reduce + 0 (vals bag))))))

;; ============================================================
;; A toy node used to drive the simulator
;; ============================================================

(defrecord Decree []
  n/Node
  (init [_ config]
    (let [peer-id (:peer-id config)]
      (n/result {:peer-id peer-id
                 :validators (:validators config)
                 :heard {peer-id peer-id}
                 :committed? false}
                [(n/broadcast :propose {:from peer-id :value peer-id})])))
  (step [_ state input]
    (if (= :message-received (:type input))
      (let [{:keys [from value]} (:msg input)
            heard (assoc (:heard state) from value)
            need (n/byzantine-threshold (count (:validators state)))]
        (if (and (not (:committed? state)) (>= (count heard) need))
          (n/result (assoc state :heard heard :committed? true)
                    [(n/persist-then {:writes {:decision (first (sort (vals heard)))}
                                      :epoch 1
                                      :then [(n/commit [(first (sort (vals heard)))] 0)]})])
          (n/result (assoc state :heard heard))))
      (n/result state))))

(def peers [:a :b :c :d])

(defn- fresh [& [cfg]]
  (sim/make {:seed 7 :nodes (zipmap peers (repeat (->Decree))) :config (or cfg {})}))

;; ============================================================
;; Simulator behaviour
;; ============================================================

(deftest converges-on-a-quiet-network
  (let [s (sim/run (fresh) 60 sim/quiet?)]
    (is (sim/agreement? s))
    (is (every? seq (vals (sim/all-committed s))) "every node committed")))

(deftest persist-barrier-precedes-the-commit
  (testing "a commit gated behind persist-then only lands after the write"
    (let [s (sim/run (fresh) 60 sim/quiet?)
          writes (get-in s [:storage :a :writes])]
      (is (seq writes) "the durable write was recorded")
      (is (:durable? (first writes)) "and it was an fsync, not a buffered write"))))

(deftest partition-blocks-quorum
  (testing "a 2/2 split cannot reach a quorum of 3"
    (let [s (-> (fresh) (sim/partition-network [#{:a :b} #{:c :d}]) (sim/run 40))]
      (is (every? empty? (vals (sim/all-committed s)))))))

(deftest majority-side-of-a-partition-still-commits
  (testing "a 3/1 split lets the majority side finish; the minority stalls"
    (let [s (-> (fresh) (sim/partition-network [#{:a :b :c} #{:d}]) (sim/run 40))]
      (is (seq (sim/committed s :a)))
      (is (empty? (sim/committed s :d)))
      (is (sim/agreement? s) "a lagging node is not a disagreeing node"))))

(deftest restart-discards-in-memory-state
  (testing "restart replays from DURABLE state only"
    (let [s0 (sim/run (fresh) 3)
          before (sim/node-state s0 :b)
          s1 (sim/restart (sim/crash s0 :b) :b)
          after (sim/node-state s1 :b)]
      (is (> (count (:heard before)) (count (:heard after)))
          "unpersisted in-memory state must be lost, or the simulator would
           hide exactly the durability bugs it exists to find")
      (is (some? (get-in s1 [:storage :b])) "durable storage survives"))))

(deftest crashed-nodes-do-not-step
  (let [s (-> (fresh) (sim/run 2) (sim/crash :a))
        before (sim/node-state s :a)
        after (sim/node-state (sim/run s 20) :a)]
    (is (= before after))))

(deftest simulator-detects-a-real-agreement-violation
  (testing "the toy algorithm is genuinely unsafe under message loss, and the
            simulator catches it -- this is a regression test for the DETECTOR,
            not for the algorithm.

            `Decree` commits the minimum of whatever it happened to hear once it
            has a quorum's worth. Under loss, different nodes hold different
            subsets, so they commit different values. A simulator that reported
            agreement here would be useless."
    (let [s (sim/run (fresh {:drop-rate 0.3}) 60)
          committed (vals (sim/all-committed s))
          non-empty (remove empty? committed)]
      (is (> (count (distinct non-empty)) 1)
          "expected divergent commits under 30% loss")
      (is (not (sim/agreement? s))
          "and agreement? must report the violation"))))

;; ============================================================
;; Reproducibility -- the property the whole approach rests on
;; ============================================================

(deftest reproducible-under-faults
  (testing "identical seed and faults produce an identical history"
    (let [run-it #(-> (fresh {:drop-rate 0.3 :duplicate-rate 0.2})
                      (sim/partition-network [#{:a :b :c} #{:d}])
                      (sim/run 25)
                      sim/heal
                      (sim/run 25))
          x (run-it), y (run-it)]
      (is (= (sim/all-committed x) (sim/all-committed y)))
      (is (= (:trace x) (:trace y)))
      (is (= (:tick x) (:tick y))))))

(defspec reproducible-across-seeds 50
  (prop/for-all [seed (gen/choose 1 100000)
                 drop-rate (gen/elements [0.0 0.1 0.3 0.5])]
                (let [run-it #(sim/run
                               (sim/make {:seed seed
                                          :nodes (zipmap peers (repeat (->Decree)))
                                          :config {:drop-rate drop-rate}})
                               40)
                      x (run-it), y (run-it)]
                  (and (= (sim/all-committed x) (sim/all-committed y))
                       (= (:trace x) (:trace y))))))

(defspec different-seeds-explore-different-schedules 30
  ;; Not strictly required for correctness, but if every seed produced the same
  ;; schedule the simulator would only ever explore one history.
  (prop/for-all [a (gen/choose 1 500)]
                (let [run-it (fn [seed]
                               (:trace (sim/run
                                        (sim/make {:seed seed
                                                   :nodes (zipmap peers (repeat (->Decree)))
                                                   :config {:drop-rate 0.4}})
                                        40)))]
                  ;; Over a spread of seeds we should see more than one history.
                  (> (count (distinct (map run-it (range a (+ a 12))))) 1))))
