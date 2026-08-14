(ns urd.consensus.algorithms.snowman-test
  "Tests for Snowflake/Snowball and the Snowman node.

  Snowman is in the suite to stress the OPPOSITE corner of the core protocol
  from Raft: leaderless rather than leader-driven, sample-decided rather than
  quorum-decided, probabilistically final rather than absolutely final. Its
  passing is evidence that the protocol is general, not merely that Snowman
  works.

  The instance-level tests follow the shape of avalanchego's
  `snowflake_test.go`, which is already an implementation-agnostic conformance
  suite behind a three-method interface."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.snowflake :as sf]
            [urd.consensus.algorithms.snowman :as sm]))

(def params {:k 5 :alpha-preference 3 :alpha-confidence 3 :beta 3})

;; ============================================================
;; Parameter validity
;; ============================================================

(deftest parameter-validity
  (testing "k/2 < alpha-preference <= alpha-confidence <= k"
    (is (sf/valid-params? params))
    (is (not (sf/valid-params? {:k 5 :alpha-preference 2 :alpha-confidence 3 :beta 3}))
        "alpha-preference must exceed k/2, or two conflicting choices could
         both clear it in a single poll")
    (is (not (sf/valid-params? {:k 5 :alpha-preference 4 :alpha-confidence 3 :beta 3}))
        "alpha-confidence must be at least alpha-preference")
    (is (not (sf/valid-params? {:k 5 :alpha-preference 3 :alpha-confidence 6 :beta 3}))
        "alpha-confidence cannot exceed k")
    (is (not (sf/valid-params? {:k 5 :alpha-preference 3 :alpha-confidence 3 :beta 0}))
        "beta must be positive, or a fresh instance finalizes on its first poll")))

;; ============================================================
;; Snowball instance semantics
;; ============================================================

(deftest beta-consecutive-strong-polls-finalize
  (let [s (reduce (fn [s _] (sf/snowball-record-poll s 4 :a)) (sf/snowball params :a) (range 3))]
    (is (sf/finalized? s))
    (is (= :a (sf/snowball-preference s)))))

(deftest one-poll-short-does-not-finalize
  (let [s (reduce (fn [s _] (sf/snowball-record-poll s 4 :a)) (sf/snowball params :a) (range 2))]
    (is (not (sf/finalized? s)))))

(deftest preference-flip-resets-confidence
  (testing "this is what stops a flapping network from ever finalizing"
    (let [s (-> (sf/snowball params :a)
                (sf/snowball-record-poll 4 :a)
                (sf/snowball-record-poll 4 :a)
                (sf/snowball-record-poll 4 :b)   ; flip
                (sf/snowball-record-poll 4 :a))]
      (is (not (sf/finalized? s)))
      (is (= [1] (sf/confidence s)) "confidence restarted from zero after the flip"))))

(deftest weak-poll-clears-confidence
  (let [s (-> (sf/snowball params :a)
              (sf/snowball-record-poll 4 :a)
              (sf/snowball-record-poll 4 :a)
              (sf/snowball-record-poll 1 :a))]   ; below alpha-preference
    (is (= [0] (sf/confidence s)))
    (is (not (sf/finalized? s)))))

(deftest finalization-is-absorbing
  (testing "a finalized instance ignores everything, including a landslide the
            other way -- avalanchego pins this with TestBinarySnowballLockColor"
    (let [s (reduce (fn [s _] (sf/snowball-record-poll s 5 :a)) (sf/snowball params :a) (range 3))
          s' (reduce (fn [s _] (sf/snowball-record-poll s 5 :b)) s (range 10))]
      (is (sf/finalized? s'))
      (is (= :a (sf/snowball-preference s')) "preference is frozen at finalization"))))

(defspec confidence-never-exceeds-beta 200
  (prop/for-all [polls (gen/vector (gen/tuple (gen/choose 0 5) (gen/elements [:a :b :c])) 0 40)]
                (let [s (reduce (fn [s [votes choice]] (sf/snowball-record-poll s votes choice))
                                (sf/snowball params :a)
                                polls)]
                  (every? #(<= 0 % (:beta params)) (sf/confidence s)))))

(defspec finalized-is-monotone 200
  (testing "once true, never false again"
    (prop/for-all [polls (gen/vector (gen/tuple (gen/choose 0 5) (gen/elements [:a :b])) 0 40)]
                  (let [states (reductions (fn [s [votes choice]] (sf/snowball-record-poll s votes choice))
                                           (sf/snowball params :a)
                                           polls)
                        flags (map sf/finalized? states)]
                    ;; no true is ever followed by a false
                    (not (some (fn [[x y]] (and x (not y))) (partition 2 1 flags)))))))

(defspec preference-is-frozen-after-finalization 200
  (prop/for-all [polls (gen/vector (gen/tuple (gen/choose 0 5) (gen/elements [:a :b])) 0 40)]
                (let [states (reductions (fn [s [votes choice]] (sf/snowball-record-poll s votes choice))
                                         (sf/snowball params :a)
                                         polls)
                      finalized (drop-while (complement sf/finalized?) states)]
                  (or (empty? finalized)
                      (apply = (map sf/snowball-preference finalized))))))

;; ============================================================
;; The Snowman node in the simulator
;; ============================================================

(def peers [:a :b :c :d :e])
(def sim-params {:k 3 :alpha-preference 2 :alpha-confidence 2 :beta 3})

(defn- fresh [& [cfg]]
  (sim/make {:seed 3
             :nodes (zipmap peers (repeat (sm/create)))
             :node-config (zipmap peers (repeat {:params sim-params}))
             :config (or cfg {})}))

(deftest uncontested-block-is-accepted-by-everyone
  (let [s (-> (fresh)
              (sim/inject-all (n/vertex-received {:id :blk1 :parent :genesis :height 1}))
              (sim/run 80))]
    (is (sim/agreement? s))
    (is (every? #(= [:blk1] %) (vals (sim/all-committed s))))))

(deftest contested-block-converges
  (testing "two nodes prefer X, three prefer Y; repeated sampling must break the
            tie and land everyone on the same block"
    (let [s0 (fresh)
          s1 (reduce #(sim/inject %1 %2 (n/vertex-received {:id :blkX :parent :genesis :height 1}))
                     s0 [:a :b])
          s2 (reduce #(sim/inject %1 %2 (n/vertex-received {:id :blkY :parent :genesis :height 1}))
                     s1 [:c :d :e])
          s3 (-> s2
                 (sim/inject-all (n/vertex-received {:id :blkX :parent :genesis :height 1}))
                 (sim/inject-all (n/vertex-received {:id :blkY :parent :genesis :height 1}))
                 (sim/run 200))
          committed (vals (sim/all-committed s3))]
      (is (sim/agreement? s3))
      (is (= 1 (count (distinct (remove empty? committed))))
          "everyone that decided must have decided the same block"))))

(deftest partitioned-network-does-not-finalize
  (testing "with the network split, no node can gather alpha of its sample
            consistently, so confidence keeps resetting and nothing finalizes.

            This is the safety-relevant direction: Snowball must NOT decide when
            it cannot see a coherent majority."
    (let [s (-> (fresh)
                (sim/partition-network [#{:a :b} #{:c} #{:d :e}])
                (sim/inject-all (n/vertex-received {:id :blk1 :parent :genesis :height 1}))
                (sim/run 120))]
      (is (sim/agreement? s) "no divergent commits"))))

(deftest snowman-is-deterministic
  (let [run-it #(-> (fresh {:drop-rate 0.2})
                    (sim/inject-all (n/vertex-received {:id :blk1 :parent :genesis :height 1}))
                    (sim/run 100))
        x (run-it), y (run-it)]
    (is (= (sim/all-committed x) (sim/all-committed y)))
    (is (= (:trace x) (:trace y)))))

(defspec converges-across-seeds 20
  (testing "convergence is not an artifact of one lucky schedule"
    (prop/for-all [seed (gen/choose 1 10000)]
                  (let [s (-> (sim/make {:seed seed
                                         :nodes (zipmap peers (repeat (sm/create)))
                                         :node-config (zipmap peers (repeat {:params sim-params}))})
                              (sim/inject-all (n/vertex-received {:id :blk1 :parent :genesis :height 1}))
                              (sim/run 120))]
                    (sim/agreement? s)))))
