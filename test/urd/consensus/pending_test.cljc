(ns urd.consensus.pending-test
  "Tests for the park-and-retry pool.

  This is shared machinery under four algorithms, so its bounds matter more
  than most: an eviction policy that is subtly arbitrary strands exactly the
  node it was added to rescue."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.pending :as p]))

(defn- park* [pool [id dep item at]] (p/park pool id dep item at))
(defn- park-all [pool entries] (reduce park* pool entries))

(deftest release-returns-dependents-in-arrival-order
  (let [pool (park-all p/empty-pool
                       [[:x :dep {:v 1} 0]
                        [:y :dep {:v 2} 1]
                        [:z :other {:v 3} 2]])
        [pool' items] (p/release pool :dep)]
    (is (= [{:v 1} {:v 2}] items)
        "a chain parked in order must be replayed in that order")
    (is (= 1 (p/held pool')) "only the released dependency's items leave")
    (is (not (p/waiting-on? pool' :dep)))
    (is (p/waiting-on? pool' :other))))

(deftest releasing-an-unawaited-dependency-is-not-an-error
  (let [[pool items] (p/release p/empty-pool :nobody)]
    (is (= [] items))
    (is (= 0 (p/held pool)))))

(deftest parking-the-same-item-twice-changes-nothing
  (testing "btcd checks for an existing orphan BEFORE adding; Nakamoto did not,
            and a re-delivered header therefore re-stamped its arrival sequence
            and re-ran eviction -- evicting a legitimate orphan to make room for
            something already held"
    (let [once (p/park p/empty-pool :x :dep {:v 1} 0)
          twice (p/park once :x :dep {:v :DIFFERENT} 99)]
      (is (= once twice) "identical, down to the arrival sequence")
      (is (= 1 (p/held twice)))
      (let [[_ items] (p/release twice :dep)]
        (is (= [{:v 1}] items) "the first item is kept, not the re-delivery")))))

(deftest re-parking-does-not-let-a-peer-hold-the-pool-below-capacity
  (testing "the measured btcd/Nakamoto exploit: rotate through already-held
            items and the pool sheds a legitimate entry on every refill"
    (let [full (park-all p/empty-pool
                         (for [i (range 4)] [i :dep {:v i} i]))
          ;; Re-deliver something already held, repeatedly.
          churned (reduce (fn [pool _] (p/park pool 0 :dep {:v 0} 100)) full (range 10))
          [reaped dropped] (p/reap churned nil nil 4)]
      (is (= 4 (p/held churned)) "re-parking never grew the pool")
      (is (= 0 dropped) "so nothing had to be evicted")
      (is (= 4 (p/held reaped))))))

(deftest eviction-is-oldest-first-by-arrival-sequence
  (testing "not by timestamp: whole-second clocks tie, and breaking a tie by id
            or by map order makes eviction arbitrary"
    (let [;; Timestamps DISAGREE with arrival order: the item that arrived
          ;; first carries the latest clock reading. Sorting by `:at` would
          ;; evict `:third`; the policy must evict `:first`. An earlier version
          ;; of this test gave every item the same timestamp, which a stable
          ;; sort reproduced by accident -- it passed against a deliberately
          ;; broken policy and was therefore not a guard at all.
          pool (park-all p/empty-pool
                         [[:first :d {:v 1} 100]
                          [:second :d {:v 2} 50]
                          [:third :d {:v 3} 10]])
          [pool' dropped] (p/reap pool nil nil 2)]
      (is (= 1 dropped))
      (is (not (p/parked? pool' :first)) "the earliest ARRIVAL goes")
      (is (p/parked? pool' :second))
      (is (p/parked? pool' :third) "despite carrying the oldest timestamp"))))

(deftest expiry-drops-by-age-and-keeps-the-rest
  (let [pool (park-all p/empty-pool
                       [[:old :d {:v 1} 0]
                        [:recent :d {:v 2} 90]])
        [pool' dropped] (p/reap pool 100 50 nil)]
    (is (= 1 dropped))
    (is (not (p/parked? pool' :old)))
    (is (p/parked? pool' :recent))))

(deftest reap-without-bounds-drops-nothing
  (let [pool (park-all p/empty-pool [[:a :d {} 0] [:b :d {} 1]])
        [pool' dropped] (p/reap pool nil nil nil)]
    (is (= 0 dropped))
    (is (= 2 (p/held pool')))))

(deftest an-item-with-no-timestamp-never-expires
  (testing "an algorithm without a clock must still be able to park"
    (let [pool (p/park p/empty-pool :a :d {} nil)
          [pool' dropped] (p/reap pool 10000 1 nil)]
      (is (= 0 dropped))
      (is (p/parked? pool' :a)))))

(deftest the-arrival-counter-survives-the-pool-emptying
  (testing "eviction order must stay total across a drain and refill, or two
            items from different eras compare equal"
    (let [pool (p/park p/empty-pool :a :d {:v :a} 0)
          [pool _] (p/release pool :d)
          pool (-> pool
                   (p/park :b :d2 {:v :b} 1)
                   (p/park :c :d2 {:v :c} 2))
          [pool' _] (p/reap pool nil nil 1)]
      (is (= 0 (p/held (first (p/reap pool nil nil 0)))))
      (is (p/parked? pool' :c) "the later arrival survives")
      (is (not (p/parked? pool' :b))))))

(deftest deps-lists-what-to-request
  (let [pool (park-all p/empty-pool [[:a :d1 {} 0] [:b :d2 {} 1] [:c :d1 {} 2]])]
    (is (= #{:d1 :d2} (set (p/deps pool))))
    (let [[pool' _] (p/release pool :d1)]
      (is (= [:d2] (p/deps pool'))
          "a satisfied dependency stops being re-requested"))))

(deftest forgetting-the-last-dependent-removes-the-dependency-entry
  (testing "or `deps` keeps naming things nobody waits on, and the algorithm
            re-requests them forever"
    (let [pool (p/park p/empty-pool :a :d {} 0)
          [pool' _] (p/release pool :d)]
      (is (= [] (p/deps pool')))
      (is (= {} (:by-dep pool'))))))
