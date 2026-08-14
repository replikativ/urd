(ns urd.consensus.node-test
  "Tests for the core protocol's membership abstraction.

  Both bugs pinned here were live in shipped code and were found by
  implementing algorithms against the protocol, not by review."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]))

(def ^:private four {:validators [:a :b :c :d]})

;; ============================================================
;; Regression: quorum must count DISTINCT SENDERS
;; ============================================================

(deftest quorum-counts-distinct-senders-not-statements
  (testing "a single validator repeating itself must not reach a quorum.

            This was a live safety hole: `quorum?` counted statements, so three
            copies of one validator's vote cleared a quorum of four and one
            Byzantine validator could decide a height alone. Found while
            implementing Tendermint."
    (is (false? (n/quorum? n/bft-membership four
                           [{:from :a} {:from :a} {:from :a}]
                           (constantly true)))
        "three statements, one sender")
    (is (true? (n/quorum? n/bft-membership four
                          [{:from :a} {:from :b} {:from :c}]
                          (constantly true)))
        "three distinct senders")
    (is (false? (n/quorum? n/bft-membership four
                           [{:from :a} {:from :b}]
                           (constantly true)))
        "two distinct senders is short of the threshold")))

(deftest anonymous-statements-never-count
  (testing "a statement that identifies no sender cannot be attributed, so it
            cannot count toward a threshold"
    (is (false? (n/quorum? n/bft-membership four
                           [{:x 1} {:x 2} {:x 3}]
                           (constantly true))))))

;; ============================================================
;; Regression: a missing validator set must fail loudly
;; ============================================================

(deftest missing-validator-set-throws
  (testing "(count nil) is 0 and every threshold maps 0 to 1, so a state that
            merely forgot :validators would report that ONE statement is a
            quorum -- a silent safety failure that looks like normal operation"
    (is (thrown? Exception (n/quorum? n/bft-membership {} [{:from :a}] (constantly true))))
    (is (thrown? Exception (n/quorum? n/bft-membership {:validators []} [{:from :a}] (constantly true))))))

;; ============================================================
;; Voting power
;; ============================================================

(deftest quorum-respects-voting-power
  (testing "with power supplied, BOTH sides are weight

           This test previously asserted the opposite, and the assertion was
           the bug: it compared :a's 3 power against `byzantine-threshold(4)`,
           the threshold for the validator COUNT, and concluded that half the
           power of a four-node cluster was a Byzantine quorum. The threshold
           for 6 total power is 5."
    (let [weighted (assoc four :voting-power {:a 3 :b 1 :c 1 :d 1})]
      (is (= 5 (n/byzantine-threshold 6)))
      (is (false? (n/quorum? n/bft-membership weighted [{:from :a}] (constantly true)))
          ":a alone holds 3 of 6 power, which is not a Byzantine quorum")
      (is (false? (n/quorum? n/bft-membership weighted
                             [{:from :a} {:from :b}] (constantly true)))
          "4 of 6 is still short")
      (is (true? (n/quorum? n/bft-membership weighted
                            [{:from :a} {:from :b} {:from :c}] (constantly true)))
          "5 of 6 clears it")
      (is (false? (n/quorum? n/bft-membership weighted [{:from :b}] (constantly true)))
          ":b alone holds 1")))
  (testing "uniform power is exactly the unweighted case"
    (let [uniform (assoc four :voting-power {:a 1 :b 1 :c 1 :d 1})]
      (is (= (n/quorum? n/bft-membership four [{:from :a} {:from :b} {:from :c}]
                        (constantly true))
             (n/quorum? n/bft-membership uniform [{:from :a} {:from :b} {:from :c}]
                        (constantly true)))))))

;; ============================================================
;; The f+1 identity
;; ============================================================

(defspec v-blocking-threshold-is-f-plus-one 200
  ;; Tendermint's L55 round-skip fires on f+1 messages from higher rounds.
  ;; That threshold turns out to be EXACTLY the v-blocking one: a set is
  ;; v-blocking when its complement can no longer reach a quorum. Discovered
  ;; independently while implementing Tendermint, and it is a good sign for the
  ;; Membership abstraction that the two coincide rather than needing a special
  ;; case.
  (prop/for-all [nv (gen/choose 1 200)]
                (= (n/byzantine-tolerance nv)
                   (- nv (n/byzantine-threshold nv)))))

(defspec byzantine-quorum-intersects 200
  ;; Two quorums share strictly more than f members, hence at least one honest
  ;; one. Machine-checked over Nat in ansatz as `quorum-intersection`; this is
  ;; the executable counterpart.
  (prop/for-all [nv (gen/choose 1 200)]
                (< (+ nv (n/byzantine-tolerance nv))
                   (* 2 (n/byzantine-threshold nv)))))
