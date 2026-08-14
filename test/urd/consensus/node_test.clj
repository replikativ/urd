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
  (testing "with power supplied, a quorum is summed weight, not head count"
    (let [weighted (assoc four :voting-power {:a 3 :b 1 :c 1 :d 1})]
      (is (true? (n/quorum? n/bft-membership weighted [{:from :a}] (constantly true)))
          ":a alone holds 3 of 6 power, meeting the threshold of 3")
      (is (false? (n/quorum? n/bft-membership weighted [{:from :b}] (constantly true)))
          ":b alone holds 1"))))

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
