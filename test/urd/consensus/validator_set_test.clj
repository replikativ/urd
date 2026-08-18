(ns urd.consensus.validator-set-test
  "A validator set that is empty or contains a duplicate is a config error, and
  both used to be accepted."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.node :as n]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.tendermint :as tm]
            [urd.consensus.algorithms.bullshark :as bs]
            [urd.consensus.algorithms.snowman :as snow]
            [urd.consensus.algorithms.round-robin :as rr]))

(deftest a-duplicate-validator-would-let-one-node-vote-twice
  (testing "quorum arithmetic counts POSITIONS, not identities

           Raft's `vote-result` on `[:a :a :b]` computes q=2 and then counts a
           single grant from `:a` twice, so `:a` elects itself leader alone
           against a rule that says it needs two of three. Every threshold in
           this library is `(count validators)` somewhere, so one duplicate
           under-counts every quorum at once."
    (is (= 2 (inc (quot (count [:a :a :b]) 2)))
        "the arithmetic that makes this fatal, stated plainly")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"duplicate validator"
                          (n/validator-set {:peer-id :a :validators [:a :a :b]})))
    (is (= [:a :b :c] (n/validator-set {:peer-id :a :validators [:c :a :b]}))
        "and a well-formed set still comes back sorted, as every algorithm
         needs it")))

(deftest an-empty-validator-set-is-refused-at-init-not-on-the-first-tick
  (testing "round-robin picks its proposer with `(mod height (count vs))` and
            divides by zero on the very first timer tick, killing the event
            loop before the node has done anything. The symptom is a validator
            that starts cleanly and is never heard from again."
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"non-empty :validators"
                          (n/validator-set {:peer-id :a :validators []})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"non-empty :validators"
                          (n/validator-set {:peer-id :a})))))

(deftest every-algorithm-refuses-both
  (testing "the check is shared, so it cannot be applied to four of five"
    (let [atts (rr/test-attestations)
          bad [{:peer-id :a :validators []}
               {:peer-id :a :validators [:a :a :b]}]]
      (doseq [cfg bad]
        (is (thrown? clojure.lang.ExceptionInfo (n/init (raft/make) cfg)))
        (is (thrown? clojure.lang.ExceptionInfo (n/init (snow/create) cfg)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (n/init (bs/create) (merge (bs/test-attestations) cfg))))
        (is (thrown? clojure.lang.ExceptionInfo (n/init (rr/create) (merge atts cfg))))
        (is (thrown? clojure.lang.ExceptionInfo (n/init (tm/make) cfg)))))))
