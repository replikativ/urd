(ns urd.consensus.reconfig-test
  "Config algebra only: no network, no log, no time.

  Shape borrowed from etcd's `confchange/datadriven_test.go`, which drives a
  bare `Changer` with config -> config commands and golden files enumerating
  every rejection message. That separation is why their diff-application logic
  has been stable since 2019 while the bugs kept appearing in the surrounding
  machinery -- the algebra is testable in isolation, so it got tested."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.reconfig :as rc]))

(def base {:validators [:a :b :c]
           :powers {:a 1 :b 1 :c 1}
           :priorities {:a 0 :b 0 :c 0}})

;; ============================================================
;; Order independence -- the safety property, not tidiness
;; ============================================================

(deftest updates-are-a-set-not-a-sequence
  (testing "CometBFT #3181, fixed by `cce4d21cc` as a CONSENSUS-BREAKING change:
            proposer selection depended on the ORDER of updates in the ABCI
            response, so two honest nodes given identical input computed
            different proposer priorities.

           That failure is silent. No message is lost, nothing is malformed,
           the input is byte-identical on both nodes, and they simply disagree
           about who proposes next. It is the single most important property in
           this namespace."
    (let [us [{:id :d :power 3} {:id :c :power 0} {:id :a :power 2}]]
      (is (apply = (map #(rc/apply-updates base %) (repeatedly 20 #(shuffle us))))
          "every permutation of the same updates gives the same config"))))

(defspec order-independence-holds-for-generated-updates 200
  (prop/for-all
   [us (gen/vector-distinct-by
        :id
        (gen/hash-map :id (gen/elements [:a :b :c :d :e])
                      :power (gen/choose 0 4))
        {:max-elements 5})]
   (let [results (map #(rc/apply-updates base %) (repeatedly 8 #(shuffle us)))]
     (apply = results))))

;; ============================================================
;; Every rejection, driven down its false arm
;; ============================================================

(deftest each-rejection-is-reachable-and-named
  (testing "a diff can be invalid in ways a whole-set replacement cannot, which
            is the price of using one. Each of these is a way the application
            and the consensus state can disagree about what the set IS, so each
            is named rather than being silently absorbed."

    (testing "negative or non-integer power"
      (is (= :negative-or-non-integer-power
             (:error (rc/apply-updates base [{:id :a :power -1}]))))
      (is (= :negative-or-non-integer-power
             (:error (rc/apply-updates base [{:id :a :power 1.5}]))))
      (is (= :negative-or-non-integer-power
             (:error (rc/apply-updates base [{:id :a :power nil}])))))

    (testing "removing a validator that is not in the set"
      (is (= :remove-unknown-validator
             (:error (rc/apply-updates base [{:id :zz :power 0}])))
          "a no-op would hide the fact that the two sides disagree about the set"))

    (testing "the same id twice"
      (is (= :duplicate-update
             (:error (rc/apply-updates base [{:id :a :power 2} {:id :a :power 3}])))
          "silently picking one is exactly how two nodes end up disagreeing"))

    (testing "emptying the set"
      (is (= :would-empty-the-validator-set
             (:error (rc/apply-updates base [{:id :a :power 0} {:id :b :power 0}
                                             {:id :c :power 0}])))))

    (testing "exceeding the total power ceiling"
      (is (= :total-power-exceeded
             (:error (rc/apply-updates base [{:id :a :power rc/max-total-power}
                                             {:id :b :power rc/max-total-power}])))
          "the ceiling is arithmetic headroom for the priority accumulator, not
           a BFT bound -- see the namespace docstring"))

    (testing "and a valid update is NOT rejected"
      (is (nil? (:error (rc/apply-updates base [{:id :d :power 1}])))
          "or every assertion above passes while the mechanism refuses
           everything, which is the failure mode a rejection test invites"))))

;; ============================================================
;; Priorities across a change
;; ============================================================

(deftest a-joining-validator-cannot-propose-immediately
  (testing "CometBFT `validator_set.go:543-550`. Without the penalty a fresh
            validator proposes at once; worse, a validator could unbond and
            rebond to clear a negative priority -- their issue #2785."
    (let [after (rc/apply-updates base [{:id :d :power 1}])
          total (reduce + 0 (vals (:powers after)))]
      (is (= 4 total))
      (is (neg? (get-in after [:priorities :d])) "the newcomer starts behind")
      (is (= (- (+ total (bit-shift-right total 3)))
             (get-in after [:priorities :d]))
          "-(P + P>>3) over the RESULTING total, not the previous one")
      (is (= {:a 0 :b 0 :c 0} (dissoc (:priorities after) :d))
          "and nobody else's priority is disturbed by the arrival"))))

(deftest a-leaving-validator-does-not-bank-its-priority
  (testing "keeping it would let a validator accumulate priority while absent
            and propose immediately on return -- the same attack the joining
            penalty closes, approached from the other side."
    (let [cfg (assoc base :priorities {:a 5 :b -2 :c -3})
          after (rc/apply-updates cfg [{:id :c :power 0}])]
      (is (= [:a :b] (:validators after)))
      (is (= {:a 5 :b -2} (:priorities after)) "c's priority is gone, not parked")
      (is (not (contains? (:priorities after) :c))))))

(deftest priorities-are-optional
  (testing "an algorithm with no proposer rotation -- round-robin picks by
            height alone -- should not have to carry a priority map to change
            its validator set."
    (let [after (rc/apply-updates (dissoc base :priorities) [{:id :d :power 1}])]
      (is (= [:a :b :c :d] (:validators after)))
      (is (not (contains? after :priorities))))))

;; ============================================================
;; Batching is not the same as applying one at a time
;; ============================================================

(deftest a-batch-is-not-equivalent-to-sequential-application
  (testing "etcd asserts the OPPOSITE for its own model -- `TestConfChangeQuick`
            requires that N simple changes reach the same Config as
            EnterJoint+LeaveJoint. That holds there because etcd's config
            carries no priority state.

           Here it does NOT hold, and the reason is worth pinning: the joining
           penalty is computed from the RESULTING total power, so adding two
           validators in one batch gives both the same penalty, while adding
           them one at a time gives the second a larger one. Neither is wrong;
           they are different histories.

           The consequence is a rule for callers: apply a set change as ONE
           batch on every node. Splitting it locally would silently produce a
           different priority state and therefore a different proposer
           schedule -- the same class of divergence as CometBFT #3181, reached
           by a different route."
    (let [batch (rc/apply-updates base [{:id :d :power 1} {:id :e :power 1}])
          seq' (-> base
                   (rc/apply-updates [{:id :d :power 1}])
                   (rc/apply-updates [{:id :e :power 1}]))]
      (is (= (:validators batch) (:validators seq')) "same membership")
      (is (= (:powers batch) (:powers seq')) "same powers")
      (is (not= (:priorities batch) (:priorities seq'))
          (str "but NOT the same priorities: " (:priorities batch)
               " vs " (:priorities seq')))
      (is (= (get-in batch [:priorities :d]) (get-in batch [:priorities :e]))
          "batched, both newcomers are penalised against the same total"))))

;; ============================================================
;; No-ops
;; ============================================================

(deftest an-update-that-changes-nothing-is-reported-as-such
  (testing "setting a validator to the power it already has is legal and is a
            no-op. An algorithm should not pay for a transition for one --
            and under Raft, where at most one change may be in flight, a
            no-op transition would occupy that slot for nothing."
    (is (false? (rc/changed? base [{:id :a :power 1}])))
    (is (false? (rc/changed? base [])))
    (is (true? (rc/changed? base [{:id :a :power 2}])))
    (is (true? (rc/changed? base [{:id :d :power 1}])))
    (is (true? (rc/changed? base [{:id :c :power 0}])))
    (is (false? (rc/changed? base [{:id :zz :power 0}]))
        "an invalid update changed nothing, whatever else is true of it")))

;; ============================================================
;; Determinism of the resulting order
;; ============================================================

(deftest the-resulting-validator-order-is-canonical
  (testing "every algorithm here sorts its validator list for determinism --
            `node/validator-set` does it at init, and round-robin picks its
            proposer by `(mod height (count vs))` over the sorted order. A
            reconfiguration that returned a differently-ordered list would
            change who proposes without changing WHO is a validator."
    (let [after (rc/apply-updates base [{:id :aa :power 1} {:id :d :power 1}])]
      (is (= (sort-by str (:validators after)) (:validators after)))
      (is (= [:a :aa :b :c :d] (:validators after))))))
