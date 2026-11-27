(ns urd.consensus.node-test
  "Tests for the core protocol's membership abstraction.

  Both bugs pinned here were live in shipped code and were found by
  implementing algorithms against the protocol, not by review."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.tendermint :as tm]
            [urd.consensus.algorithms.scp :as scp]
            [urd.consensus.algorithms.bullshark :as bs]
            [urd.consensus.algorithms.snowman :as sm]
            [urd.consensus.algorithms.nakamoto :as nk]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.trace :as trace]))

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
  ;; one. Machine-checked over Nat by `clj -M:proofs`; this is
  ;; the executable counterpart.
  (prop/for-all [nv (gen/choose 1 200)]
                (< (+ nv (n/byzantine-tolerance nv))
                   (* 2 (n/byzantine-threshold nv)))))

;; ============================================================
;; Capability declaration
;; ============================================================

(deftest a-node-must-declare-what-it-emits
  (testing "not optional, and validated at registration -- a declaration that
            nothing checks is a comment"
    (is (thrown? Exception
                 (n/check-capabilities
                  (reify n/Node
                    (init [_ _] (n/result {}))
                    (step [_ st _] (n/result st))
                    (capabilities [_] {}))))
        "an empty declaration has no :emits set")
    (is (thrown? Exception
                 (n/check-capabilities
                  (reify n/Node
                    (init [_ _] (n/result {}))
                    (step [_ st _] (n/result st))
                    (capabilities [_] {:emits #{:commit :brodcast}}))))
        "a typo names an effect the protocol does not define, and must not
         silently narrow what the node may do")
    (is (= #{:commit :log}
           (n/check-capabilities
            (reify n/Node
              (init [_ _] (n/result {}))
              (step [_ st _] (n/result st))
              (capabilities [_] {:emits #{:commit :log}})))))))

(deftest an-undeclared-effect-is-refused-by-the-interpreter
  (testing "the guard, watched failing. A node that declares only `:log` and
            then commits is stopped, because otherwise the declaration would
            never be checked on a live run."
    (let [liar (reify n/Node
                 (init [_ _] (n/result {:n 0}))
                 (step [_ st _] (n/result st [(n/commit [:v])]))
                 (capabilities [_] {:emits #{:log :set-timer}}))]
      (is (thrown-with-msg?
           Exception #"did not declare"
           (-> (sim/make {:seed 1 :nodes {:a liar}})
               (sim/inject :a (n/timer-fired :x))
               (sim/run 2)))))))

(deftest every-shipped-algorithm-declares-honestly
  (testing "the declarations are checked against `all-effects`, but nothing
            checks that an algorithm declares MORE than it uses. This pins the
            one distinction the vocabulary exists to make: exactly one of the
            six may revoke a decision."
    (let [emits (fn [impl] (:emits (n/capabilities impl)))]
      (is (= #{:revert} (into #{} (filter #{:revert}) (emits (nk/create))))
          "Nakamoto revokes")
      (doseq [[nm impl] [["raft" (raft/make)] ["tendermint" (tm/make)]
                         ["scp" (scp/make)] ["bullshark" (bs/create)]
                         ["snowman" (sm/create)]]]
        (is (not (contains? (emits impl) :revert))
            (str nm " must not declare :revert -- it never revokes")))
      (is (contains? (emits (sm/create)) :sample) "only Snowman samples")
      (is (contains? (emits (sm/create)) :persist-then)
          "Snowman persists its accepted frontier"))))

;; ============================================================
;; Tracing
;; ============================================================

(deftest a-traced-node-behaves-identically-and-records-what-happened
  (testing "the wrapper is transparent to the algorithm and to the interpreter,
            which is what lets it be turned on anywhere without changing a
            result. avalanchego wraps its Consensus the same way."
    (let [plain (rr/create)
          traced (trace/tracing (rr/create))
          run (fn [impl]
                (sim/run (sim/make {:seed 5
                                    :nodes {:a impl :b (rr/create) :c (rr/create)}
                                    :node-config (zipmap [:a :b :c]
                                                         (repeat (rr/test-attestations)))
                                    :config {:value-fn (fn [_ p ctx]
                                                         {:snapshot-id [p (:height ctx)]})}})
                         60))]
      (is (= (sim/all-committed (run plain)) (sim/all-committed (run traced)))
          "identical committed sequences with and without the trace")
      (let [{:keys [n in out]} (trace/summary traced)]
        (is (pos? n))
        (is (pos? (get in :message-received 0)) "it saw messages")
        (is (pos? (get out :commit 0)) "and it committed")))))

(deftest the-trace-distinguishes-silence-from-inaction
  (testing "the question state inspection cannot answer.

            A node that has received nothing and a node that receives and does
            not act look identical from the outside -- both sit at height 0 --
            and telling them apart is the first thing any network diagnosis
            needs. An empty `:in` says which."
    (let [isolated (trace/tracing (rr/create))
          s (-> (sim/make {:seed 1 :nodes {:a isolated :b (rr/create) :c (rr/create)}
                           :node-config (zipmap [:a :b :c]
                                                (repeat (rr/test-attestations)))})
                (sim/partition-network [#{:a} #{:b :c}])
                (sim/run 60))
          {:keys [in]} (trace/summary isolated)]
      (is (zero? (get in :message-received 0))
          "an isolated node receives nothing, and the trace says so plainly")
      (is (pos? (get in :timer-fired 0))
          "while still firing its own timers, so it is running -- which is
           exactly the distinction that matters"))))

(deftest a-tracing-wrapper-reports-what-it-wraps
  (is (= (n/capabilities (rr/create))
         (n/capabilities (trace/tracing (rr/create))))))

(deftest weight-and-total-weight-use-the-same-default
  (testing "two quantities that must be measured the same way

           `total-weight` defaults a validator missing from `:voting-power` to
           0; `weight` defaulted it to 1. With a partial power map an unlisted
           validator therefore contributed nothing to the denominator and a
           full unit to the numerator: the quorum bar dropped while its vote
           still counted, in the direction that reaches a quorum too easily.

           This is the same shape as the bug `total-weight`'s own docstring was
           written about -- summed stake on one side, head count on the other --
           and it survived in the same file, twelve lines below the warning.

           The default has to be CONDITIONAL. With no power map both sides fall
           back to head count, so 1 is right there and 0 is right here; a single
           constant is wrong in one regime or the other."
    (let [m (n/->ThresholdMembership n/byzantine-threshold :from)
          partial-powers {:validators [:a :b :c :d] :voting-power {:a 10 :b 10}}
          uniform {:validators [:a :b :c :d]}]
      (is (= 0 (n/weight m partial-powers :c))
          "a validator absent from a declared power map has no power")
      (is (= 10 (n/weight m partial-powers :a)))
      (is (= 1 (n/weight m uniform :c))
          "while with no power map at all, everyone counts one")
      (is (false? (n/quorum? m partial-powers [{:from :c} {:from :d}] (constantly true)))
          "so two undeclared validators cannot manufacture a quorum against a
           denominator that does not include them")
      (is (true? (n/quorum? m uniform [{:from :a} {:from :b} {:from :c}]
                            (constantly true)))
          "and the uniform path still works, which is what every algorithm
           here actually runs"))))
