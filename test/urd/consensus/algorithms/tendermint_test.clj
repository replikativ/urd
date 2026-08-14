(ns urd.consensus.algorithms.tendermint-test
  "Tendermint: pure-function units, the individual upon-rules, and the
  simulator under crash faults.

  Byzantine behaviour lives in `tendermint-byzantine-test`; this namespace is
  about getting the paper's arithmetic and its four notorious rule conditions
  exactly right, because every one of them is a place a plausible-looking
  implementation is silently wrong.

  Private rule functions are reached through vars on purpose. Driving a single
  `upon` rule end-to-end through the simulator would take a hundred ticks of
  setup and would not pin the condition being tested; poking the rule with a
  hand-built state does."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as node]
            [urd.consensus.sim :as sim]
            [urd.consensus.proposer :as proposer]
            [urd.consensus.signing :as signing]
            [urd.consensus.algorithms.tendermint :as tm]))

;; ============================================================
;; Quorum arithmetic
;;
;; CometBFT writes "more than two thirds" three syntactically different ways.
;; Before trusting any of them, prove they are the same function.
;; ============================================================

(defspec the-three-cometbft-quorum-encodings-agree 300
  (testing "vote_set.go:308 `sum >= T*2/3+1`, vote_set.go:459 `sum > T*2/3`,
            and validation.go:40 `sum > votingPowerNeeded` are one predicate --
            and it is `byzantine-threshold`"
    (prop/for-all [total (gen/choose 1 400)
                   k (gen/choose 0 400)]
                  (let [e1 (>= k (+ (quot (* total 2) 3) 1)) ; vote_set.go:308
                        e2 (> k (quot (* total 2) 3))        ; vote_set.go:459
                        e3 (> k (quot (* total 2) 3))        ; validation.go:40
                        e4 (> (* 3 k) (* 2 total))           ; the rational form
                        ours (>= k (node/byzantine-threshold total))]
                    (= e1 e2 e3 e4 ours)))))

(defspec v-blocking-is-exactly-f-plus-one 300
  (testing "L55's round-skip trigger is `f+1`, and the `Membership` protocol
            already has that predicate: the dual of a quorum. So the paper's
            two thresholds are one abstraction, not two constants."
    (prop/for-all [total (gen/choose 1 400)]
                  (= (inc (- total (node/byzantine-threshold total)))
                     (inc (node/byzantine-tolerance total))))))

(deftest quorums-are-over-power-not-headcount
  (testing "one validator with 10 of 12 power is a quorum on its own; a
            headcount says it is one of four"
    (let [state {:powers {:a 10 :b 1 :c 1 :d 1}}
          stmts [{:from :a}]]
      (is (node/quorum? tm/power-weighted-bft state stmts (constantly true)))
      (is (not (node/quorum? tm/power-weighted-bft state [{:from :b} {:from :c}]
                             (constantly true)))))))

(deftest a-repeated-sender-is-not-a-quorum
  (testing "the same validator shouting three times must not clear a
            four-validator quorum. `ThresholdMembership` counts STATEMENTS and
            would say yes here; summing weight over distinct senders says no."
    (let [state {:powers {:a 1 :b 1 :c 1 :d 1}}
          spam [{:from :a} {:from :a} {:from :a}]]
      (is (not (node/quorum? tm/power-weighted-bft state spam (constantly true))))
      (is (node/quorum? tm/power-weighted-bft state
                        [{:from :a} {:from :b} {:from :c}]
                        (constantly true))))))

(deftest three-validators-tolerate-no-byzantine-fault
  (is (= 0 (tm/fault-tolerance 3)))
  (is (= 1 (tm/fault-tolerance 4)))
  (is (= 2 (tm/fault-tolerance 7))))

;; ============================================================
;; The double-sign guard
;; ============================================================

(deftest may-sign-rejects-a-repeat
  (testing "the theorem `no-double-sign` from proofs/may_sign.clj, exercised
            through the shipped predicate"
    (let [last {:height 3 :round 2 :step :prevote}]
      (is (not (signing/may-sign? last last)))
      (is (not (signing/may-sign? {:height 3 :round 2 :step :propose} last)))
      (is (signing/may-sign? {:height 3 :round 2 :step :precommit} last))
      (is (signing/may-sign? {:height 3 :round 3 :step :propose} last))
      (is (signing/may-sign? {:height 4 :round 0 :step :propose} last))
      (is (not (signing/may-sign? {:height 2 :round 9 :step :precommit} last))))))

(deftest a-fresh-validator-may-sign-at-height-zero
  (is (signing/may-sign? {:height 0 :round 0 :step :propose} nil)))

(deftest unknown-signing-steps-throw-rather-than-rank-zero
  (is (thrown? clojure.lang.ExceptionInfo (signing/rank :commit))))

(deftest the-wal-barrier-refuses-to-guess
  (testing "state.go:881-905 has a `default: panic` so a new self-message type
            cannot silently skip the fsync. Copying the panic is the point."
    (is (= :prevote (tm/signed-message-step {:type :prevote})))
    (is (nil? (tm/signed-message-step {:type :end-height})))
    (is (thrown? clojure.lang.ExceptionInfo
                 (tm/signed-message-step {:type :block-part})))))

;; ============================================================
;; Weighted proposer selection
;; ============================================================

(def uniform {:a 1 :b 1 :c 1 :d 1})

(deftest uniform-power-is-round-robin-in-id-order
  (let [p0 (proposer/initial-priorities [:a :b :c :d])]
    (is (= [:a :b :c :d :a :b]
           (mapv #(proposer/proposer-for p0 uniform %) (range 6))))))

(deftest the-height-advance-rotates-the-base
  (let [p0 (proposer/initial-priorities [:a :b :c :d])
        p1 (proposer/advance p0 uniform)]
    (is (= :a (proposer/proposer-for p0 uniform 0)))
    (is (= :b (proposer/proposer-for p1 uniform 0)))))

(deftest selection-is-proportional-to-voting-power
  (let [powers {:a 4 :b 2 :c 1 :d 1}
        p0 (proposer/initial-priorities [:a :b :c :d])
        freq (frequencies (map #(proposer/proposer-for p0 powers %) (range 80)))]
    (is (= 40 (:a freq)) "half the power, half the rounds")
    (is (= 20 (:b freq)))
    (is (= 10 (:c freq)))
    (is (= 10 (:d freq)))))

(deftest centering-floors-rather-than-truncating
  (testing "CometBFT centers with big.Int.Div, which is Euclidean. `quot` would
            truncate toward zero and diverge on the negative sums that the
            demote-the-winner step makes the normal case."
    ;; sum = -1 over 4 validators. Euclidean mean is -1, so everything shifts
    ;; up by one; a truncating mean would be 0 and leave the map untouched.
    (let [in {:a 0 :b -1 :c 0 :d 0}]
      (is (= {:a 1 :b 0 :c 1 :d 1} (proposer/center in)))
      (is (not= in (proposer/center in))
          "with `quot` this would be a no-op and the priorities would drift"))))

(deftest rescaling-bounds-the-priority-window
  (let [wide {:a 1000 :b 0 :c 0 :d 0}]
    ;; ratio = ceil(1000/8) = 125, so the window closes to exactly diff-max.
    (is (= {:a 8 :b 0 :c 0 :d 0} (proposer/rescale wide 8)))
    (is (= wide (proposer/rescale wide 100000)) "no rescale when already inside")))

(deftest a-new-validators-penalty-truncates-away-below-power-eight
  (testing "validator_set.go:550 documents -1.125*P but computes
            -(P + P>>3) in integers, so for P < 8 the 0.125 is simply gone"
    (is (= -7 (proposer/new-validator-priority 7)) "penalty lost entirely")
    (is (= -9 (proposer/new-validator-priority 8)))
    (is (= -18 (proposer/new-validator-priority 16)))))

(deftest ties-break-on-validator-id-ascending
  (is (= :a (proposer/proposer-for {:a 0 :b 0} {:a 1 :b 1} 0))))

;; ============================================================
;; The upon-rules, one at a time
;; ============================================================

(def validators [:a :b :c :d])

(defn- st0
  "A node state with `:fx` re-armed, so a rule's emissions are observable."
  [& {:as over}]
  (merge (:state (node/init (tm/make) {:peer-id :a :validators validators}))
         {:fx {:msgs [] :logs [] :signed []}}
         over))

(defn- signed [st] (mapv :msg (get-in st [:fx :signed])))
(defn- effects [st] (get-in st [:fx :msgs]))
(defn- logs [st] (get-in st [:fx :logs]))

(defn- pv [from r vid] {:type :prevote :from from :height 0 :round r :value-id vid})
(defn- pc [from r vid] {:type :precommit :from from :height 0 :round r :value-id vid})
(defn- pp [from r v vr] {:type :proposal :from from :height 0 :round r :value v :vr vr})

(defn- with-votes [st bucket r msgs]
  (assoc-in st [bucket r] (into {} (map (juxt :from identity)) msgs)))

(deftest proposer-schedule-for-the-test-fixture
  (is (= [:a :b :c :d] (mapv #(#'tm/proposer-at (st0) %) (range 4)))))

;; ---------- L22 ----------

(deftest l22-prevotes-the-proposal-when-unlocked
  (let [v {:id :x}
        st (-> (st0 :round 0 :step :propose)
               (assoc-in [:proposals 0 :a] (pp :a 0 v -1)))
        st' (#'tm/rule-l22 st)]
    (is (= [:x] (map :value-id (signed st'))))
    (is (= :prevote (:step st')))))

(deftest l22-prevotes-nil-when-locked-on-something-else
  (let [v {:id :x}
        st (-> (st0 :round 0 :step :propose :locked-round 0 :locked-value-id :other)
               (assoc-in [:proposals 0 :a] (pp :a 0 v -1)))
        st' (#'tm/rule-l22 st)]
    (is (= [nil] (map :value-id (signed st'))))))

(deftest l22-ignores-a-proposal-from-a-non-proposer
  (let [st (-> (st0 :round 0 :step :propose)
               (assoc-in [:proposals 0 :b] (pp :b 0 {:id :x} -1)))]
    (is (nil? (#'tm/rule-l22 st)) "only the round's proposer proposes")))

(deftest l22-does-not-fire-for-a-proposal-carrying-a-valid-round
  (let [st (-> (st0 :round 1 :step :propose)
               (assoc-in [:proposals 1 :b] (pp :b 1 {:id :x} 0)))]
    (is (nil? (#'tm/rule-l22 st)) "vr >= 0 is L28's business, not L22's")))

;; ---------- L28: the two traps ----------

(deftest l28-unlocks-when-locked-round-EQUALS-vr
  (testing "the condition is `lockedRound <= vr`, not `<`. With `<` a node
            locked at exactly vr prevotes nil for the very value it is locked
            on, and the rule that exists to restore liveness destroys it."
    (let [v {:id :y}
          st (-> (st0 :round 3 :step :propose :locked-round 1 :locked-value-id :x)
                 (assoc-in [:proposals 3 :d] (pp :d 3 v 1))
                 (with-votes :prevotes 1 [(pv :b 1 :y) (pv :c 1 :y) (pv :d 1 :y)]))
          st' (#'tm/rule-l28 st)]
      (is (some? st') "the rule must fire")
      (is (= [:y] (map :value-id (signed st')))
          "locked-round 1 <= vr 1, so we release the lock and prevote y")
      (is (= :prevote (:step st'))))))

(deftest l28-keeps-the-lock-when-locked-round-exceeds-vr
  (let [v {:id :y}
        st (-> (st0 :round 3 :step :propose :locked-round 2 :locked-value-id :x)
               (assoc-in [:proposals 3 :d] (pp :d 3 v 1))
               (with-votes :prevotes 1 [(pv :b 1 :y) (pv :c 1 :y) (pv :d 1 :y)]))
        st' (#'tm/rule-l28 st)]
    (is (= [nil] (map :value-id (signed st')))
        "locked at 2 > vr 1 on a different value: prevote nil")))

(deftest l28-needs-the-quorum-at-vr-not-at-the-current-round
  (testing "the second trap: `2f+1 Prevote(h, vr, id(v))` -- the prevotes are
            at the proposal's valid-round, not at round_p"
    (let [v {:id :y}
          base (-> (st0 :round 3 :step :propose)
                   (assoc-in [:proposals 3 :d] (pp :d 3 v 1)))]
      (is (nil? (#'tm/rule-l28
                 (with-votes base :prevotes 3 [(pv :b 3 :y) (pv :c 3 :y) (pv :d 3 :y)])))
          "a quorum at the CURRENT round does not satisfy L28")
      (is (some? (#'tm/rule-l28
                  (with-votes base :prevotes 1 [(pv :b 1 :y) (pv :c 1 :y) (pv :d 1 :y)])))
          "a quorum at vr does"))))

(deftest l28-requires-vr-strictly-below-the-current-round
  (let [v {:id :y}
        st (-> (st0 :round 1 :step :propose)
               (assoc-in [:proposals 1 :b] (pp :b 1 v 1))
               (with-votes :prevotes 1 [(pv :b 1 :y) (pv :c 1 :y) (pv :d 1 :y)]))]
    (is (nil? (#'tm/rule-l28 st)) "vr < round_p is required")))

;; ---------- L36: the two traps ----------

(deftest l36-in-precommit-updates-only-the-valid-value
  (testing "the guard is `step >= prevote`, so the rule fires in precommit too
            -- and then it must NOT re-lock or re-precommit"
    (let [v {:id :x}
          st (-> (st0 :round 2 :step :precommit
                      :locked-round 0 :locked-value-id :old)
                 (assoc-in [:proposals 2 :c] (pp :c 2 v -1))
                 (with-votes :prevotes 2 [(pv :b 2 :x) (pv :c 2 :x) (pv :d 2 :x)]))
          st' (#'tm/rule-l36 st)]
      (is (some? st'))
      (is (empty? (signed st')) "no second precommit")
      (is (= [:old 0] (tm/locked st')) "the lock is untouched")
      (is (= [:x 2] (tm/valid-pair st'))))))

(deftest l36-in-prevote-locks-and-precommits
  (let [v {:id :x}
        st (-> (st0 :round 2 :step :prevote)
               (assoc-in [:proposals 2 :c] (pp :c 2 v -1))
               (with-votes :prevotes 2 [(pv :b 2 :x) (pv :c 2 :x) (pv :d 2 :x)]))
        st' (#'tm/rule-l36 st)]
    (is (= [:x] (map :value-id (signed st'))))
    (is (= :precommit (:step st')))
    (is (= [:x 2] (tm/locked st')))
    (is (= [:x 2] (tm/valid-pair st')))))

(deftest l36-sets-valid-round-to-the-current-round-not-the-proposals-vr
  (testing "L43 is `validRound := round_p`. Using the proposal's vr instead
            would make the node re-propose with a stale valid-round and stall
            the very termination argument validValue exists for."
    (let [v {:id :x}
          st (-> (st0 :round 4 :step :prevote)
                 (assoc-in [:proposals 4 :a] (pp :a 4 v 1))
                 (with-votes :prevotes 4 [(pv :b 4 :x) (pv :c 4 :x) (pv :d 4 :x)]))
          st' (#'tm/rule-l36 st)]
      (is (= [:x 4] (tm/valid-pair st')) "4, the current round -- not 1"))))

(deftest l36-fires-once-per-round-and-value
  (let [v {:id :x}
        st (-> (st0 :round 2 :step :precommit)
               (assoc-in [:proposals 2 :c] (pp :c 2 v -1))
               (with-votes :prevotes 2 [(pv :b 2 :x) (pv :c 2 :x) (pv :d 2 :x)]))
        st' (#'tm/rule-l36 st)]
    (is (contains? (:done-l36 st') [2 :x]))
    (is (nil? (#'tm/rule-l36 st')) "the latch stops the second firing")))

;; ---------- L34, L44, L47 ----------

(deftest l34-arms-the-prevote-timer-once
  (let [st (-> (st0 :round 0 :step :prevote)
               (with-votes :prevotes 0 [(pv :b 0 :x) (pv :c 0 nil) (pv :d 0 :y)]))
        st' (#'tm/rule-l34 st)]
    (is (= [[:set-timer {:timer-id [:prevote 0 0] :after-ticks 8}]] (effects st'))
        "2f+1 for *anything*, mixed values included")
    (is (nil? (#'tm/rule-l34 st')))))

(deftest l44-precommits-nil-on-a-nil-polka
  (let [st (-> (st0 :round 0 :step :prevote)
               (with-votes :prevotes 0 [(pv :b 0 nil) (pv :c 0 nil) (pv :d 0 nil)]))
        st' (#'tm/rule-l44 st)]
    (is (= [nil] (map :value-id (signed st'))))
    (is (= :precommit (:step st')))))

(deftest l47-has-no-step-guard
  (testing "the paper attaches no `with step_p = ...` to L47, so it must arm
            the precommit timer even while still in propose"
    (doseq [step [:propose :prevote :precommit]]
      (let [st (-> (st0 :round 1 :step step)
                   (with-votes :precommits 1 [(pc :b 1 :x) (pc :c 1 nil) (pc :d 1 :y)]))
            st' (#'tm/rule-l47 st)]
        (is (some? st') (str "L47 must fire in step " step))
        (is (= [[:set-timer {:timer-id [:precommit 0 1] :after-ticks 10}]]
               (effects st')))))))

;; ---------- L49 ----------

(deftest l49-decides-on-any-round-not-only-the-current-one
  (testing "a node dragged forward to round 4 must still decide on the quorum
            that formed back at round 1"
    (let [v {:id :x}
          st (-> (st0 :round 4 :step :propose)
                 (assoc-in [:proposals 1 :b] (pp :b 1 v -1))
                 (with-votes :precommits 1 [(pc :b 1 :x) (pc :c 1 :x) (pc :d 1 :x)]))
          st' (#'tm/rule-l49 st)]
      (is (= v (tm/decided st' 0)))
      (is (= 1 (count (get-in st' [:fx :signed]))) "one end-height marker")
      (is (= :end-height (:type (first (signed st'))))))))

(deftest l49-needs-the-proposal-too-not-just-the-precommits
  (let [st (-> (st0 :round 1 :step :propose)
               (with-votes :precommits 1 [(pc :b 1 :x) (pc :c 1 :x) (pc :d 1 :x)]))]
    (is (nil? (#'tm/rule-l49 st))
        "precommits carry only id(v); without the proposal the node does not
         know the value it would be committing")))

(deftest l49-does-not-decide-on-a-nil-quorum
  (let [st (-> (st0 :round 1 :step :propose)
               (assoc-in [:proposals 1 :b] (pp :b 1 {:id :x} -1))
               (with-votes :precommits 1 [(pc :b 1 nil) (pc :c 1 nil) (pc :d 1 nil)]))]
    (is (nil? (#'tm/rule-l49 st)))))

;; ---------- L55 ----------

(deftest l55-skips-on-f-plus-one-not-two-f-plus-one
  (testing "the paper uses f+1 (state.go:2362 uses 2f+1; we follow the paper).
            With n=4, f=1, so two distinct senders at a higher round suffice."
    (let [st (-> (st0 :round 0 :step :prevote)
                 (with-votes :prevotes 3 [(pv :b 3 :x) (pv :c 3 :x)]))
          st' (#'tm/rule-l55 st)]
      (is (= 3 (:round st')))
      (is (= :propose (:step st'))))))

(deftest l55-does-not-skip-on-a-single-sender
  (let [st (-> (st0 :round 0 :step :prevote)
               (with-votes :prevotes 3 [(pv :b 3 :x)]))]
    (is (nil? (#'tm/rule-l55 st))
        "one message could be a lone Byzantine validator; f+1 guarantees an
         honest node is really there")))

(deftest l55-counts-senders-across-message-types
  (let [st (-> (st0 :round 0 :step :prevote)
               (with-votes :prevotes 2 [(pv :b 2 :x)])
               (with-votes :precommits 2 [(pc :c 2 :x)]))]
    (is (= 2 (:round (#'tm/rule-l55 st)))
        "the paper's rule is over <*,h,round,*,*> -- any message type")))

(deftest l55-jumps-to-the-highest-qualifying-round
  (let [st (-> (st0 :round 0 :step :prevote)
               (with-votes :prevotes 2 [(pv :b 2 :x) (pv :c 2 :x)])
               (with-votes :prevotes 5 [(pv :b 5 :x) (pv :c 5 :x)]))]
    (is (= 5 (:round (#'tm/rule-l55 st))))))

;; ---------- timeouts ----------

(deftest timeouts-grow-linearly-with-the-round
  (let [st (st0)]
    (is (= [10 12 14 16] (mapv #(#'tm/timeout-for st :propose %) (range 4))))
    (is (= [8 10 12] (mapv #(#'tm/timeout-for st :prevote %) (range 3))))))

(deftest a-timer-from-an-abandoned-round-is-a-no-op
  (let [st (st0 :round 3 :step :propose)]
    (is (= :propose (:step (#'tm/handle-timer st [:propose 0 1])))
        "round 1's propose timeout must not prevote at round 3")
    (is (= :prevote (:step (#'tm/handle-timer st [:propose 0 3]))))))

(deftest the-precommit-timeout-has-no-step-guard
  (testing "OnTimeoutPrecommit checks only (height, round) -- it starts the
            next round whatever step we are in"
    (doseq [step [:propose :prevote :precommit]]
      (let [st (#'tm/handle-timer (st0 :round 2 :step step) [:precommit 0 2])]
        (is (= 3 (:round st)))))))

;; ============================================================
;; Equivocation detection is an OUTPUT
;; ============================================================

(deftest a-conflicting-vote-becomes-evidence
  (let [st (-> (st0)
               (#'tm/record-message (pv :b 0 :x))
               (#'tm/record-message (pv :b 0 :y)))
        [kind params] (first (effects st))]
    (is (= :report-equivocation kind))
    (is (= :b (:peer params)))
    (is (= [:x :y] (map :value-id (:conflicting (:evidence params)))))
    (is (= :x (get-in st [:prevotes 0 :b :value-id]))
        "the first statement stands and is what counts toward quorums")))

(deftest a-duplicate-vote-with-different-signature-bytes-is-not-equivocation
  (testing "(vote -> signature) is not a function: CometBFT carries
            ErrVoteNonDeterministicSignature for exactly this. Inferring vote
            inequality from signature inequality would slash honest validators
            that use a remote signer."
    (let [st (-> (st0)
                 (#'tm/record-message (assoc (pv :b 0 :x) :signature "sig-1"))
                 (#'tm/record-message (assoc (pv :b 0 :x) :signature "sig-2")))]
      (is (empty? (effects st)))
      (is (= "sig-1" (get-in st [:prevotes 0 :b :signature]))))))

(deftest equivocation-is-reported-once-per-sender-round-and-kind
  (let [st (reduce #'tm/record-message (st0)
                   [(pv :b 0 :x) (pv :b 0 :y) (pv :b 0 :z)])]
    (is (= 1 (count (effects st))))))

(deftest two-proposals-for-one-round-are-equivocation
  (let [st (-> (st0)
               (#'tm/record-message (pp :a 0 {:id :x} -1))
               (#'tm/record-message (pp :a 0 {:id :y} -1)))
        [kind params] (first (effects st))]
    (is (= :report-equivocation kind))
    (is (= :proposal (:kind (:evidence params))))))

;; ============================================================
;; The crypto boundary
;; ============================================================

(deftest an-unverified-author-is-dropped
  (testing "a Byzantine node may lie in its own name but may not forge another
            validator's identity (tendermint.ivy:379-383). The state machine
            never sees an unverified signature, so this is the only place the
            check can live."
    (let [st (#'tm/ingest (st0) :b (pv :c 0 :x) #{:b})]
      (is (empty? (get-in st [:prevotes 0])))
      (is (= [:warn] (map #(:level (second %)) (logs st)))))
    (let [st (#'tm/ingest (st0) :b (pv :b 0 :x) #{:b})]
      (is (= 1 (count (get-in st [:prevotes 0])))))))

(deftest a-non-validator-is-dropped
  (let [st (#'tm/ingest (st0) :z (pv :z 0 :x) #{:z})]
    (is (empty? (get-in st [:prevotes 0])))))

;; ============================================================
;; The simulator: liveness and safety under crash faults
;; ============================================================

(def peers [:a :b :c :d])

(defn value-fn [_ peer ctx]
  {:id [:blk peer (:height ctx) (:round ctx)]})

(def node-cfg {:timeout-propose 20 :timeout-prevote 15
               :timeout-precommit 15 :timeout-delta 5})

(defn fresh
  ([] (fresh {} {}))
  ([sim-cfg] (fresh sim-cfg {}))
  ([sim-cfg extra-node-cfg]
   (sim/make {:seed 7
              :nodes (zipmap peers (repeat (tm/make)))
              :node-config (zipmap peers (repeat (merge node-cfg extra-node-cfg)))
              :config (merge {:value-fn value-fn} sim-cfg)})))

(defn- heights [s] (mapv #(:height (sim/node-state s %)) peers))

(deftest a-quiet-network-decides-a-block-per-round-zero
  (let [s (sim/run (fresh) 60)]
    (is (sim/agreement? s))
    (is (every? #(>= % 4) (heights s)) "several heights inside 60 ticks")
    (is (every? zero? (mapv #(:round (sim/node-state s %)) peers))
        "no round changes at all when nothing is faulty")
    (is (apply = (vals (sim/all-committed s))) "identical decision sequences")))

(deftest the-proposer-rotates-by-height
  (let [s (sim/run (fresh) 45)
        decided (sim/committed s :a)]
    (is (= [:a :b :c :d] (mapv #(second (:id %)) (take 4 decided)))
        "each height's value came from that height's round-0 proposer")))

(deftest a-decision-is-never-observed-before-its-write-is-durable
  (testing "the end-height marker is CometBFT's one unsigned WAL barrier; the
            `commit` effect rides in its `:then`"
    (let [s (sim/run (fresh) 30)]
      (doseq [p peers]
        (let [landed (get-in s [:storage p :landed])
              markers (filter #(= :end-height (get-in % [:writes :wal :type])) landed)]
          (is (= (count (sim/committed s p)) (count markers))
              "one durable marker per committed height, never more"))))))

(deftest one-crashed-validator-of-four-does-not-stop-consensus
  (testing "n = 3f+1 with f = 1"
    (let [s (-> (fresh) (sim/crash :d) (sim/run 150))]
      (is (sim/agreement? s))
      (is (every? #(>= % 5) (take 3 (heights s)))))))

(deftest two-crashed-validators-of-four-stop-consensus
  (testing "the safety-relevant direction: below quorum nothing may decide"
    (let [s (-> (fresh) (sim/crash :c) (sim/crash :d) (sim/run 200))]
      (is (every? empty? (map #(sim/committed s %) [:a :b])))
      (is (sim/agreement? s)))))

(deftest a-partition-blocks-progress-and-healing-restores-it
  (let [split (-> (fresh) (sim/partition-network [#{:a :b} #{:c :d}]) (sim/run 80))
        healed (sim/run (sim/heal split) 150)]
    (is (every? zero? (heights split)) "neither half of a 2/2 split has a quorum")
    (is (sim/agreement? split))
    (is (every? pos? (heights healed)))
    (is (sim/agreement? healed))))

(deftest consensus-survives-heavy-message-loss
  (let [s (sim/run (fresh {:drop-rate 0.3}) 250)]
    (is (sim/agreement? s))
    (is (every? pos? (heights s))
        "retransmission of our own signed messages is what makes this possible
         -- see `gossip`; the paper assumes a reliable gossip layer and the
         algorithm itself never re-sends anything")))

(deftest a-restart-keeps-the-committed-prefix
  (let [s (-> (fresh) (sim/run 12) (sim/crash :c) (sim/run 8))
        s' (-> s (sim/restart :c) (sim/run 120))]
    (is (sim/agreement? s'))
    (is (pos? (count (sim/committed s' :c))) ":c came back and caught up")))

(deftest a-restarted-node-never-signs-twice-at-one-height-and-round
  (testing "the WAL is replayed for exactly one purpose: to restore the
            double-sign guard. This is what makes the validator non-slashable."
    (let [s (-> (fresh) (sim/run 10) (sim/crash :b) (sim/run 5)
                (sim/restart :b) (sim/run 60))
          signed (->> (get-in s [:storage :b :landed])
                      (keep #(get-in % [:writes :wal]))
                      (filter #(#{:prevote :precommit :proposal} (:type %))))
          keys' (map (juxt :height :round :type) signed)]
      (is (= (count keys') (count (distinct keys')))
          (str "duplicate signature at " (->> keys' frequencies (filter #(> (val %) 1))))))))

(deftest the-simulation-is-reproducible
  (let [run-it #(sim/run (fresh {:drop-rate 0.2}) 100)
        x (run-it), y (run-it)]
    (is (= (sim/all-committed x) (sim/all-committed y)))
    (is (= (:trace x) (:trace y)))))

;; ============================================================
;; Safety properties across seeds and schedules
;; ============================================================

(defn- precommitters
  "Who actually signed a precommit for `vid` at `height`, according to their own
  durable write logs? Read from storage, not from any node's belief."
  [s height vid]
  (into #{}
        (for [p peers
              record (get-in s [:storage p :landed])
              :let [m (get-in record [:writes :wal])]
              :when (and (= :precommit (:type m))
                         (= height (:height m))
                         (= vid (:value-id m)))]
          p)))

(defn- proposed-values
  "Every value any validator ever put on the wire as a proposal."
  [s]
  (into #{}
        (for [p peers
              record (get-in s [:storage p :landed])
              :let [m (get-in record [:writes :wal])]
              :when (= :proposal (:type m))]
          (tm/value-id (:value m)))))

(defn- check-safety [s]
  (let [committed (sim/all-committed s)]
    (and
     ;; AGREEMENT: nobody decides differently at the same height.
     (every? (fn [h]
               (apply = (keep #(nth % h nil) (vals committed))))
             (range (apply max 0 (map count (vals committed)))))
     ;; VALIDITY: every decided value was proposed by somebody.
     (every? (proposed-values s)
             (map tm/value-id (mapcat identity (vals committed))))
     ;; QUORUM: no decision without 2f+1 signed precommits for it.
     (every? (fn [[_ vs]]
               (every? (fn [[h v]]
                         (>= (count (precommitters s h (tm/value-id v)))
                             (node/byzantine-threshold (count peers))))
                       (map-indexed vector vs)))
             committed))))

(defspec safety-holds-under-loss-and-partition 25
  (prop/for-all [seed (gen/choose 1 100000)
                 drop-rate (gen/elements [0.0 0.1 0.25])
                 split? gen/boolean]
                (let [s0 (sim/make {:seed seed
                                    :nodes (zipmap peers (repeat (tm/make)))
                                    :node-config (zipmap peers (repeat node-cfg))
                                    :config {:value-fn value-fn :drop-rate drop-rate}})
                      s1 (if split?
                           (-> s0 (sim/run 40)
                               (sim/partition-network [#{:a :b :c} #{:d}])
                               (sim/run 60)
                               sim/heal)
                           s0)]
                  (check-safety (sim/run s1 120)))))

(defspec safety-holds-under-crash-and-restart 20
  (prop/for-all [seed (gen/choose 1 100000)
                 victim (gen/elements peers)
                 crash-at (gen/choose 3 40)]
                (let [s (-> (sim/make {:seed seed
                                       :nodes (zipmap peers (repeat (tm/make)))
                                       :node-config (zipmap peers (repeat node-cfg))
                                       :config {:value-fn value-fn}})
                            (sim/run crash-at)
                            (sim/crash victim)
                            (sim/run 20))
                      s (-> s (sim/restart victim) (sim/run 120))]
                  (check-safety s))))
