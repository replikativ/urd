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
            [urd.consensus.reconfig :as reconfig]
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

(deftest l22-prevotes-nil-for-a-value-the-application-rejects
  (testing "`:valid-fn`'s FALSE arm, which had never executed

           It defaults to `(constantly true)` and was not configured anywhere
           in src, test or docs, so every test in this suite exercised the same
           branch. An application-supplied predicate that ever returns false
           was, in effect, untested code -- and it is the only thing standing
           between a Byzantine proposer and an arbitrary value being prevoted
           by every honest node.

           Prevoting nil is the correct response: the node does not endorse the
           value, the round times out, and a later proposer offers another. It
           does not stall, and it does not accept."
    (let [bad {:id :x :payload :garbage}
          st (-> (st0 :round 0 :step :propose
                      :valid-fn (fn [v] (not= :garbage (:payload v))))
                 (assoc-in [:proposals 0 :a] (pp :a 0 bad -1)))
          st' (#'tm/rule-l22 st)]
      (is (= [nil] (map :value-id (signed st')))
          "nil, not the value id -- we move on rather than endorse it")
      (is (= :prevote (:step st'))
          "and the round still advances, so a rejected proposal is not a stall")))

  (testing "and the same predicate's true arm still prevotes the value, so the
            test is not passing because the fixture broke"
    (let [good {:id :x :payload :fine}
          st (-> (st0 :round 0 :step :propose
                      :valid-fn (fn [v] (not= :garbage (:payload v))))
                 (assoc-in [:proposals 0 :a] (pp :a 0 good -1)))]
      (is (= [:x] (map :value-id (signed (#'tm/rule-l22 st))))))))

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

(defn- signed-keys
  "Every (height, round, type) this peer has signed according to its own landed
  writes."
  [s p]
  (->> (get-in s [:storage p :landed])
       (keep #(get-in % [:writes :wal]))
       (filter #(#{:prevote :precommit :proposal} (:type %)))
       (mapv (juxt :height :round :type))))

(deftest a-message-naming-an-absurd-round-is-dropped
  (testing "the message log is keyed by round, and the keys were unbounded: one
            validator sending votes at rounds 1, 2, ... 10^9 allocated one map
            entry per round at a single height. Rounds advance only on timeouts,
            so no honest node is ever more than a handful ahead."
    (let [impl (tm/make)
          {st :state} (node/init impl {:peer-id :a :validators [:a :b :c :d]})
          vote (fn [r] {:type :prevote :from :b :height 0 :round r :value-id :v})
          feed (fn [st msg] (:state (node/step impl st (node/message-received :b msg #{:b}))))
          near (feed st (vote 3))
          far (feed st (vote 1000000))]
      (is (seq (get-in near [:prevotes 3])) "a plausible round is recorded")
      (is (empty? (get-in far [:prevotes 1000000])))
      (is (= (:prevotes st) (:prevotes far))
          "and no round key was allocated for it at all"))))

(deftest a-proposal-with-an-impossible-valid-round-is-dropped
  (testing "the paper's proposal carries -1 <= vr < r. L28 re-checks it at the
            point of use, but L22 tests only `(= -1 vr)`, so a proposal with
            vr = -7 sat in the log looking to any other reader like a
            valid-round claim."
    (let [impl (tm/make)
          {st :state} (node/init impl {:peer-id :a :validators [:a :b :c :d]})
          prop (fn [r vr] {:type :proposal :from :b :height 0 :round r
                           :value :v :vr vr})
          feed (fn [msg] (:state (node/step impl st (node/message-received :b msg #{:b}))))]
      (is (seq (get-in (feed (prop 2 -1)) [:proposals 2])) "vr = -1 is the normal case")
      (is (seq (get-in (feed (prop 2 1)) [:proposals 2])) "and 0 <= vr < r is legal")
      (is (empty? (get-in (feed (prop 2 -7)) [:proposals 2])) "vr < -1")
      (is (empty? (get-in (feed (prop 2 2)) [:proposals 2])) "vr = r")
      (is (empty? (get-in (feed (prop 2 5)) [:proposals 2])) "vr > r")
      (is (empty? (get-in (feed (prop 2 nil)) [:proposals 2])) "vr absent"))))

(deftest a-proposer-that-crashed-before-proposing-proposes-on-restart
  (testing "the round is otherwise spent, every time.

            `replay-one` sets step to `:propose` both for a node that never
            proposed and for one that proposed and crashed. Restarting into the
            propose step used to arm the PROPOSE TIMER in both cases -- which,
            when the restarted node is the proposer, means waiting for a
            proposal from itself. Nobody else proposes at that round, so it
            expires, everyone prevotes nil, and the round is lost.

            Reaching that branch takes care. An empty durable log replays to
            height 0, round 0, nothing signed -- which is the FRESH path, and
            the fresh path always proposed. The restart path needs a node that
            has decided a height: an `:end-height` marker replays to height h+1,
            round 0, step `:propose`, with the sign guard carried over. That is
            a node which committed and crashed before proposing the next
            height, and it is the ordinary case, not a corner."
    (let [impl (tm/make)
          vs [:a :b :c :d]
          decided {:writes {:wal {:type :end-height :height 0 :decision :v0}}}
          restart (fn [id]
                    (node/init impl {:peer-id id :validators vs
                                     :restored {:writes [decided]
                                                :durable {:last-signed
                                                          {:height 0 :round 0
                                                           :step :precommit}}}}))
          proposer (first (filter #(some? (:awaiting-value (:state (restart %)))) vs))]

      ;; Sanity: the replay really did put everyone at height 1, step propose,
      ;; with no proposal of their own -- i.e. on the restart branch.
      (doseq [id vs]
        (let [st (:state (restart id))]
          (is (= 1 (:height st)) (str id " resumed at the next height"))
          (is (= :propose (:step st)))
          (is (nil? (get-in st [:proposals 0 id])) (str id " has no proposal of its own"))))

      (is (some? proposer)
          "exactly the proposer for height 1 asks the application for a value")

      (let [{st :state fx :effects} (restart proposer)]
        (is (some? (:awaiting-value st)))
        (is (some #(= :request-value (node/effect-kind %)) fx)
            "it proposes rather than arming a timer to wait for itself"))

      (let [other (first (remove #{proposer} vs))
            {st :state fx :effects} (restart other)]
        (is (nil? (:awaiting-value st)))
        (is (some #(and (= :set-timer (node/effect-kind %))
                        (= :propose (first (:timer-id (node/effect-params %)))))
                  fx)
            "while a non-proposer still waits, which is correct for it")))))

(deftest the-sign-guard-outlives-the-wal
  (testing "the substrate question, stated as a fault: WIPE the write-ahead log
            and leave only the durable register.

            CometBFT keeps `FilePVLastSignState` in a file distinct from the WAL
            (`privval/file.go:74-83`) precisely so this scenario is survivable --
            a validator that loses its WAL can re-derive everything else, but one
            that loses its last-sign state can be slashed. Deriving the guard
            from the WAL, as this implementation originally did, put it back
            inside the thing it must outlive: with `:landed` emptied the guard
            came back `nil` and :b happily signed height 0 round 0 a second time.

            Nothing else here changes. The register is a last-write-wins merge of
            landed writes, which is exactly the atomically-rewritten-file
            semantics, and `:durable` is untouched by the wipe."
    (let [s (-> (fresh) (sim/run 14) (sim/crash :b) (sim/run 6))
          before (signed-keys s :b)
          register (get-in s [:storage :b :durable :last-signed])
          ;; The fault: the WAL is gone, the register is not.
          wiped (assoc-in s [:storage :b :landed] [])
          s' (-> wiped (sim/restart :b) (sim/run 120))
          after (signed-keys s' :b)
          all (concat before after)]
      (is (seq before) ":b must actually have signed something before the wipe,
                        or this test proves nothing")
      (is (some? register) "the guard must have its own durable key at all")
      (is (= (count all) (count (distinct all)))
          (str "signed twice after losing the WAL: "
               (->> all frequencies (filter #(> (val %) 1)) (into {}))))
      (is (sim/agreement? s')))))

(deftest the-sign-guard-also-survives-losing-the-register
  (testing "the other direction. Restore takes whichever of the WAL-derived
            value and the register is FURTHER ALONG, so neither substrate alone
            can move the guard backwards."
    (let [s (-> (fresh) (sim/run 14) (sim/crash :b) (sim/run 6))
          before (signed-keys s :b)
          wiped (update-in s [:storage :b :durable] dissoc :last-signed)
          s' (-> wiped (sim/restart :b) (sim/run 120))
          ;; `:landed` is NOT wiped here, so it already carries the pre-crash
          ;; signatures -- concatenating `before` would double-count them.
          all (signed-keys s' :b)]
      (is (seq before))
      (is (= (count all) (count (distinct all)))
          (str "signed twice after losing the register: "
               (->> all frequencies (filter #(> (val %) 1)) (into {}))))
      (is (sim/agreement? s')))))

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

;; ============================================================
;; Regression: nil is not a value
;; ============================================================

(deftest a-nil-valued-proposal-cannot-lock-decide-or-wedge
  (testing "one Byzantine proposer sending :value nil used to take the cluster down.

            `value-id` maps both nil and {:id nil} onto nil, which is also the
            sentinel for prevote-nil -- so a nil-valued proposal was
            indistinguishable from 'no value' at every stage. Every honest node
            prevoted for it, LOCKED on nil, recorded {height nil} as a decision,
            and then refired L49 forever because all three decision guards
            tested truthiness rather than membership and could not see a nil
            decision. The rule fixpoint hit its iteration limit and threw: a
            one-validator denial of service.

            `:valid-fn` could not have caught it -- it defaults to
            (constantly true) and was never configured anywhere, so its false
            arm had never run."
    (let [nil-prop (pp :a 0 nil -1)]
      ;; L36 must not lock on nil.
      (let [st (-> (st0 :round 0 :step :prevote)
                   (assoc-in [:proposals 0 :a] nil-prop)
                   (with-votes :prevotes 0 (map #(pv % 0 nil) [:a :b :c :d])))
            st' (#'tm/rule-l36 st)]
        (is (nil? (:locked-round st')) "must not lock on a nil value")
        (is (nil? (:valid-round st')) "and must not treat it as a valid value"))
      ;; L49 must not decide nil.
      (let [st (-> (st0 :round 0 :step :precommit)
                   (assoc-in [:proposals 0 :a] nil-prop)
                   (with-votes :precommits 0 (map #(pc % 0 nil) [:a :b :c :d])))
            st' (#'tm/rule-l49 st)]
        (is (not (contains? (:decisions (or st' st)) 0))
            "a nil precommit quorum is prevote-nil, not a decision")))))

(deftest a-decision-guard-must-test-membership-not-truthiness
  (testing "even if a nil decision were somehow recorded, the guards must see it"
    (let [st (assoc-in (st0 :round 0) [:decisions 0] nil)]
      (is (contains? (:decisions st) 0))
      ;; The rule must not fire again for a height already decided.
      (is (nil? (#'tm/rule-l49 st))
          "L49 refiring on an already-decided height is what wedged the fixpoint"))))

;; ============================================================
;; Catch-up beyond a lag of one
;; ============================================================

(deftest a-node-many-heights-behind-catches-up
  (testing "LIVENESS, and the measured freeze. The only catch-up mechanism was
            `:last-commit` -- our own signed messages from the IMMEDIATELY
            preceding height -- and `advance-height` overwrites it, so height
            H's evidence is unrecoverable from anyone the moment the network
            reaches H+2. A node at lag >= 2 had no trigger of any kind.

            Measured before the fix: 7 validators, no Byzantine nodes, no
            partition. Crash one at height 19, let the network run to 66,
            restart it, run 1200 more ticks -- it advanced exactly ONE height
            and then froze, 117 behind, with no future buffer, no precommits
            and no timer armed.

            CometBFT announces (H,R,Step) continuously (`reactor.go:516`) and
            serves a lagging peer the Commit for its height from the block
            store (`:907-937`) at any lag."
    (let [s (-> (fresh) (sim/run 12) (sim/crash :b) (sim/run 90))
          others (remove #{:b} [:a :b :c :d])
          ahead (apply min (map #(:height (sim/node-state s %)) others))
          behind (:height (sim/node-state s :b))]
      (is (> (- ahead behind) 1)
          "the network must be more than one height ahead, or this proves
           nothing about lag >= 2")
      (let [s' (-> s (sim/restart :b) (sim/run 400))
            caught (:height (sim/node-state s' :b))]
        (is (> caught behind) ":b made progress at all")
        (is (>= caught (- ahead 1))
            (str "and caught up: was " behind ", network was " ahead
                 ", reached " caught))
        (is (sim/agreement? s')
            "without committing anything twice or out of order")))))

(deftest catch-up-needs-f-plus-one-agreeing-peers
  (testing "a single peer's claim is not enough. Our ingest authenticates the
            SENDER and nothing else, so a peer cannot vouch for another peer's
            precommits -- forwarding a commit proof would mean trusting the
            forwarder. f+1 distinct claims contains at least one honest node,
            and an honest node only claims a value it decided."
    (let [s (-> (fresh) (sim/run 12) (sim/crash :b) (sim/run 60))
          st (sim/node-state s :b)
          h (:height st)
          lie {:type :catchup :from :a :height h :decision {:id [:blk :evil h 0]}}
          one (:state (node/step (tm/make) st (node/message-received :a lie #{:a})))]
      (is (not (contains? (:decisions one) h))
          "one claim decides nothing")
      (let [two (:state (node/step (tm/make) one
                                   (node/message-received
                                    :c (assoc lie :from :c) #{:c})))]
        (is (contains? (:decisions two) h)
            "f+1 = 2 of 4 agreeing claims is enough")))))

;; ============================================================
;; Catch-up is not the gossip interval
;; ============================================================

(deftest a-node-that-is-behind-polls-separately-from-vote-gossip
  (testing "these rode the same timer, and that made the gossip interval the
            catch-up RATE

           `answer-status` replies with exactly one height, so a lagging node
           gained one height per gossip interval and no faster. Measured on
           four validators over websockets, crash and restart, twenty seconds:

               :gossip-interval 12 (default)   gap 20 -> 40, never converges
               :gossip-interval  3             gap  7 ->  0

           Turning the gossip interval down fixes the lag and pays the whole
           vote retransmission at the same rate: a `gossip` tick carries every
           message we signed this round plus the last commit, while this one
           carries `{:type :status :height h}`.

           So it is a second timer, armed only while behind. On stock defaults
           the same fault run now goes 90 -> 310 against the cluster's 310 --
           gap 9 -> 0, with `:gossip-interval` untouched."
    (let [impl (tm/make)
          st (st0 :height 5)
          ;; A peer says it is at 40. That is the evidence of being behind.
          heard (:state (node/step impl st (node/message-received
                                            :b {:type :status :from :b :height 40}
                                            #{:b})))
          armed (:effects (node/step impl st (node/message-received
                                              :b {:type :status :from :b :height 40}
                                              #{:b})))]
      (is (= 40 (:peer-height heard)) "the furthest claim is remembered")
      (is (some #(and (= :set-timer (node/effect-kind %))
                      (= @#'tm/catchup-timer (:timer-id (node/effect-params %))))
                armed)
          "and the catch-up poll is armed")))

  (testing "a healthy node arms nothing, so the poll costs a converged cluster
            exactly nothing"
    (let [impl (tm/make)
          st (st0 :height 40)
          fx (:effects (node/step impl st (node/message-received
                                           :b {:type :status :from :b :height 5}
                                           #{:b})))]
      (is (not-any? #(and (= :set-timer (node/effect-kind %))
                          (= @#'tm/catchup-timer (:timer-id (node/effect-params %))))
                    fx)
          "a peer BEHIND us is not evidence that we are behind")))

  (testing "and the poll carries only :status -- if it carried the gossip
            payload it would be the gossip timer with a different name"
    (let [impl (tm/make)
          st (assoc (st0 :height 5) :peer-height 40)
          fx (:effects (node/step impl st (node/timer-fired @#'tm/catchup-timer)))
          sent (keep #(when (= :broadcast (node/effect-kind %))
                        (:msg (node/effect-params %)))
                     fx)]
      (is (= [:status] (mapv :type sent))
          "one status message, and nothing else"))))

;; ============================================================
;; Bounded memory
;; ============================================================

(deftest decisions-and-proposal-alts-do-not-grow-without-bound
  (testing "`advance-height` already trimmed `:catchup-claims`, with a comment
            saying why -- 'keeping older ones is pure growth'. Two structures
            were not in that list.

           `:decisions` grew one entry per height for the life of the process.
           `:proposal-alts` is worse: `record-proposal` files every CONFLICTING
           proposal under `[round (value-id ...)]`, an ATTACKER-CHOSEN key,
           deduped for reporting by `:reported` but not for storage -- and it
           survived every height transition, so one equivocating validator grew
           it without bound.

           Retention for `:decisions` is a policy rather than a cache size:
           `answer-status` serves from it, so what is dropped is exactly what a
           lagging peer can no longer be caught up on. Hence configurable, and
           hence the current height is always kept whatever the setting."
    (let [impl (tm/make)
          st (-> (st0 :height 50 :decision-retention 10)
                 (assoc :decisions (into {} (map (fn [h] [h {:id [:v h]}])) (range 51)))
                 (assoc :proposal-alts {0 {:x :p1} 1 {:y :p2}}))
          after (#'tm/advance-height st)]
      (is (= 51 (:height after)))
      (is (= 10 (count (:decisions after)))
          "trimmed to the retention window")
      (is (every? #(>= % 41) (keys (:decisions after)))
          "and it is the NEWEST heights that survive")
      (is (empty? (:proposal-alts after))
          "and the attacker-keyed map is cleared with the other per-height
           buckets it should always have been reset alongside")))

  (testing "the height just DECIDED survives the trim, at any retention

           Not the new current height -- that one has not been decided yet, by
           definition, and my first version of this test asserted it was
           present and was simply wrong about the algorithm. What matters is
           that moving to h+1 never drops h, because several rules test
           `(contains? (:decisions st) (:height st))` and a node that forgot
           the decision it just made would re-propose that height."
    (let [st (-> (st0 :height 5 :decision-retention 1)
                 (assoc :decisions (into {} (map (fn [h] [h {:id [:v h]}])) (range 6))))
          after (#'tm/advance-height st)]
      (is (contains? (:decisions after) 5)
          "the height we just left is still there")
      (is (>= 2 (count (:decisions after)))
          "and retention 1 really does mean about one")))

  (testing "nil retention keeps everything -- the old behaviour, still
            available and still unbounded, chosen rather than inherited"
    (let [st (-> (st0 :height 50 :decision-retention nil)
                 (assoc :decisions (into {} (map (fn [h] [h {:id [:v h]}])) (range 51))))]
      (is (= 51 (count (:decisions (#'tm/advance-height st))))))))

;; ============================================================
;; WAL compaction
;; ============================================================

(deftest the-wal-is-rewritten-instead-of-growing-forever
  (testing "`:decision-retention` bounds MEMORY; this bounds the STORE, and the
            two are independent. A node can hold a thousand decisions in RAM
            while replaying a million WAL records to get them, which is what
            this algorithm did: every proposal, prevote and precommit it ever
            signed stayed on disk for the life of the deployment, and restart
            cost grew without limit.

           `:wal-retention 4` here so a short run crosses the threshold; the
           default is 100 heights and the arithmetic is identical."
    (let [s (-> (fresh {} {:wal-retention 4}) (sim/run 900))
          landed (get-in s [:storage :a :landed])
          h (:height (sim/node-state s :a))]
      (is (> h 8) "the run has to pass several checkpoints to prove anything")
      (is (some #(contains? (:writes %) :decided-through) landed)
          "the surviving records carry the state the WAL used to be replayed for")
      (is (< (count landed) (* 3 h))
          (str "the store is bounded by the checkpoint interval, not by the
                number of messages ever signed -- got " (count landed)
               " records at height " h)))))

(deftest a-checkpoint-alone-is-enough-to-restart-from
  (testing "the round trip, and it has to be set up deliberately.

           Restarting a node that has simply been running is NOT a test of the
           checkpoint: after one is written, every later `:end-height` appends
           an ordinary record carrying `:decided-through` again, so the restore
           succeeds off that tail no matter what the checkpoint left out.
           Measured -- three mutations that drop load-bearing keys from the
           checkpoint (`:decided-through`, `:decisions`, `:last-signed`) all
           passed a plain crash-restart test.

           So the WAL is cut back to the checkpoint record alone, which is the
           state a real store is in the instant after `checkpoint!` returns and
           before the next height closes. Crash there and this is exactly what
           comes back."
    (let [;; Advance until :b's log IS exactly one checkpoint record -- the
          ;; instant after `checkpoint!` returns and before the next height
          ;; appends anything. Found by running, not by editing the store:
          ;; rewinding a log to an older checkpoint models a store that lost
          ;; writes which had already landed, and the node then correctly
          ;; re-commits the heights it was told to forget. That is a fault
          ;; injection, not a checkpoint test, and it reads as a safety
          ;; violation.
          cp-state (loop [s (fresh {} {:wal-retention 4}), n 0]
                     (let [landed (get-in s [:storage :b :landed])]
                       (cond
                         (and (= 1 (count landed))
                              (not (contains? (:writes (first landed)) :wal)))
                         s
                         (> n 400) nil
                         :else (recur (sim/run s 1) (inc n)))))
          s cp-state
          cp (first (get-in s [:storage :b :landed]))
          before-signed (signed-keys s :b)
          ;; The state the instant it comes back, BEFORE it runs. Everything
          ;; the checkpoint should have carried is rebuilt within a few
          ;; heights of running, so asserting after a 300-tick run proves only
          ;; that the node still works -- measured, mutations that drop
          ;; `:decisions` and `:last-commit` from the checkpoint both survive
          ;; that. What they lose is the ability to serve a peer during the
          ;; window before they catch up, and that is visible only here.
          restarted (-> s (sim/crash :b) (sim/run 10) (sim/restart :b))
          st0 (sim/node-state restarted :b)
          s' (sim/run restarted 300)
          st (sim/node-state s' :b)
          after-signed (signed-keys s' :b)
          all (concat before-signed after-signed)]
      (is (some? cp-state)
          "the run must actually reach a checkpoint, or this proves nothing")
      (is (= [:decided-through :decisions :last-commit :last-signed :powers
              :priorities :validators]
             (sort (keys (:writes cp))))
          "and the checkpoint is the WHOLE durable state -- the store keeps
           nothing else, so a key missing here is a key lost on restart")
      (is (> (:decided-through (:writes cp)) 0)
          "which names the height it closed")
      (is (>= (:height st) (inc (:decided-through (:writes cp))))
          "the node resumes ABOVE the checkpointed height rather than at 0 --
           restarting at 0 is a duplicate delivery of every height to the
           application, which is what `:decided-through` exists to prevent")
      (is (= (count all) (count (distinct all)))
          (str "and it never signs a height+round twice across the restart: "
               (->> all frequencies (filter #(> (val %) 1)) (into {}))))
      (is (= (:decisions (sim/node-state s :b)) (:decisions st0))
          "the decisions come back EXACTLY as the LIVE node held them, before
           the restarted one has run a tick. Compared against the live state
           and not against the checkpoint: a checkpoint that stored `{}` and a
           node that restored `{}` agree with each other perfectly, and that
           assertion passes while the data is gone. They are what
           `answer-status` serves a lagging peer from, so a node that has to
           re-derive them cannot answer during exactly the window when a peer
           most needs it.")
      (is (seq (:last-commit (:writes cp)))
          "the checkpoint records the commit for the height it closed")
      (is (= (:last-commit (:writes cp)) (:last-commit st0))
          "and that commit survives, so a restarted node can still prove the
           height it just decided to a peer one behind")
      (is (sim/agreement? s')
          "and no safety property broke"))))

(deftest a-checkpoint-is-only-ever-taken-at-a-height-boundary
  (testing "SAFETY, and the reason the trigger is not simply `every N writes`.

           Mid-height the WAL holds this node's own votes for a height still in
           progress, and `init` replays them back into its tallies -- that is
           how a restarted node remembers how it voted. Truncating there would
           make it forget, and a validator that forgets its own prevote can
           prevote differently for the same round. CometBFT truncates at
           `#ENDHEIGHT` for this reason.

           So every checkpoint record must carry a `:decided-through`, which is
           written only by an `:end-height`."
    (let [s (-> (fresh {} {:wal-retention 2}) (sim/run 900))]
      (doseq [p peers]
        (let [landed (get-in s [:storage p :landed])]
          ;; After a checkpoint the log is exactly the records it wrote, plus
          ;; whatever was appended since. The FIRST record is the checkpoint.
          (when (> (count landed) 0)
            (let [head (first landed)]
              (is (or (contains? (:writes head) :decided-through)
                      (contains? (:writes head) :wal))
                  (str p ": the log head is either a checkpoint or ordinary WAL"))
              (when-not (contains? (:writes head) :wal)
                (is (some? (:decided-through (:writes head)))
                    (str p ": a checkpoint names the height it closed"))))))))))

;; ============================================================
;; Joining by state sync
;; ============================================================

(deftest a-node-joins-at-a-height-without-replaying-any-history
  (testing "the path a NEW VALIDATOR takes, and the reason it is not blocked on
            a consensus-level history transfer.

           There is no archival tier anywhere in this library. Every algorithm
           bounds catch-up with an in-memory window, and compaction truncates
           the DURABLE log to match -- so a peer far enough behind cannot be
           caught up from anyone's consensus state, however many peers are
           healthy. Widening retention only moves the number.

           The way out is the one CometBFT takes and the one kabel and
           konserve-sync already implement: transfer the APPLICATION state, not
           the block history, and start consensus above it. urd's side of that
           is already here -- `:decided-through` is a trusted register, and a
           node handed nothing but that register starts above it holding no
           history at all.

           Modelled by wiping the consensus log down to the register while
           KEEPING what the node had committed, because that is what a state
           sync leaves behind: konserve-sync moved the database, the consensus
           log did not come with it."
    (let [s (sim/run (fresh) 400)
          h (:height (sim/node-state s :b))
          decided (dec h)
          committed-before (count (sim/committed s :b))
          joined (-> s
                     (sim/crash :b)
                     ;; No history. One trusted number, which is all a state
                     ;; sync can hand over.
                     (assoc-in [:storage :b :landed] [])
                     (assoc-in [:storage :b :durable] {:decided-through decided})
                     (sim/restart :b)
                     (sim/run 400))
          st (sim/node-state joined :b)]
      (is (> h 3) "the cluster must have real history for the join to skip any")
      (is (>= (:height st) h)
          "the joiner resumes ABOVE the height it was handed, not at 0")
      (is (empty? (:decisions (sim/node-state (-> s (sim/crash :b)
                                                  (assoc-in [:storage :b :landed] [])
                                                  (assoc-in [:storage :b :durable]
                                                            {:decided-through decided})
                                                  (sim/restart :b))
                                              :b)))
          "holding no decisions -- it replayed nothing, which is the point")
      (is (= committed-before
             (count (take committed-before (sim/committed joined :b))))
          "and it did NOT re-deliver the heights it already had: a joiner that
           re-commits its transferred prefix hands the ledger every transaction
           a second time")
      (is (sim/agreement? joined)
          "it agrees with the peers it joined")
      (is (> (count (sim/committed joined :b)) committed-before)
          "and goes on committing, so it really did rejoin consensus rather
           than sitting silent above its checkpoint"))))

(deftest the-transferred-ledger-is-itself-the-join-checkpoint
  (testing "closing the loop, and removing a trusted input rather than adding one.

           A state-synced joiner needs to know which height its transferred
           database corresponds to. The obvious design hands it a number
           alongside the data -- one more thing to trust, and one more thing to
           get wrong or forge.

           It is unnecessary. The database knows how many values it applied,
           and for this algorithm that count IS the height: one height decides
           one value, heights start at 0, so a consumer holding N values has
           seen 0..N-1 and starts at N. `:delivered-through` -- built so a
           RESTARTING node would stop re-delivering -- answers a joiner's
           question too, because they are the same question.

           So konserve-sync moves the database and nothing else has to travel
           with it."
    (testing "a joiner with no consensus state at all starts from its ledger"
      (let [{st :state fx :effects}
            (node/init (tm/make) {:peer-id :new :validators [:a :b :c :new]
                                  :delivered-through 500
                                  :restored {:durable {} :writes []}})]
        (is (= 500 (:height st)))
        (is (empty? (:decisions st)) "having replayed nothing")
        (is (empty? (filter #(= :commit (node/effect-kind %)) fx))
            "and it must NOT re-deliver: the ledger already holds those values,
             and handing them over again writes every transaction twice")))

    (testing "and whichever source is further along wins"
      (is (= 91 (:height (:state (node/init (tm/make)
                                            {:peer-id :n :validators [:a :b :c]
                                             :delivered-through 10
                                             :restored {:durable {:decided-through 90}
                                                        :writes []}}))))
          "our own durable register, when the consumer lags it")
      (is (= 300 (:height (:state (node/init (tm/make)
                                             {:peer-id :n :validators [:a :b :c]
                                              :delivered-through 300
                                              :restored {:durable {:decided-through 90}
                                                         :writes []}}))))
          "the consumer, when it is ahead -- a node whose log was wiped but
           whose ledger survived"))))

;; ============================================================
;; Transferable commit certificates
;; ============================================================

(def ^:private atts (tm/test-attestations))

(defn- cert-cfg [extra]
  (merge node-cfg {:sign-vote (:sign-vote atts)
                   :verify-vote (:verify-vote atts)}
         extra))

(defn- cert-fresh []
  (sim/make {:seed 7
             :nodes (zipmap peers (repeat (tm/make)))
             :node-config (zipmap peers (repeat (cert-cfg {})))
             :config {:value-fn value-fn}}))

(deftest a-decision-assembles-a-certificate-of-its-own-precommits
  (testing "the evidence a peer can relay. `corroborated?` exists precisely
            because our ingest authenticates the SENDER and nothing else, so a
            forwarded precommit is a claim by the forwarder -- which is why
            catch-up needs f+1 distinct peers to say the same thing before it
            can be believed. A certificate carries the voters' OWN
            attestations, so it is evidence rather than hearsay."
    (let [s (sim/run (cert-fresh) 200)
          st (sim/node-state s :a)
          h (first (sort (keys (:certificates st))))
          cert (get (:certificates st) h)]
      (is (seq (:certificates st)) "certificates are assembled at all")
      (is (= h (:height cert)))
      (is (= (tm/value-id (get (:decisions st) h)) (:value-id cert))
          "and name the value that was actually decided")
      (is (true? (tm/valid-certificate? st cert h (:value-id cert)))
          "and verify against our own validator set"))))

(deftest one-peer-with-a-certificate-is-enough-to-catch-up
  (testing "the point of the whole exercise. Without a certificate a lagging
            node must hear the SAME decision from f+1 distinct peers before it
            may adopt it -- an extra round trip, and impossible from a single
            surviving peer. With one, a single answer suffices."
    (let [s (sim/run (cert-fresh) 200)
          donor (sim/node-state s :a)
          h (first (sort (keys (:certificates donor))))
          cert (get (:certificates donor) h)
          decision (get (:decisions donor) h)
          ;; A node at that height with nothing else.
          {behind :state} (node/init (tm/make)
                                     (merge (cert-cfg {})
                                            {:peer-id :z :validators peers
                                             :restored {:durable {:decided-through (dec h)}
                                                        :writes []}}))
          one-claim {:type :catchup :from :a :height h :decision decision}]

      (testing "one claim WITHOUT a certificate is not enough"
        (let [{st :state} (node/step (tm/make) behind
                                     (node/message-received :a one-claim #{:a}))]
          (is (not (contains? (:decisions st) h))
              "a single unverifiable claim must not move us -- that is exactly
               what f+1 corroboration is protecting against")))

      (testing "one claim WITH a certificate is"
        (let [{st :state} (node/step (tm/make) behind
                                     (node/message-received
                                      :a (assoc one-claim :cert cert) #{:a}))]
          (is (contains? (:decisions st) h)
              "verified evidence from a single peer decides the height")
          (is (= (tm/value-id decision) (tm/value-id (get (:decisions st) h)))
              "on the value the certificate actually attests to"))))))

(deftest a-forged-or-short-certificate-is-refused
  (testing "each guard, driven down its false arm. A certificate that is
            believed without these checks is strictly worse than no certificate
            at all: it turns one Byzantine peer into an authority."
    (let [s (sim/run (cert-fresh) 200)
          st (sim/node-state s :a)
          h (first (sort (keys (:certificates st))))
          cert (get (:certificates st) h)
          vid (:value-id cert)]
      (is (true? (tm/valid-certificate? st cert h vid)) "the genuine one passes")

      (is (false? (tm/valid-certificate?
                   st (update cert :votes
                              #(into {} (map (fn [[k _]] [k :forged])) %))
                   h vid))
          "attestations that do not verify are refused, however many there are")

      (is (false? (tm/valid-certificate?
                   st (assoc cert :votes (into {} (take 1) (:votes cert))) h vid))
          "and a single genuine vote is not a quorum")

      (is (false? (tm/valid-certificate?
                   st (assoc cert :votes
                             (let [[v a] (first (:votes cert))]
                               {v a, :not-a-validator a, :also-not a}))
                   h vid))
          "voters outside the validator set do not count, so an attacker
           cannot pad a certificate with keys it invented")

      (is (false? (tm/valid-certificate? st cert (inc h) vid))
          "a genuine certificate for another HEIGHT does not apply here")
      (is (false? (tm/valid-certificate? st cert h :some-other-value))
          "nor to another value")
      (is (false? (tm/valid-certificate? st nil h vid)) "nor does nothing")
      (is (false? (tm/valid-certificate? st {:height h :value-id vid} h vid))
          "nor a certificate with no votes at all"))))

(deftest without-a-scheme-nothing-changes
  (testing "certificates are opt-in. A caller that configures no signing scheme
            gets precisely the previous behaviour -- no attestations, no
            certificates, and catch-up on f+1 corroboration -- rather than a
            half-enabled feature that refuses what it cannot verify."
    (let [s (sim/run (fresh) 200)
          st (sim/node-state s :a)]
      (is (seq (:decisions st)) "the cluster decided normally")
      (is (empty? (:certificates st)) "and assembled no certificates")
      (is (false? (tm/valid-certificate? st {:height 0 :value-id :x :votes {}} 0 :x))
          "and cannot verify one, so it never adopts on that path"))))

;; ============================================================
;; Proposer priorities across a restart
;; ============================================================

(deftest priorities-are-read-back-not-replayed-from-genesis
  (testing "CORRECTNESS, and it is invisible until validator powers can change.

           `init` used to rebuild the proposer priorities with one
           `proposer/advance` per height from genesis, using TODAY's powers for
           every historical height. That is right only while powers never
           change -- and the whole point of validator set changes is that they
           do.

           It is also O(height) on every restart. CometBFT has the same shape
           in `LoadValidators` and measured up to 903x at 100k heights past a
           checkpoint, which is why they added one.

           The stored value is as of `:decided-through`, the same height that
           register names, so both advance by exactly one to reach the resume
           height. Off-by-ones around this offset are the largest single bug
           cluster in CometBFT's history -- the same error in six subsystems --
           so the assertion below compares against a node that never restarted
           rather than against my own arithmetic."

    (testing "a restarted node's priorities match one that stayed up"
      (let [s (sim/run (fresh) 400)
            stayed (:priorities (sim/node-state s :b))
            s' (-> s (sim/crash :b) (sim/run 5) (sim/restart :b))
            restarted (:priorities (sim/node-state s' :b))]
        (is (pos? (:height (sim/node-state s :b))) "there is real history")
        (is (= stayed restarted)
            "the restart is invisible in the proposer schedule, which is the
             only property that actually matters here")))

    (testing "and they are persisted, so a real run restores from the store"
      (let [s (sim/run (fresh) 400)
            durable (get-in s [:storage :b :durable])
            live (:priorities (sim/node-state s :b))]
        (is (some? (:priorities durable)) "priorities are actually persisted")
        (is (= live (:priorities
                     (:state (node/init (tm/make)
                                        {:peer-id :b :validators peers
                                         :restored {:durable durable
                                                    :writes (get-in s [:storage :b :landed])}}))))
            "and restoring reproduces the live state exactly")))

    (testing "restore is O(1) in the height, not O(height)"
      ;; The decisive test of the mechanism, and it needs a height no replay
      ;; could plausibly reach. A genesis replay at height 1,000,000 would take
      ;; a million `advance` calls AND land somewhere else entirely; reading the
      ;; stored value takes one.
      (let [powers (zipmap peers (repeat 1))
            stored {:a 7 :b -3 :c -2 :d -2}
            durable {:decided-through 999999 :priorities stored}
            _ (assert (= 1000000 (inc 999999)))
            {st :state} (node/init (tm/make)
                                   {:peer-id :b :validators peers
                                    :restored {:durable durable :writes []}})]
        (is (= 1000000 (:height st)) "resumed above the height it was handed")
        (is (= (proposer/advance stored powers) (:priorities st))
            "exactly ONE advance from the stored value -- the stored priorities
             and `:decided-through` name the same height, so both step by one")
        ;; The coincidence-proof form. Comparing against one particular replay
        ;; length is fragile -- with 4 uniform validators the priorities cycle
        ;; with period 4, so a replay of 1000 lands on all-zeros and can match
        ;; by accident (it did). Independence from the height cannot coincide:
        ;; a genesis replay is a different length at every height, this is
        ;; always exactly one advance.
        (is (= (:priorities st)
               (:priorities (:state (node/init (tm/make)
                                               {:peer-id :b :validators peers
                                                :restored {:durable (assoc durable
                                                                           :decided-through 9)
                                                           :writes []}}))))
            "the SAME stored priorities restore to the same value at height 10
             and at height 1,000,000 -- the result does not depend on the
             height, which is precisely what a genesis replay cannot manage")))))

(deftest a-genesis-replay-and-a-real-history-disagree-once-powers-change
  (testing "the arithmetic on its own, so the claim above does not rest on the
            algorithm being able to change powers yet -- it cannot.

           This is the whole reason the priorities had to become durable before
           any set change lands."
    (let [vs [:a :b :c]
          old-p {:a 1 :b 1 :c 1}
          new-p {:a 5 :b 1 :c 1}
          p0 (proposer/initial-priorities vs)
          truth (as-> p0 x
                  (reduce (fn [p _] (proposer/advance p old-p)) x (range 5))
                  (reduce (fn [p _] (proposer/advance p new-p)) x (range 5)))
          replayed (reduce (fn [p _] (proposer/advance p new-p)) p0 (range 10))]
      (is (not= truth replayed)
          (str "a genesis replay with current powers does not reconstruct a "
               "history that ran under different ones: " truth " vs " replayed)))))

;; ============================================================
;; Validator set changes
;; ============================================================

(deftest a-set-change-activates-one-height-after-the-decision-that-carried-it
  (testing "N=1, not CometBFT's +2, and the difference is structural.

           Their first +1 is FORCED: a block header is built from
           pre-execution state, so the result of deciding H cannot appear in
           H's own header. urd has no header -- the decided value IS the value,
           and every node that decided H holds the update the instant it
           decides. Their second +1 buys light-client pre-commitment we do not
           have.

           Safety at N=1 is that the update rides INSIDE the decided value, so
           agreeing on the value is agreeing on the update. Votes at H were
           counted under the set for H, which this does not touch: exactly one
           set per height, as in CometBFT."
    (let [sm (tm/make)
          st0 (:state (node/init sm {:peer-id :a :validators peers}))
          ;; Decide a value at height 0 that adds :e.
          decided {:id :v0 :validator-updates [{:id :e :power 1}]}
          st1 (-> st0
                  (assoc-in [:decisions 0] decided)
                  (#'urd.consensus.algorithms.tendermint/advance-height))]
      (is (= 1 (:height st1)))
      (is (= [:a :b :c :d :e] (:validators st1))
          "the newcomer is a validator at height 1")
      (is (= 1 (get-in st1 [:powers :e])))
      (is (contains? (:priorities st1) :e)
          "and has a priority, so proposer selection can see it"))))

(deftest the-joining-penalty-is-applied-before-the-height-advance
  (testing "ORDER, which CometBFT gets right by construction: copy the set,
            apply the diff, THEN increment priorities. Reversed, a newcomer
            would be advanced before being penalised and could propose
            immediately -- the thing the penalty exists to prevent."
    (let [sm (tm/make)
          st0 (:state (node/init sm {:peer-id :a :validators peers}))
          st1 (-> st0
                  (assoc-in [:decisions 0] {:id :v0 :validator-updates [{:id :e :power 1}]})
                  (#'urd.consensus.algorithms.tendermint/advance-height))
          ;; What the reconfig alone would give, before any advance.
          after-diff (reconfig/apply-updates
                      {:validators (:validators st0) :powers (:powers st0)
                       :priorities (:priorities st0)}
                      [{:id :e :power 1}])]
      (is (neg? (get-in after-diff [:priorities :e])) "the penalty is negative")
      (is (= (proposer/advance (:priorities after-diff) (:powers after-diff))
             (:priorities st1))
          "the height's priorities are diff-then-advance, in that order"))))

(deftest a-rejected-update-keeps-the-old-set-on-every-node
  (testing "the update is invalid as a pure function of (config, updates), so
            every node classifies it identically and the network stalls on the
            value rather than splitting over it.

           CometBFT panics here. Logging and keeping the old set is the same
           safety property with a better operational story -- and crucially
           NOT a per-node judgement call, which is what caused real data
           corruption in CockroachDB when etcd validated against whatever
           config happened to be active."
    (let [sm (tm/make)
          st0 (:state (node/init sm {:peer-id :a :validators peers}))
          st1 (-> st0
                  ;; Removing a validator that is not in the set.
                  (assoc-in [:decisions 0] {:id :v0 :validator-updates
                                            [{:id :nobody :power 0}]})
                  (#'urd.consensus.algorithms.tendermint/advance-height))]
      (is (= 1 (:height st1)) "the height still advances -- the value was decided")
      (is (= peers (:validators st1)) "but the set is untouched")
      (is (= (:powers st0) (:powers st1)))
      ;; The set surviving is not enough to prove the guard ran: `select-keys`
      ;; on an error map yields {} and the merge is a no-op anyway, so removing
      ;; the check changes no membership -- verified by mutation. What DOES
      ;; change is what the node says about itself, and a node that logs a
      ;; successful reconfiguration it did not perform is worse than one that
      ;; says nothing.
      (let [logs (map #(:message (node/effect-params %)) (get-in st1 [:fx :logs]))]
        (is (some #(re-find #"REFUSING" (str %)) logs)
            (str "the refusal must be reported, not silent: " (pr-str logs)))
        (is (not-any? #(re-find #"validator set changes" (str %)) logs)
            "and it must NOT claim the set changed")))))

(deftest a-changed-set-survives-a-restart
  (testing "once a decided value can change the set, the set is durable STATE
            rather than configuration. A restart that read it from the config
            file would silently revert every change the network had agreed --
            and the node would then count quorums over a set nobody else has,
            which is a split with no message lost and nothing malformed."
    (let [sm (tm/make)
          st0 (:state (node/init sm {:peer-id :a :validators peers}))
          st1 (-> st0
                  (assoc-in [:decisions 0] {:id :v0 :validator-updates [{:id :e :power 3}]})
                  (#'urd.consensus.algorithms.tendermint/advance-height))
          ;; What the durable write would carry at the next end-height.
          durable {:decided-through 0
                   :validators (:validators st1)
                   :powers (:powers st1)
                   :priorities (:priorities st1)}
          restored (:state (node/init sm {:peer-id :a
                                          ;; The CONFIG still names the genesis set.
                                          :validators peers
                                          :restored {:durable durable :writes []}}))]
      (is (= [:a :b :c :d :e] (:validators restored))
          "the durable set wins over the configured one")
      (is (= 3 (get-in restored [:powers :e]))
          "including the power it was given, not a default of 1")
      (is (= peers (:validators st0))
          "and the config set is still what a FRESH node starts from"))))

;; ============================================================
;; Two defects found by audit against CometBFT
;; ============================================================

(deftest gossip-retransmits-the-proof-of-lock-round
  (testing "L28 lets a locked node prevote for a proposal whose POL round `vr`
            is at or above its own `locked-round`, and `vr` is chosen by the
            proposer -- it can sit arbitrarily far below the current round. The
            retransmission window used to be the current and immediately
            preceding round only, on the stated grounds that older rounds
            cannot change a decision a newer round has not settled. That is
            wrong: once the network is two rounds past `vr`, a node that missed
            the round-`vr` prevotes can never be sent them again, can never
            fire L28, and prevotes nil forever.

            Measured on the simulator with FOUR validators, zero Byzantine
            nodes, zero crashes and no message loss: 5000 ticks, still at
            height 0, round 25. Two locked nodes and two that had missed one
            round-0 prevote, alternating 2-2 forever."
    (let [impl (tm/make)
          st0 (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))
          ;; At round 5, holding a proposal whose POL round is 0, and our own
          ;; round-0 prevote -- the message a peer needs to fire L28.
          st (-> st0
                 (assoc :round 5)
                 (assoc-in [:proposals 5 :b] {:type :proposal :from :b :height 0
                                              :round 5 :value {:id :V}
                                              :value-id :V :vr 0})
                 (assoc-in [:prevotes 0 :a] {:type :prevote :from :a :height 0
                                             :round 0 :value-id :V})
                 (assoc-in [:prevotes 4 :a] {:type :prevote :from :a :height 0
                                             :round 4 :value-id :V}))
          sent (->> (:effects (node/step impl st (node/timer-fired @#'tm/gossip-timer)))
                    (filter #(= :broadcast (first %)))
                    (map #(:msg (second %)))
                    (filter #(= :prevote (:type %)))
                    (map (juxt :round :value-id))
                    set)]
      (is (contains? sent [0 :V])
          "the POL round of a proposal we hold must stay in the window")
      (is (contains? sent [4 :V])
          "and the previous round, as before")))

  (testing "a `vr` off the wire cannot widen the window arbitrarily -- it is an
            attacker-chosen integer, so a nonsense value must be ignored rather
            than trusted"
    (let [impl (tm/make)
          st0 (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))
          st (-> st0
                 (assoc :round 3)
                 (assoc-in [:proposals 3 :b] {:type :proposal :from :b :height 0
                                              :round 3 :value {:id :V}
                                              :value-id :V :vr "not-a-round"})
                 (assoc-in [:prevotes 0 :a] {:type :prevote :from :a :height 0
                                             :round 0 :value-id :V}))
          sent (->> (:effects (node/step impl st (node/timer-fired @#'tm/gossip-timer)))
                    (filter #(= :broadcast (first %)))
                    (map #(:msg (second %)))
                    (filter #(= :prevote (:type %)))
                    (map :round) set)]
      (is (not (contains? sent 0))))))

(deftest the-persisted-validator-set-is-the-one-after-activation
  (testing "the durable write is issued when the `:end-height` marker is
            SIGNED; `activate-updates` runs later, in `advance-height`, when
            that write lands. Persisting the live set therefore stored the set
            as it was BEFORE the change the decision carried -- and `init`
            never re-applies it, so a restart in that window reverted the set
            permanently rather than for one height.

            Measured consequences: the restarted node ran a quorum threshold of
            3 while the network ran 4, dropped the new validator's messages as
            non-validator traffic, and diverged on proposer selection from
            height 8 onward, after which every proposal it saw failed
            `proposal-from-proposer` and it prevoted nil forever.

            This asserts on what `finish` ACTUALLY WRITES. The pre-existing
            restart test hand-builds its durable map from post-advance state,
            which is not what `finish` produces -- so it encoded the bug as its
            expectation and passed throughout."
    (let [impl (tm/make)
          st0 (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))
          st (-> st0
                 (assoc-in [:decisions 0] {:id :V :validator-updates [{:id :e :power 1}]})
                 (assoc :fx {:msgs [] :logs []
                             :signed [{:msg {:type :end-height :height 0 :from :a}}]}))
          written (->> (:effects (#'tm/finish st))
                       (filter #(= :persist-then (first %)))
                       (map #(:writes (second %)))
                       (filter :decided-through)
                       first)]
      (is (= [:a :b :c :d :e] (:validators written)))
      (is (= {:a 1 :b 1 :c 1 :d 1 :e 1} (:powers written)))
      (is (= [:a :b :c :d] (:validators st))
          "while the live state is still pre-activation at write time, which is
           exactly why the two used to disagree")))

  (testing "a REFUSED update persists the old set, matching what the node will
            keep -- `activate-updates` returns no `:config` on that path"
    (let [impl (tm/make)
          st0 (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))
          st (-> st0
                 (assoc-in [:decisions 0] {:id :V
                                           :validator-updates [{:id :e :power -5}]})
                 (assoc :fx {:msgs [] :logs []
                             :signed [{:msg {:type :end-height :height 0 :from :a}}]}))
          written (->> (:effects (#'tm/finish st))
                       (filter #(= :persist-then (first %)))
                       (map #(:writes (second %)))
                       (filter :decided-through)
                       first)]
      (is (= [:a :b :c :d] (:validators written))))))

(deftest a-refused-signature-costs-a-round-not-the-process
  (testing "`advance-step` deliberately does not move the step when
            `sign-and-broadcast` refuses -- the double-sign guard said no. L22
            and L28 had no latch, so they re-fired on a state differing only by
            a log line, `apply-rules` reported `fired? true`, and `run-rules`
            spun to `max-rule-iterations` and THREW, killing the node.

            Reachable exactly in the fault `the-sign-guard-outlives-the-wal`
            exists for: the WAL is wiped, the durable registers survive, and
            `replay` yields round 0 / step `:propose` while `:last-signed`
            comes back from its own register at a later round."
    (let [impl (tm/make)
          st (-> (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))
                 (assoc :step :propose :round 0)
                 (assoc :last-signed {:height 0 :round 5 :step :precommit})
                 (assoc-in [:proposals 0 :a] {:type :proposal :from :a :height 0
                                              :round 0 :value {:id :V}
                                              :value-id :V :vr -1}))
          r (node/step impl st (node/timer-fired :nothing))]
      (is (= :propose (:step (:state r)))
          "the node sits out the round rather than believing it voted")
      (is (contains? (:done-l22 (:state r)) 0)
          "and latches the attempt, which is what stops the spin")))

  (testing "the same for L28, whose proposal carries a valid-round"
    (let [impl (tm/make)
          st (-> (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))
                 (assoc :step :propose :round 2)
                 (assoc :last-signed {:height 0 :round 9 :step :precommit})
                 (assoc-in [:proposals 2 :c] {:type :proposal :from :c :height 0
                                              :round 2 :value {:id :V}
                                              :value-id :V :vr 0})
                 (assoc-in [:prevotes 0 :a] {:type :prevote :from :a :height 0
                                             :round 0 :value-id :V})
                 (assoc-in [:prevotes 0 :b] {:type :prevote :from :b :height 0
                                             :round 0 :value-id :V})
                 (assoc-in [:prevotes 0 :c] {:type :prevote :from :c :height 0
                                             :round 0 :value-id :V}))
          r (node/step impl st (node/timer-fired :nothing))]
      (is (= :propose (:step (:state r))))))

  (testing "and the latches are cleared per height, or a node would sit out
            every round of every later height"
    (let [impl (tm/make)
          st (:state (node/init impl {:peer-id :a :validators [:a :b :c :d]}))]
      (is (= #{} (:done-l22 st)))
      (is (= #{} (:done-l28 st))))))
