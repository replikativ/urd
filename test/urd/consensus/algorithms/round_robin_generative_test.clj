(ns urd.consensus.algorithms.round-robin-generative-test
  "Generative tests for round-robin consensus state machine.

  These tests generate:
  - Varying numbers of validators (3-7)
  - Random event sequences simulating network behavior
  - Failure scenarios (message loss, duplication, reordering)
  - Multi-validator simulations

  We verify consensus invariants hold across all generated scenarios."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [urd.consensus.attest :as attest]
            [urd.consensus.node :as n]
            [urd.consensus.algorithms.round-robin :as rr]))

;; ============================================================
;; Generators
;; ============================================================

(def gen-validator-id
  "Generate a validator UUID."
  (gen/fmap (fn [n]
              (java.util.UUID/fromString
               (format "00000000-0000-0000-0000-%012d" n)))
            (gen/choose 1 100)))

(defn gen-validator-set
  "Generate a validator set of size n."
  [n]
  (gen/fmap (fn [ids]
              (into {} (map (fn [id] [id (str "pubkey-" id)]) ids)))
            (gen/vector-distinct gen-validator-id {:num-elements n})))

(def gen-proposal
  "Generate a proposal."
  (gen/fmap (fn [id]
              {:snapshot-id id
               :system-id "test-system"
               :data (str "data-" id)})
            gen/uuid))

(defn gen-height
  "Generate a consensus height (0-10)."
  []
  (gen/choose 0 10))

(defn gen-round
  "Generate a consensus round (0-5)."
  []
  (gen/choose 0 5))

(defn gen-proposal-received-event
  "Generate a proposal-received event."
  [validator-ids]
  (gen/let [proposal gen-proposal
            height (gen-height)
            round (gen-round)
            sender (gen/elements validator-ids)]
    {:type :proposal-received
     :proposal proposal
     :height height
     :round round
     :sender sender}))

(defn gen-vote-received-event
  "Generate a vote-received event."
  [validator-ids proposal-ids]
  (gen/let [proposal-id (gen/elements proposal-ids)
            voter (gen/elements validator-ids)
            signature gen/string-alphanumeric]
    {:type :vote-received
     :proposal-id proposal-id
     :voter voter
     :signature signature}))

(defn gen-timeout-event
  "Generate a timeout event."
  []
  (gen/elements [{:type :timeout :timer-id :proposal-timeout}
                 {:type :timeout :timer-id :quorum-timeout}]))

(defn gen-proposal-finalized-event
  "Generate a proposal-finalized event."
  [proposal-ids]
  (gen/let [proposal gen-proposal
            height (gen-height)]
    {:type :proposal-finalized
     :proposal proposal
     :height height}))

(defn gen-event
  "Generate a random event."
  [validator-ids proposal-ids]
  (gen/frequency
   [[40 (gen-proposal-received-event validator-ids)]
    [30 (gen-vote-received-event validator-ids proposal-ids)]
    [20 (gen-timeout-event)]
    [10 (gen-proposal-finalized-event proposal-ids)]]))

(defn gen-event-sequence
  "Generate a sequence of events."
  [validator-ids proposal-ids length]
  (gen/vector (gen-event validator-ids proposal-ids) length))

;; ============================================================
;; Realistic Event Sequence Generators
;; ============================================================

(defn gen-valid-consensus-round
  "Generate a valid consensus round: proposal → votes → finalization.

  This simulates what happens when everything works correctly."
  [validator-ids height round]
  (gen/let [proposal gen-proposal
            ;; Proposer for this height
            proposer-idx (gen/return (mod height (count validator-ids)))
            proposer (gen/return (nth (sort validator-ids) proposer-idx))

            ;; All validators receive proposal
            proposal-events (gen/return
                             (repeat (count validator-ids)
                                     {:type :proposal-received
                                      :proposal proposal
                                      :height height
                                      :round round
                                      :sender proposer}))

            ;; All validators vote (quorum guaranteed)
            vote-events (gen/return
                         (map (fn [voter]
                                {:type :vote-received
                                 :proposal-id (:snapshot-id proposal)
                                 :voter voter
                                 :signature (str "sig-" voter)})
                              validator-ids))

            ;; Finalization event
            finalize-event (gen/return
                            {:type :proposal-finalized
                             :proposal proposal
                             :height height})]

    (concat proposal-events vote-events [finalize-event])))

(defn gen-consensus-scenario
  "Generate a realistic multi-round consensus scenario."
  [num-validators num-rounds]
  (gen/let [validator-set (gen-validator-set num-validators)
            validator-ids (gen/return (vec (sort (keys validator-set))))

            ;; Generate sequence of consensus rounds
            rounds (gen/fmap
                    (fn [_]
                      (mapcat (fn [height]
                                (gen/generate
                                 (gen-valid-consensus-round validator-ids height 0)))
                              (range num-rounds)))
                    gen/nat)]

    {:validator-set validator-set
     :validator-ids validator-ids
     :events rounds}))

;; ============================================================
;; Failure Injection
;; ============================================================

(defn inject-message-loss
  "Randomly drop some events (simulates network message loss)."
  [events drop-rate]
  (gen/fmap
   (fn [keep-mask]
     (keep-indexed (fn [idx event]
                     (when (nth keep-mask idx) event))
                   events))
   (gen/vector (gen/frequency [[drop-rate (gen/return false)]
                               [(- 100 drop-rate) (gen/return true)]])
               (count events))))

(defn inject-message-duplication
  "Randomly duplicate some events."
  [events dup-rate]
  (gen/fmap
   (fn [dup-mask]
     (mapcat (fn [idx event]
               (if (nth dup-mask idx)
                 [event event]  ; Duplicate
                 [event]))
             (range (count events))
             events))
   (gen/vector (gen/frequency [[dup-rate (gen/return true)]
                               [(- 100 dup-rate) (gen/return false)]])
               (count events))))

(defn inject-reordering
  "Randomly shuffle adjacent events (simulates out-of-order delivery)."
  [events]
  (gen/let [should-shuffle? gen/boolean]
    (if should-shuffle?
      (gen/shuffle events)
      events)))

(defn inject-failures
  "Apply failure injections to event sequence."
  [events config]
  (gen/let [events-after-loss (inject-message-loss events (:message-loss config))
            events-after-dup (inject-message-duplication events-after-loss (:message-duplication config))
            events-after-reorder (inject-reordering events-after-dup)]
    events-after-reorder))

;; ============================================================
;; Multi-Validator Simulation
;; ============================================================

(defn create-validator-states
  "Create initial states for all validators."
  [validator-set]
  (into {}
        (map (fn [v-id]
               [v-id {:sm (rr/create validator-set)
                      :state (:state (n/init (rr/create validator-set)
                                             (merge (rr/test-attestations)
                                                    {:peer-id v-id
                                                     :validators (vec (keys validator-set))})))}])
             (keys validator-set))))

(defn ->input
  "Translate a legacy event map into a core-protocol input.

  The generators below emit the event shapes the old `ConsensusAlgorithm`
  protocol took -- `:proposal-received`, `:vote-received`, `:start-round`. The
  algorithm now takes `:message-received`, `:timer-fired` and `:value-ready`,
  which is the whole point of having one protocol. Translating HERE keeps the
  generators, and what they generate, exactly as they were: these properties are
  about the algorithm, not about the calling convention, and rewriting them
  would have quietly changed what is being tested."
  [event]
  (case (:type event)
    :start-round {:type :timer-fired :timer-id :next-round}
    :timeout {:type :timer-fired :timer-id (:timer-id event)}
    :proposal-ready {:type :value-ready :value (:proposal event)}
    :proposal-received {:type :message-received
                        :from (:sender event)
                        :msg {:kind :proposal :proposal (:proposal event)
                              :height (:height event) :round (:round event)}}
    :vote-received {:type :message-received
                    :from (:voter event)
                    :msg {:kind :vote :proposal-id (:proposal-id event)
                          :voter (:voter event)
                          :att (if (contains? event :att)
                                 (:att event)
                                 ((:sign-vote (rr/test-attestations))
                                  (:voter event) (:proposal-id event)))}}
    :proposal-finalized {:type :message-received
                         :from (:sender event)
                         :msg {:kind :finalized :proposal (:proposal event)
                               :height (:height event)}}
    event))

(defn deliver-event-to-validator
  "Deliver an event to a specific validator and return new state."
  [validator-state event]
  (let [{:keys [sm state]} validator-state
        result (n/step sm state (->input event))]
    {:sm sm
     :state (:state result)
     :effects (:effects result)}))

(defn deliver-event-to-all
  "Deliver an event to all validators (broadcast)."
  [validator-states event]
  (into {}
        (map (fn [[v-id v-state]]
               [v-id (deliver-event-to-validator v-state event)])
             validator-states)))

(defn run-simulation
  "Run a multi-validator simulation with given events."
  [validator-set events]
  (let [initial-states (create-validator-states validator-set)]
    (reduce (fn [states event]
              (deliver-event-to-all states event))
            initial-states
            events)))

;; ============================================================
;; Invariant Checks
;; ============================================================

(defn check-agreement-across-validators
  "SAFETY: no two validators finalized DIFFERENT proposals at one height.

  This replaces a predicate that could not fail. It read

      (= (count finalized) (count (keys finalized)))

  which is true of every map and `0` for nil -- and it was the only assertion
  in the file with `safety` in its name, folded into `check-all-invariants`,
  which is the ENTIRE assertion of all eight defspecs. So the generative suite
  established nothing about safety across four hundred generated scenarios.

  It could not have: the file never required `urd.consensus.sim` and never
  called `sim/agreement?`, so no predicate here ever compared one validator to
  another. Every check was intra-validator, and disagreement is by definition a
  relation BETWEEN validators.

  This is not hypothetical. Three real round-robin divergences were found and
  fixed in one session -- a stale state-sync erasing the proposer's own
  proposal, catch-up jumping to a peer's height, and one-proposal-per-height
  enforced on two of the four paths that can set one. None of them was caught
  here."
  [validator-states]
  (let [by-height (reduce (fn [acc [_ v-state]]
                            (reduce (fn [acc [h p]]
                                      (update acc h (fnil conj #{}) p))
                                    acc
                                    (get-in v-state [:state :finalized])))
                          {}
                          validator-states)]
    (every? (fn [[_ proposals]] (= 1 (count proposals))) by-height)))

(defn check-monotonic-height
  "Heights should be monotonically increasing or equal."
  [validator-states]
  (every? (fn [[v-id v-state]]
            (let [state (:state v-state)
                  height (:height state)
                  finalized-heights (keys (:finalized state))]
              ;; All finalized heights should be < current height
              (every? #(< % height) finalized-heights)))
          validator-states))

(defn check-vote-counts-positive
  "Every recorded vote is a voter mapped to the attestation that proves it.

  `:votes` was a set of bare NAMES, which is all a relayed `:vote-bundle` could
  carry and all a receiver could check -- so one peer could hand a node a full
  quorum it had invented. It is now `{voter attestation}`, and this invariant
  checks the shape as well as the count, because the shape is the guarantee."
  [validator-states]
  (every? (fn [[v-id v-state]]
            (let [votes (get-in v-state [:state :votes])]
              (every? (fn [[prop-id voters]]
                        (and (map? voters)
                             (every? some? (vals voters))
                             (>= (count voters) 0)))
                      votes)))
          validator-states))

(defn check-quorum-size-correct
  "Quorum size should be > n/2."
  [validator-set validator-states]
  (let [n (count validator-set)
        expected-quorum (inc (quot n 2))]
    (= expected-quorum (rr/quorum-size validator-set))))

(defn check-phase-valid
  "Phase should be one of the valid phases."
  [validator-states]
  (every? (fn [[v-id v-state]]
            (let [phase (get-in v-state [:state :phase])]
              (contains? #{:proposing :voting :finalizing} phase)))
          validator-states))

(defn check-current-proposal-consistency
  "If current-proposal exists, current-proposal-id should match."
  [validator-states]
  (every? (fn [[v-id v-state]]
            (let [state (:state v-state)
                  proposal (:current-proposal state)
                  proposal-id (:current-proposal-id state)]
              (if proposal
                (= (:snapshot-id proposal) proposal-id)
                (nil? proposal-id))))
          validator-states))

(defn check-all-invariants
  "Check all consensus invariants."
  [validator-set validator-states]
  (and
   (check-agreement-across-validators validator-states)
   (check-monotonic-height validator-states)
   (check-vote-counts-positive validator-states)
   (check-quorum-size-correct validator-set validator-states)
   (check-phase-valid validator-states)
   (check-current-proposal-consistency validator-states)))

;; ============================================================
;; Properties
;; ============================================================

(defn prop-random-events-maintain-invariants
  "Property: Random event sequences maintain invariants."
  [num-validators num-events]
  (prop/for-all [validator-set (gen-validator-set num-validators)
                 proposal-ids (gen/vector gen/uuid 5)]
                (let [validator-ids (vec (sort (keys validator-set)))
                      events (gen/generate (gen-event-sequence validator-ids proposal-ids num-events))
                      final-states (run-simulation validator-set events)]
                  (check-all-invariants validator-set final-states))))

(defn prop-valid-consensus-rounds-succeed
  "Property: Valid consensus rounds should complete successfully."
  [num-validators num-rounds]
  (prop/for-all [validator-set (gen-validator-set num-validators)]
                (let [validator-ids (vec (sort (keys validator-set)))
                      events (mapcat (fn [height]
                                       (gen/generate
                                        (gen-valid-consensus-round validator-ids height 0)))
                                     (range num-rounds))
                      final-states (run-simulation validator-set events)]

      ;; Invariants should hold
                  (and (check-all-invariants validator-set final-states)

           ;; All validators should have finalized num-rounds proposals
                       (every? (fn [[v-id v-state]]
                                 (= num-rounds (count (get-in v-state [:state :finalized]))))
                               final-states)))))

(defn prop-consensus-with-failures
  "Property: Consensus should maintain invariants even with network failures."
  [num-validators num-rounds]
  (prop/for-all [validator-set (gen-validator-set num-validators)
                 message-loss (gen/choose 0 30)
                 message-duplication (gen/choose 0 20)]
                (let [validator-ids (vec (sort (keys validator-set)))
                      events (mapcat (fn [height]
                                       (gen/generate
                                        (gen-valid-consensus-round validator-ids height 0)))
                                     (range num-rounds))
                      failure-config {:message-loss message-loss
                                      :message-duplication message-duplication
                                      :reorder? false}
                      events-with-failures (gen/generate (inject-failures events failure-config))
                      final-states (run-simulation validator-set events-with-failures)]

      ;; Invariants must always hold, even with failures
                  (check-all-invariants validator-set final-states))))

;; ============================================================
;; Test Specs
;; ============================================================

(defspec random-events-3-validators-maintain-invariants 50
  (prop-random-events-maintain-invariants 3 20))

(defspec random-events-5-validators-maintain-invariants 50
  (prop-random-events-maintain-invariants 5 20))

(defspec random-events-7-validators-maintain-invariants 50
  (prop-random-events-maintain-invariants 7 20))

(defspec valid-consensus-3-validators-2-rounds 50
  (prop-valid-consensus-rounds-succeed 3 2))

(defspec valid-consensus-5-validators-3-rounds 50
  (prop-valid-consensus-rounds-succeed 5 3))

(defspec valid-consensus-7-validators-2-rounds 30
  (prop-valid-consensus-rounds-succeed 7 2))

(defspec consensus-with-failures-3-validators 50
  (prop-consensus-with-failures 3 2))

(defspec consensus-with-failures-5-validators 50
  (prop-consensus-with-failures 5 2))

;; ============================================================
;; Additional Properties
;; ============================================================

(defn prop-quorum-is-a-majority
  "Property: round-robin's quorum is a strict majority, and is achievable.

  Round-robin is CRASH-fault-tolerant, so a majority is the correct threshold
  for it. See `rr/quorum-size` for why raising it to the Byzantine threshold
  would cost liveness without buying safety."
  []
  (prop/for-all [n (gen/choose 3 15)]
                (let [validator-set (gen/generate (gen-validator-set n))
                      quorum (rr/quorum-size validator-set)]
                  (and
                   ;; Strict majority: two quorums always intersect in >= 1 node,
                   ;; which is what gives CFT agreement.
                   (> (* 2 quorum) n)
                   ;; Achievable at all.
                   (<= quorum n)
                   ;; Tolerates the crash of a minority.
                   (<= quorum (- n (quot (dec n) 2)))))))

(defspec quorum-is-a-majority-property 100
  (prop-quorum-is-a-majority))

(defn prop-quorum-thresholds-differ
  "Property: the CFT and BFT thresholds are DIFFERENT, on purpose.

  `rr/quorum-size` is a crash-fault majority; the Byzantine threshold is
  floor(2n/3)+1, because certificates must be checkable by third parties under
  an adversarial assumption. It now has a home again --
  `urd.consensus.attest/byzantine-quorum-size` -- and this test asserts against
  BOTH that function and the inline formula, so the two cannot drift. (It was
  computed inline for a while after `urd.crypto`'s uncalled certificate layer
  was deleted and before the real one replaced it.)

  They coincide at n=4 and diverge from n=5 on. This test exists so that anyone
  who notices the discrepancy finds a deliberate, documented decision rather
  than assuming one of them is a typo -- and so that silently changing either
  one to match the other fails loudly.

  The BFT threshold's own safety property (quorum intersection: two quorums
  share more than f members) is machine-checked in ansatz as
  `quorum-intersection`, run by `clj -M:proofs`."
  []
  (prop/for-all [n (gen/choose 3 15)]
                (let [validator-set (gen/generate (gen-validator-set n))
                      cft (rr/quorum-size validator-set)
                      bft (inc (quot (* 2 n) 3))]
                  (and
                   ;; The shipped function agrees with the formula this test
                   ;; states. Without this the test would happily pass while
                   ;; `byzantine-quorum-size` said something else entirely.
                   (= bft (attest/byzantine-quorum-size n))
                   ;; The Byzantine threshold is never weaker than the CFT one.
                   (<= cft bft)
                   ;; They agree ONLY at n in #{1,2,4} (verified exhaustively).
                   ;; n=4 is the case that made the old discrepancy invisible:
                   ;; every small example in the test suite used 3 or 4 nodes.
                   (if (= n 4) (= cft bft) true)
                   ;; For EVERY n >= 5 the Byzantine threshold is strictly
                   ;; stronger. This is the assertion that matters: there is no
                   ;; cluster size above 4 where the two coincide, so the
                   ;; distinction can never be dismissed as a rounding detail.
                   (if (>= n 5) (< cft bft) true)
                   ;; Two worked examples, spelled out.
                   (if (= n 5) (and (= cft 3) (= bft 4)) true)
                   (if (= n 7) (and (= cft 4) (= bft 5)) true)))))

(defspec quorum-thresholds-are-intentionally-different 100
  (prop-quorum-thresholds-differ))

(defn prop-proposer-rotation
  "Property: Proposer rotates through all validators."
  []
  (prop/for-all [n (gen/choose 3 10)]
                (let [validator-set (gen/generate (gen-validator-set n))
                      validator-ids (sort (keys validator-set))

          ;; Get proposers for n consecutive heights
                      proposers (map #(rr/get-proposer-id % validator-set) (range n))]

                  (and
        ;; All proposers should be in validator set
                   (every? (set validator-ids) proposers)
        ;; Should cycle through all validators exactly once
                   (= (set proposers) (set validator-ids))
        ;; Should be in deterministic order
                   (= proposers validator-ids)))))

(defspec proposer-rotation-property 100
  (prop-proposer-rotation))

;; ============================================================
;; Summary and Statistics
;; ============================================================

(comment
  "Generative Test Coverage:

  1. VALIDATOR SCALING:
     - 3 validators (minimum for simple majority)
     - 5 validators (common production size)
     - 7 validators (larger network)
     - Up to 15 validators for quorum testing

  2. EVENT TYPES GENERATED:
     - proposal-received (40% frequency)
     - vote-received (30% frequency)
     - timeout (20% frequency)
     - proposal-finalized (10% frequency)

  3. FAILURE SCENARIOS:
     - Message loss (0-30%)
     - Message duplication (0-20%)
     - Message reordering
     - Combined failure modes

  4. INVARIANTS CHECKED:
     - Safety: At most one proposal per height
     - Monotonicity: Heights only increase
     - Vote counting: Correct vote aggregation
     - Quorum: Correct quorum calculation
     - Phase validity: Only valid phases
     - Proposal consistency: ID matches proposal

  5. CONSENSUS PROPERTIES:
     - Quorum scaling with validator count
     - Proposer rotation determinism
     - Multi-round completion
     - Failure resilience

  Total test cases generated: ~500+ scenarios

  To run:
    clojure -M:test -n urd.consensus.algorithms.round-robin-generative-test

  To see failures:
    (tc/quick-check 1000 (prop-random-events-maintain-invariants 5 30))

  To shrink failures:
    Test.check automatically shrinks failing cases to minimal examples")

(deftest the-agreement-invariant-can-actually-fail
  (testing "a guard nobody has watched fail is not a guard

           The predicate this replaced was
           `(= (count finalized) (count (keys finalized)))` -- true of every
           map -- and it was the only assertion in this file with `safety` in
           its name, folded into `check-all-invariants`, which is the entire
           assertion of all eight defspecs. Four hundred generated scenarios
           establishing nothing.

           So this test drives the invariant with a disagreement built by hand
           and asserts it says no, and drives it with agreement and asserts it
           says yes. The old predicate is applied to the same disagreement to
           show what it would have done."
    (let [disagreeing {:a {:state {:finalized {0 {:snapshot-id :x}}}}
                       :b {:state {:finalized {0 {:snapshot-id :y}}}}}
          agreeing    {:a {:state {:finalized {0 {:snapshot-id :x}}}}
                       :b {:state {:finalized {0 {:snapshot-id :x}}}}}
          tautology   (fn [vs]
                        (every? (fn [[_ v]]
                                  (let [f (get-in v [:state :finalized])]
                                    (= (count f) (count (keys f)))))
                                vs))]
      (is (false? (check-agreement-across-validators disagreeing))
          "two validators finalizing different proposals at one height is a
           safety violation and must be reported as one")
      (is (true? (check-agreement-across-validators agreeing))
          "and agreement must not be reported as a violation")
      (is (true? (tautology disagreeing))
          "while the predicate this replaced passed the very same disagreement,
           which is what 'could not fail' means")
      (is (true? (check-agreement-across-validators {}))
          "and no validators is not a violation, it is nothing to check"))))
