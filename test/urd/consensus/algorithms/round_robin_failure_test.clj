(ns urd.consensus.algorithms.round-robin-failure-test
  "Targeted failure tests for round-robin state machine.

  These tests verify correct behavior under adverse conditions:
  - Message loss
  - Duplicate messages
  - Out-of-order messages
  - Stale proposals
  - Minority votes
  - Timeout scenarios
  - Byzantine inputs"
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.state-machine :as sm]
            [urd.consensus.algorithms.round-robin :as rr]))

;; ============================================================
;; Test Helpers
;; ============================================================

(defn contains-effect?
  "Check if effects vector contains an effect matching pattern."
  [effects pattern]
  (when (sequential? effects)
    (let [effect-type (if (keyword? pattern) pattern (first pattern))]
      (some #(= (first %) effect-type) effects))))

(defn get-effect
  "Get first effect matching type."
  [effects effect-type]
  (first (filter #(= (first %) effect-type) effects)))

(def test-validators
  {#uuid "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa" "pubkey-a"
   #uuid "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb" "pubkey-b"
   #uuid "cccccccc-cccc-cccc-cccc-cccccccccccc" "pubkey-c"})

(def validator-a #uuid "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa")
(def validator-b #uuid "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb")
(def validator-c #uuid "cccccccc-cccc-cccc-cccc-cccccccccccc")

(def test-proposal
  {:snapshot-id #uuid "dddddddd-dddd-dddd-dddd-dddddddddddd"
   :system-id "test"
   :data "test-data"})

;; ============================================================
;; Message Loss Tests
;; ============================================================

(deftest proposal-timeout-test
  (testing "Timeout when no proposal received"
    (let [sm (rr/create test-validators)
          ;; Non-proposer validator waiting for proposal
          state (sm/initial-state sm {:peer-id validator-b})
          r1 (sm/handle-event sm state {:type :start-round})]

      ;; Should set timer
      (is (contains-effect? (:effects r1) [:set-timer]))

      ;; Timeout occurs - no proposal received
      (let [r2 (sm/handle-event sm (:state r1) {:type :timeout
                                                :timer-id :proposal-timeout})]
        ;; Round should increment
        (is (= 1 (:round (:state r2))))
        ;; Height unchanged
        (is (= 0 (:height (:state r2))))))))

(deftest minority-votes-timeout-test
  (testing "Quorum not reached - timeout advances round"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive only 1 vote (need 2 for quorum)
          r1 (sm/handle-event sm state {:type :vote-received
                                        :proposal-id (:snapshot-id test-proposal)
                                        :voter validator-b
                                        :signature "sig-b"})]

      ;; No finalization yet
      (is (not (contains-effect? (:effects r1) :finalize)))

      ;; Quorum timeout occurs
      (let [r2 (sm/handle-event sm (:state r1) {:type :timeout
                                                :timer-id :quorum-timeout})]
        ;; Round increments
        (is (= 1 (:round (:state r2))))
        ;; Still no finalization
        (is (not (contains-effect? (:effects r2) :finalize)))))))

;; ============================================================
;; Duplicate Message Tests
;; ============================================================

(deftest duplicate-proposal-ignored-test
  (testing "Duplicate proposal from same proposer is ignored"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-b})

          ;; Receive first proposal
          r1 (sm/handle-event sm state {:type :proposal-received
                                        :proposal test-proposal
                                        :height 0
                                        :round 0
                                        :sender validator-a})

          ;; State updated with proposal
          _ (is (= test-proposal (:current-proposal (:state r1))))

          ;; Receive duplicate proposal (same height/round)
          r2 (sm/handle-event sm (:state r1) {:type :proposal-received
                                              :proposal test-proposal
                                              :height 0
                                              :round 0
                                              :sender validator-a})]

      ;; Should still have same proposal
      (is (= test-proposal (:current-proposal (:state r2))))
      ;; Should not broadcast another vote
      (is (not (contains-effect? (:effects r2) :broadcast))))))

(deftest duplicate-vote-test
  (testing "Duplicate votes from same validator only count once"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote from validator-b
          r1 (sm/handle-event sm state {:type :vote-received
                                        :proposal-id (:snapshot-id test-proposal)
                                        :voter validator-b
                                        :signature "sig-b"})

          ;; Receive duplicate vote from validator-b
          r2 (sm/handle-event sm (:state r1) {:type :vote-received
                                              :proposal-id (:snapshot-id test-proposal)
                                              :voter validator-b
                                              :signature "sig-b-duplicate"})]

      ;; Should still have only one vote from validator-b
      (let [votes (get-in (:state r2) [:votes (:snapshot-id test-proposal)])]
        (is (= 1 (count (filter #(= validator-b %) votes))))))))

;; ============================================================
;; Out-of-Order Message Tests
;; ============================================================

(deftest stale-proposal-rejected-test
  (testing "Proposal from past height/round is rejected"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-b})
                    (assoc :height 2)
                    (assoc :round 1))

          ;; Receive proposal for old height
          r1 (sm/handle-event sm state {:type :proposal-received
                                        :proposal test-proposal
                                        :height 0
                                        :round 0
                                        :sender validator-a})]

      ;; State unchanged
      (is (nil? (:current-proposal (:state r1))))
      ;; Height/round unchanged
      (is (= 2 (:height (:state r1))))
      (is (= 1 (:round (:state r1))))
      ;; No vote broadcast
      (is (not (contains-effect? (:effects r1) :broadcast))))))

(deftest future-proposal-rejected-test
  (testing "Proposal from future height is rejected"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-b})

          ;; Receive proposal for future height
          r1 (sm/handle-event sm state {:type :proposal-received
                                        :proposal test-proposal
                                        :height 5
                                        :round 0
                                        :sender validator-a})]

      ;; State unchanged
      (is (nil? (:current-proposal (:state r1))))
      ;; Still at height 0
      (is (= 0 (:height (:state r1))))
      ;; No vote broadcast
      (is (not (contains-effect? (:effects r1) :broadcast))))))

(deftest stale-vote-for-old-proposal-test
  (testing "Vote for old proposal is rejected (bounded storage)"
    (let [old-proposal-id #uuid "eeeeeeee-eeee-eeee-eeee-eeeeeeeeeeee"
          sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote for different (old) proposal
          r1 (sm/handle-event sm state {:type :vote-received
                                        :proposal-id old-proposal-id
                                        :voter validator-b
                                        :signature "sig-b"})]

      ;; Vote rejected - not stored (DoS resistance)
      (is (not (contains? (:votes (:state r1)) old-proposal-id)))
      ;; Current proposal still has no votes
      (is (empty? (get-in (:state r1) [:votes (:snapshot-id test-proposal)] #{})))
      ;; No finalization
      (is (not (contains-effect? (:effects r1) :finalize)))
      ;; Log effect emitted
      (is (contains-effect? (:effects r1) :log)))))

;; ============================================================
;; Wrong Round Tests
;; ============================================================

(deftest proposal-wrong-round-rejected-test
  (testing "Proposal for wrong round at current height is rejected"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-b})
                    (assoc :round 2))

          ;; Receive proposal for round 0 at same height
          r1 (sm/handle-event sm state {:type :proposal-received
                                        :proposal test-proposal
                                        :height 0
                                        :round 0
                                        :sender validator-a})]

      ;; Proposal rejected
      (is (nil? (:current-proposal (:state r1))))
      ;; Round unchanged
      (is (= 2 (:round (:state r1))))
      ;; No vote
      (is (not (contains-effect? (:effects r1) :broadcast))))))

;; ============================================================
;; Byzantine/Invalid Input Tests
;; ============================================================

(deftest non-proposer-proposal-test
  (testing "Proposal from non-proposer validator is rejected"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-c})

          ;; Receive proposal from validator-b, but validator-a should propose at height 0
          r1 (sm/handle-event sm state {:type :proposal-received
                                        :proposal test-proposal
                                        :height 0
                                        :round 0
                                        :sender validator-b})]

      ;; Proposal rejected - state unchanged
      (is (nil? (:current-proposal (:state r1))))
      ;; Warning logged
      (is (contains-effect? (:effects r1) :log)))))

(deftest vote-from-unknown-validator-test
  (testing "Vote from validator not in validator set is rejected"
    (let [unknown-validator #uuid "ffffffff-ffff-ffff-ffff-ffffffffffff"
          sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote from unknown validator
          r1 (sm/handle-event sm state {:type :vote-received
                                        :proposal-id (:snapshot-id test-proposal)
                                        :voter unknown-validator
                                        :signature "sig-unknown"})]

      ;; Vote rejected - not added to state
      (is (not (contains? (get-in (:state r1) [:votes (:snapshot-id test-proposal)])
                          unknown-validator)))
      ;; Warning logged
      (is (contains-effect? (:effects r1) :log)))))

(deftest unknown-event-type-test
  (testing "Unknown event type is handled gracefully"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-a})

          r1 (sm/handle-event sm state {:type :bogus-event
                                        :data "invalid"})]

      ;; State unchanged
      (is (= state (:state r1)))
      ;; Log effect emitted
      (is (contains-effect? (:effects r1) :log)))))

;; ============================================================
;; Multiple Concurrent Proposals Test
;; ============================================================

(deftest multiple-proposals-same-height-test
  (testing "Multiple proposals for same height/round - first one wins"
    (let [proposal-2 {:snapshot-id #uuid "eeeeeeee-eeee-eeee-eeee-eeeeeeeeeeee"
                      :system-id "test"
                      :data "different-data"}
          sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-c})

          ;; Receive first proposal
          r1 (sm/handle-event sm state {:type :proposal-received
                                        :proposal test-proposal
                                        :height 0
                                        :round 0
                                        :sender validator-a})

          ;; Receive different proposal for same height/round
          r2 (sm/handle-event sm (:state r1) {:type :proposal-received
                                              :proposal proposal-2
                                              :height 0
                                              :round 0
                                              :sender validator-b})]

      ;; First proposal accepted
      (is (= test-proposal (:current-proposal (:state r1))))

      ;; Second proposal ignored - stick with first one
      (is (= test-proposal (:current-proposal (:state r2))))

      ;; No vote broadcast for second proposal
      (is (not (contains-effect? (:effects r2) :broadcast))))))

;; ============================================================
;; Finalization Edge Cases
;; ============================================================

(deftest finalization-clears-state-test
  (testing "Finalization clears current proposal and votes"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :votes {(:snapshot-id test-proposal) #{validator-b validator-c}}))

          r1 (sm/handle-event sm state {:type :proposal-finalized
                                        :proposal test-proposal
                                        :height 0})]

      ;; Height incremented
      (is (= 1 (:height (:state r1))))
      ;; Round reset
      (is (= 0 (:round (:state r1))))
      ;; Current proposal cleared
      (is (nil? (:current-proposal (:state r1))))
      (is (nil? (:current-proposal-id (:state r1))))
      ;; Finalized recorded
      (is (= test-proposal (get-in (:state r1) [:finalized 0]))))))

(deftest finalization-wrong-height-test
  (testing "Finalization event for wrong height"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :height 2)
                    (assoc :current-proposal test-proposal))

          ;; Finalize event for old height
          r1 (sm/handle-event sm state {:type :proposal-finalized
                                        :proposal test-proposal
                                        :height 0})]

      ;; State machine correctly ignores old finalization
      ;; Height should remain unchanged
      (is (= 2 (:height (:state r1)))
          "Should ignore finalization for old height"))))

;; ============================================================
;; Round Advancement Tests
;; ============================================================

(deftest multiple-timeouts-test
  (testing "Multiple consecutive timeouts advance round correctly"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-b})

          ;; First timeout
          r1 (sm/handle-event sm state {:type :timeout :timer-id :proposal-timeout})
          _ (is (= 1 (:round (:state r1))))

          ;; Second timeout
          r2 (sm/handle-event sm (:state r1) {:type :timeout :timer-id :proposal-timeout})
          _ (is (= 2 (:round (:state r2))))

          ;; Third timeout
          r3 (sm/handle-event sm (:state r2) {:type :timeout :timer-id :proposal-timeout})]

      (is (= 3 (:round (:state r3))))
      (is (= 0 (:height (:state r3)))))))

;; ============================================================
;; Summary
;; ============================================================

(comment
  "Failure scenarios covered:

  MESSAGE LOSS:
  - Proposal timeout (no proposal received)
  - Quorum timeout (insufficient votes)

  DUPLICATE MESSAGES:
  - Duplicate proposals
  - Duplicate votes

  OUT-OF-ORDER:
  - Stale proposals (past height/round)
  - Future proposals (ahead of current height)
  - Stale votes for old proposals

  WRONG ROUND:
  - Proposals for wrong round at same height

  BYZANTINE/INVALID:
  - Proposal from non-proposer
  - Votes from unknown validators
  - Unknown event types
  - Multiple concurrent proposals

  EDGE CASES:
  - Finalization state cleanup
  - Finalization for wrong height
  - Multiple consecutive timeouts

  TODO (future enhancements):
  - Proposer identity validation
  - Unknown validator vote filtering
  - Signature verification in state machine
  - More sophisticated multi-proposal handling")
