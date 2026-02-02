(ns urd.consensus.algorithms.round-robin-test
  "Pure deterministic tests for round-robin state machine."
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
  "Test validator set"
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
;; State Machine Tests
;; ============================================================

(deftest proposer-selection-test
  (testing "Proposer rotates by height"
    (let [sm (rr/create test-validators)]
      ;; Height 0: first validator (sorted) is proposer
      (is (= validator-a (rr/get-proposer-id 0 test-validators)))
      ;; Height 1: second validator
      (is (= validator-b (rr/get-proposer-id 1 test-validators)))
      ;; Height 2: third validator
      (is (= validator-c (rr/get-proposer-id 2 test-validators)))
      ;; Height 3: wraps around
      (is (= validator-a (rr/get-proposer-id 3 test-validators))))))

(deftest quorum-calculation-test
  (testing "Quorum is simple majority"
    ;; 3 validators: need 2 votes
    (is (= 2 (rr/quorum-size test-validators)))
    ;; 4 validators: need 3 votes
    (is (= 3 (rr/quorum-size (assoc test-validators
                                    #uuid "dddddddd-dddd-dddd-dddd-dddddddddddd"
                                    "pubkey-d"))))))

(deftest initial-state-test
  (testing "Initial state is correct"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-a})]
      (is (= 0 (:height state)))
      (is (= 0 (:round state)))
      (is (= :proposing (:phase state)))
      (is (nil? (:current-proposal state)))
      (is (empty? (:votes state)))
      (is (empty? (:finalized state))))))

(deftest proposer-start-round-test
  (testing "Proposer starts round by requesting proposal"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-a})
          {:keys [state effects]} (sm/handle-event sm state {:type :start-round})]

      ;; State transitions to proposing
      (is (= :proposing (:phase state)))

      ;; Effects include request-proposal and timer
      (is (contains-effect? effects [:request-proposal]))
      (is (contains-effect? effects [:set-timer])))))

(deftest validator-start-round-test
  (testing "Validator starts round by waiting for proposal"
    (let [sm (rr/create test-validators)
          ;; Validator B starts at height 0 (A is proposer)
          state (sm/initial-state sm {:peer-id validator-b})
          {:keys [state effects]} (sm/handle-event sm state {:type :start-round})]

      ;; State transitions to voting
      (is (= :voting (:phase state)))

      ;; Effects include timer
      (is (contains-effect? effects [:set-timer])))))

(deftest proposal-broadcast-test
  (testing "Proposer broadcasts proposal when ready"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-a})
          ;; Start round
          r1 (sm/handle-event sm state {:type :start-round})
          ;; Provide proposal
          r2 (sm/handle-event sm (:state r1) {:type :proposal-ready
                                              :proposal test-proposal})]

      ;; State updated with proposal
      (is (= test-proposal (:current-proposal (:state r2))))
      (is (= (:snapshot-id test-proposal) (:current-proposal-id (:state r2))))
      (is (= :voting (:phase (:state r2))))

      ;; Broadcast effect emitted
      (let [broadcast (get-effect (:effects r2) :broadcast)]
        (is (not (nil? broadcast)))
        (is (= :proposals (get-in broadcast [1 :topic])))
        (is (= test-proposal (get-in broadcast [1 :payload :proposal])))))))

(deftest validator-receives-proposal-test
  (testing "Validator receives and votes on proposal"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-b})
          ;; Receive proposal from validator A
          {:keys [state effects]} (sm/handle-event sm state
                                                   {:type :proposal-received
                                                    :proposal test-proposal
                                                    :height 0
                                                    :round 0
                                                    :sender validator-a})]

      ;; State updated
      (is (= test-proposal (:current-proposal state)))
      (is (= :voting (:phase state)))

      ;; Vote broadcast emitted
      (let [broadcast (get-effect effects :broadcast)]
        (is (not (nil? broadcast)))
        (is (= :votes (get-in broadcast [1 :topic])))
        (is (= (:snapshot-id test-proposal)
               (get-in broadcast [1 :payload :proposal-id])))))))

(deftest stale-proposal-ignored-test
  (testing "Stale proposal (wrong height/round) is ignored"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-b})
          ;; Receive proposal for wrong height
          {:keys [state effects]} (sm/handle-event sm state
                                                   {:type :proposal-received
                                                    :proposal test-proposal
                                                    :height 99
                                                    :round 0
                                                    :sender validator-a})]

      ;; State unchanged
      (is (nil? (:current-proposal state)))

      ;; No broadcast
      (is (not (contains-effect? effects :broadcast))))))

(deftest quorum-reached-test
  (testing "Quorum triggers finalization"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote 1
          r1 (sm/handle-event sm state {:type :vote-received
                                        :proposal-id (:snapshot-id test-proposal)
                                        :voter validator-b
                                        :signature "sig-b"})

          ;; Not yet quorum (need 2 votes)
          _ (is (not (contains-effect? (:effects r1) :finalize)))

          ;; Receive vote 2
          r2 (sm/handle-event sm (:state r1) {:type :vote-received
                                              :proposal-id (:snapshot-id test-proposal)
                                              :voter validator-c
                                              :signature "sig-c"})]

      ;; Quorum reached - finalize effect emitted
      (is (contains-effect? (:effects r2) :finalize))
      (is (= :finalizing (:phase (:state r2)))))))

(deftest finalization-advances-height-test
  (testing "Finalization moves to next height"
    (let [sm (rr/create test-validators)
          state (-> (sm/initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :height 0))

          {:keys [state effects]} (sm/handle-event sm state
                                                   {:type :proposal-finalized
                                                    :proposal test-proposal
                                                    :height 0})]

      ;; Height advanced
      (is (= 1 (:height state)))
      ;; Round reset
      (is (= 0 (:round state)))
      ;; Proposal recorded
      (is (= test-proposal (get-in state [:finalized 0])))
      ;; Current proposal cleared
      (is (nil? (:current-proposal state))))))

(deftest timeout-advances-round-test
  (testing "Timeout increments round"
    (let [sm (rr/create test-validators)
          state (sm/initial-state sm {:peer-id validator-a})

          {:keys [state effects]} (sm/handle-event sm state
                                                   {:type :timeout
                                                    :timer-id :proposal-timeout})]

      ;; Round incremented
      (is (= 1 (:round state)))
      ;; Height unchanged
      (is (= 0 (:height state))))))

(deftest complete-consensus-scenario-test
  (testing "Complete consensus round with 3 validators"
    (let [sm (rr/create test-validators)

          ;; Validator A (proposer) starts
          s0-a (sm/initial-state sm {:peer-id validator-a})
          r1-a (sm/handle-event sm s0-a {:type :start-round})
          _ (is (contains-effect? (:effects r1-a) [:request-proposal]))

          ;; A broadcasts proposal
          r2-a (sm/handle-event sm (:state r1-a) {:type :proposal-ready
                                                  :proposal test-proposal})
          _ (is (contains-effect? (:effects r2-a) :broadcast))

          ;; Validator B receives and votes
          s0-b (sm/initial-state sm {:peer-id validator-b})
          r1-b (sm/handle-event sm s0-b {:type :proposal-received
                                         :proposal test-proposal
                                         :height 0
                                         :round 0
                                         :sender validator-a})
          _ (is (contains-effect? (:effects r1-b) :broadcast))

          ;; Validator C receives and votes
          s0-c (sm/initial-state sm {:peer-id validator-c})
          r1-c (sm/handle-event sm s0-c {:type :proposal-received
                                         :proposal test-proposal
                                         :height 0
                                         :round 0
                                         :sender validator-a})

          ;; A receives vote from B (has 1 vote: self)
          r3-a (sm/handle-event sm (:state r2-a) {:type :vote-received
                                                  :proposal-id (:snapshot-id test-proposal)
                                                  :voter validator-b
                                                  :signature "sig-b"})
          _ (is (not (contains-effect? (:effects r3-a) :finalize)))

          ;; A receives vote from C (has 2 votes: quorum!)
          r4-a (sm/handle-event sm (:state r3-a) {:type :vote-received
                                                  :proposal-id (:snapshot-id test-proposal)
                                                  :voter validator-c
                                                  :signature "sig-c"})]

      ;; Quorum reached - finalize
      (is (contains-effect? (:effects r4-a) :finalize))
      (is (= :finalizing (:phase (:state r4-a)))))))
