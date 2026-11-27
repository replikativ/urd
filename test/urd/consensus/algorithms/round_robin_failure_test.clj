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
            [urd.consensus.node :as n]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.algorithms.round-robin-test :refer [landed-step]]))

;; ============================================================
;; Test Helpers
;; ============================================================

(def ^:private test-atts (rr/test-attestations))

(defn attest
  "An attestation over `rr/vote-payload`, which binds the HEIGHT as well as the
  proposal id. Built through the algorithm's own function so a test cannot
  drift from what it signs."
  ([voter pid] (attest voter 0 pid))
  ([voter height pid]
   ((:sign-vote test-atts) voter (rr/vote-payload {:height height} pid))))

(defn attested
  "Voter ids -> the `{:voter :att}` pairs `:vote-bundle` and `:catchup` carry."
  ([pid voters] (attested pid 0 voters))
  ([pid height voters]
   (mapv (fn [v] {:voter v :att (attest v height pid)}) voters)))

(defn ->input
  "Translate a legacy event map into a core-protocol input.

  These tests were written against the old `ConsensusAlgorithm` protocol, whose
  events were `:proposal-received`, `:vote-received`, `:start-round` and so on.
  The algorithm now takes `:message-received`, `:timer-fired` and `:value-ready`.
  Translating here rather than rewriting each test keeps every assertion, and
  what it asserts, exactly as it was -- these are tests of the algorithm, not of
  the calling convention."
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
                                 (attest (:voter event) (:proposal-id event)))}}
    :proposal-finalized {:type :message-received
                         :from (:sender event)
                         :msg {:kind :finalized :proposal (:proposal event)
                               :height (:height event)}}
    :proposal-catchup {:type :message-received
                       :from (:sender event)
                       :msg {:kind :catchup :proposal (:proposal event)
                             :height (:height event) :round (:round event)
                             :votes (:votes event)}}
    :state-sync-response {:type :message-received
                          :from (:sender event)
                          :msg {:kind :state-sync-response
                                :finalized (:finalized event)
                                ;; The earliest height the responder still
                                ;; retains: a peer below it cannot be caught up
                                ;; by that responder at all.
                                :oldest (:oldest event)
                                :current-height (:current-height event)}}
    :vote-bundle {:type :message-received
                  :from (:sender event)
                  :msg {:kind :vote-bundle :proposal-id (:proposal-id event)
                        :votes (:votes event)}}
    event))

(defn handle-event [impl state event] (landed-step impl state (->input event)))

(defn initial-state [impl config]
  ;; Attestations are REQUIRED by `init`: a vote here is relayed, so the peer
  ;; handing us one is usually not its author.
  (:state (n/init impl (merge test-atts
                              (update config :validators
                                      (fn [v] (or v (vec (keys (:validator-set impl))))))))))

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
          state (initial-state sm {:peer-id validator-b})
          r1 (handle-event sm state {:type :start-round})]

      ;; Should set timer
      (is (contains-effect? (:effects r1) [:set-timer]))

      ;; Timeout occurs - no proposal received
      (let [r2 (handle-event sm (:state r1) {:type :timeout
                                             :timer-id :proposal-timeout})]
        ;; Round should increment
        ;; The round no longer advances on timeout. It selects nothing here --
      ;; `get-proposer-id` takes the height alone, which is what makes a majority
      ;; quorum safe without locking -- so bumping it only narrowed which
      ;; proposals this node would accept, and a validator that missed the
      ;; broadcast then refused the very proposal it was waiting for. A timeout
      ;; re-asks and re-arms instead. See `valid-proposal?`.
        (is (= 0 (:round (:state r2))) "the round does not move")
        ;; Height unchanged
        (is (= 0 (:height (:state r2))))))))

(deftest minority-votes-timeout-test
  (testing "Quorum not reached - timeout advances round"
    (let [sm (rr/create test-validators)
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive only 1 vote (need 2 for quorum)
          r1 (handle-event sm state {:type :vote-received
                                     :proposal-id (:snapshot-id test-proposal)
                                     :voter validator-b
                                     :signature "sig-b"})]

      ;; No finalization yet
      (is (not (contains-effect? (:effects r1) :commit)))

      ;; Quorum timeout occurs
      (let [r2 (handle-event sm (:state r1) {:type :timeout
                                             :timer-id :quorum-timeout})]
        ;; Round increments
        ;; The round no longer advances on timeout. It selects nothing here --
      ;; `get-proposer-id` takes the height alone, which is what makes a majority
      ;; quorum safe without locking -- so bumping it only narrowed which
      ;; proposals this node would accept, and a validator that missed the
      ;; broadcast then refused the very proposal it was waiting for. A timeout
      ;; re-asks and re-arms instead. See `valid-proposal?`.
        (is (= 0 (:round (:state r2))) "the round does not move")
        ;; Still no finalization
        (is (not (contains-effect? (:effects r2) :commit)))))))

;; ============================================================
;; Duplicate Message Tests
;; ============================================================

(deftest duplicate-proposal-ignored-test
  (testing "Duplicate proposal from same proposer is ignored"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-b})

          ;; Receive first proposal
          r1 (handle-event sm state {:type :proposal-received
                                     :proposal test-proposal
                                     :height 0
                                     :round 0
                                     :sender validator-a})

          ;; State updated with proposal
          _ (is (= test-proposal (:current-proposal (:state r1))))

          ;; Receive duplicate proposal (same height/round)
          r2 (handle-event sm (:state r1) {:type :proposal-received
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
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote from validator-b
          r1 (handle-event sm state {:type :vote-received
                                     :proposal-id (:snapshot-id test-proposal)
                                     :voter validator-b
                                     :signature "sig-b"})

          ;; Receive duplicate vote from validator-b
          r2 (handle-event sm (:state r1) {:type :vote-received
                                           :proposal-id (:snapshot-id test-proposal)
                                           :voter validator-b
                                           :signature "sig-b-duplicate"})]

      ;; Should still have only one vote from validator-b
      (let [votes (get-in (:state r2) [:votes (:snapshot-id test-proposal)])]
        ;; `:votes` is now `{voter attestation}` rather than a set of names.
        (is (= 1 (count (filter #(= validator-b (key %)) votes))))))))

;; ============================================================
;; Out-of-Order Message Tests
;; ============================================================

(deftest stale-proposal-rejected-test
  (testing "Proposal from past height/round is rejected"
    (let [sm (rr/create test-validators)
          state (-> (initial-state sm {:peer-id validator-b})
                    (assoc :height 2)
                    (assoc :round 1))

          ;; Receive proposal for old height
          r1 (handle-event sm state {:type :proposal-received
                                     :proposal test-proposal
                                     :height 0
                                     :round 0
                                     :sender validator-a})]

      ;; State unchanged
      (is (nil? (:current-proposal (:state r1))))
      ;; Height/round unchanged
      (is (= 2 (:height (:state r1))))
      (is (= 1 (:round (:state r1))) "unchanged -- this node was set up at round 1")
      ;; No vote broadcast
      (is (not (contains-effect? (:effects r1) :broadcast))))))

(deftest future-proposal-rejected-test
  (testing "Proposal from future height is rejected"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-b})

          ;; Receive proposal for future height
          r1 (handle-event sm state {:type :proposal-received
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
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote for different (old) proposal
          r1 (handle-event sm state {:type :vote-received
                                     :proposal-id old-proposal-id
                                     :voter validator-b
                                     :signature "sig-b"})]

      ;; Vote rejected - not stored (DoS resistance)
      (is (not (contains? (:votes (:state r1)) old-proposal-id)))
      ;; Current proposal still has no votes
      (is (empty? (get-in (:state r1) [:votes (:snapshot-id test-proposal)] #{})))
      ;; No finalization
      (is (not (contains-effect? (:effects r1) :commit)))
      ;; Log effect emitted
      (is (contains-effect? (:effects r1) :log)))))

;; ============================================================
;; Wrong Round Tests
;; ============================================================

(deftest proposal-wrong-round-rejected-test
  (testing "Proposal for wrong round at current height is rejected"
    (let [sm (rr/create test-validators)
          state (-> (initial-state sm {:peer-id validator-b})
                    (assoc :round 2))

          ;; Receive proposal for round 0 at same height
          r1 (handle-event sm state {:type :proposal-received
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
          state (initial-state sm {:peer-id validator-c})

          ;; Receive proposal from validator-b, but validator-a should propose at height 0
          r1 (handle-event sm state {:type :proposal-received
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
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote from unknown validator
          r1 (handle-event sm state {:type :vote-received
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
          state (initial-state sm {:peer-id validator-a})

          r1 (handle-event sm state {:type :bogus-event
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
          state (initial-state sm {:peer-id validator-c})

          ;; Receive first proposal
          r1 (handle-event sm state {:type :proposal-received
                                     :proposal test-proposal
                                     :height 0
                                     :round 0
                                     :sender validator-a})

          ;; Receive different proposal for same height/round
          r2 (handle-event sm (:state r1) {:type :proposal-received
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
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :votes {(:snapshot-id test-proposal) #{validator-b validator-c}}))

          r1 (handle-event sm state {:type :proposal-finalized
                                     :sender validator-b
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
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :height 2)
                    (assoc :current-proposal test-proposal))

          ;; Finalize event for old height
          r1 (handle-event sm state {:type :proposal-finalized
                                     :sender validator-b
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
  (testing "Multiple consecutive timeouts retransmit and leave the round alone"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-b})

          ;; First timeout
          r1 (handle-event sm state {:type :timeout :timer-id :proposal-timeout})
          ;; The round no longer advances on timeout -- it selects nothing, since
          ;; `get-proposer-id` takes the height alone. A timeout retransmits and
          ;; re-arms instead. See `valid-proposal?`.
          _ (is (= 0 (:round (:state r1))) "no round advance on the first timeout")

          ;; Second timeout
          r2 (handle-event sm (:state r1) {:type :timeout :timer-id :proposal-timeout})
          _ (is (= 0 (:round (:state r2))) "nor on the second")

          ;; Third timeout
          r3 (handle-event sm (:state r2) {:type :timeout :timer-id :proposal-timeout})]

      (is (= 0 (:round (:state r3))) "nor the third -- it retransmits instead")
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

;; ============================================================
;; The stranded node
;; ============================================================

(deftest behind-peer-asking-for-an-old-height-is-told-where-we-are
  (testing "a want-proposal below our height is answered, not ignored"
    ;; This used to return no effects at all. The silence is what stranded a
    ;; node permanently: the ONLY trigger for catch-up is receiving a
    ;; finalization, finalizations are broadcast exactly once, and a node that
    ;; missed that one has nothing else that can ever tell it it is behind.
    (let [impl (rr/create test-validators)
          state (assoc (initial-state impl {:peer-id validator-a})
                       :height 7
                       :finalized {0 test-proposal 1 test-proposal})
          {:keys [effects]} (landed-step impl state
                                         {:type :message-received
                                          :from validator-c
                                          :msg {:kind :want-proposal :height 2 :round 0}})
          send-fx (get-effect effects :send)]
      (is (some? send-fx) "a peer behind us must get an answer")
      (is (= validator-c (:to (second send-fx))) "addressed to the asker, not broadcast")
      (let [msg (:msg (second send-fx))]
        (is (= :state-sync-response (:kind msg)))
        (is (= 7 (:current-height msg)) "which tells it how far behind it is")
        ;; FROM the height it asked about, not our whole map. It is at 2 and
        ;; has no use for 0 and 1; `:finalized` is bounded to ten heights, so
        ;; spending the answer on history the asker already has is exactly how
        ;; a far-behind peer got a reply full of heights it could not use.
        (is (= {} (:finalized msg)))
        (is (= 0 (:oldest msg))
            "and the earliest height we can still serve, so a peer below it
             learns that we cannot catch it up at all")))))

(deftest a-state-sync-answer-starts-at-the-height-that-was-asked-for
  (let [impl (rr/create test-validators)
        state (assoc (initial-state impl {:peer-id validator-a})
                     :height 9
                     :finalized (into {} (map (fn [h] [h {:snapshot-id [:p h]}]))
                                      (range 3 9)))
        answer (fn [from]
                 (let [{:keys [effects]} (landed-step impl state
                                                      {:type :message-received
                                                       :from validator-c
                                                       :msg {:kind :state-sync :from from}})]
                   (:msg (second (get-effect effects :send)))))]
    (is (= (set (range 3 9)) (set (keys (:finalized (answer 0)))))
        "a peer at 0 gets everything we hold")
    (is (= (set (range 6 9)) (set (keys (:finalized (answer 6)))))
        "a peer at 6 gets only what it is missing")
    (is (= 3 (:oldest (answer 0)))
        "and is told the earliest height we retain -- it is below 3, so this
         answer cannot close its gap and it needs to know")))

(deftest want-proposal-for-a-future-height-is-still-ignored
  (testing "we cannot help a peer that is ahead of us"
    (let [impl (rr/create test-validators)
          state (assoc (initial-state impl {:peer-id validator-a}) :height 3)
          {:keys [effects]} (landed-step impl state
                                         {:type :message-received
                                          :from validator-c
                                          :msg {:kind :want-proposal :height 9 :round 0}})]
      (is (nil? (get-effect effects :send))
          "answering with our lower height would only mislead it"))))

(deftest a-node-that-missed-every-finalization-still-recovers
  (testing "end to end: stranded at 0, asks, is told, syncs, commits"
    (let [impl (rr/create test-validators)
          ;; The stranded node: at height 0, no proposal, nothing finalized --
          ;; exactly the state measured over kabel, where such a node received
          ;; 105 want-proposals and nothing else for twenty seconds.
          stranded (initial-state impl {:peer-id validator-c})
          ;; A peer well ahead answers its timeout.
          ahead (assoc (initial-state impl {:peer-id validator-a})
                       :height 3
                       :finalized {0 test-proposal 1 test-proposal 2 test-proposal})
          {ahead-fx :effects} (landed-step impl ahead
                                           {:type :message-received
                                            :from validator-c
                                            :msg {:kind :want-proposal
                                                  :height (:height stranded) :round 0}})
          reply (:msg (second (get-effect ahead-fx :send)))
          {caught :state caught-fx :effects}
          (landed-step impl stranded {:type :message-received :from validator-a :msg reply})]
      (is (= 3 (:height caught)) "the stranded node is carried to the peer's height")
      (is (= 3 (count (filter #(= :commit (first %)) caught-fx)))
          "and commits every height it had missed, in order")
      (is (= [0 1 2] (sort (keys (:finalized caught))))))))
