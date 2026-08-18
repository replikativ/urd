(ns urd.consensus.algorithms.round-robin-test
  "Pure deterministic tests for round-robin state machine."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.node :as n]
            [urd.consensus.sim :as sim]
            [urd.consensus.apphash :as ah]
            [urd.consensus.algorithms.round-robin :as rr]))

(defn- rr-apphash-checker
  "An app-hash `:valid-fn` for a node whose application state digest is `h`."
  [h]
  (ah/checker (constantly h)))

(def ^:private test-atts (rr/test-attestations))

(defn attest
  "A verifying attestation for `voter` over `pid` at `height`, from the test
  scheme.

  Builds the payload through `rr/vote-payload` rather than assembling
  `[height pid]` here, so a test cannot drift from what the algorithm actually
  signs -- which is the whole failure mode this helper exists to avoid.

  `height` defaults to 0 because almost every test in this file drives a node
  from genesis; the tests that advance first pass it explicitly."
  ([voter pid] (attest voter 0 pid))
  ([voter height pid]
   ((:sign-vote test-atts) voter (rr/vote-payload {:height height} pid))))

(defn attested
  "Turn a collection of voter ids into the `{:voter :att}` pairs that
  `:vote-bundle` and `:catchup` now carry.

  Those messages used to relay bare names, which is a claim by the RELAYER
  rather than evidence about the voters -- one peer could hand a node a full
  quorum it had invented."
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
                          ;; Honest by default, forgeable on purpose: pass
                          ;; `:att` to send something that does not verify.
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

(defn handle-event
  "`handle-event`, in the new protocol's terms."
  [impl state event]
  (n/step impl state (->input event)))

(defn initial-state
  "`initial-state`, in the new protocol's terms.

  Attestations are merged in here rather than at every call site. `init` now
  REFUSES to start without them: a vote in this algorithm is RELAYED --
  `:vote-bundle` and `:catchup` exist to carry other nodes' votes -- so the
  peer handing us one is usually not its author, and a bundle of bare names is
  a claim by the relayer rather than evidence about the voters."
  [impl config]
  (:state (n/init impl (merge (rr/test-attestations)
                              (update config :validators
                                      (fn [v] (or v (vec (keys (:validator-set impl))))))))))

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
          state (initial-state sm {:peer-id validator-a})]
      (is (= 0 (:height state)))
      (is (= 0 (:round state)))
      (is (= :proposing (:phase state)))
      (is (nil? (:current-proposal state)))
      (is (empty? (:votes state)))
      (is (empty? (:finalized state))))))

(deftest proposer-start-round-test
  (testing "Proposer starts round by requesting proposal"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-a})
          {:keys [state effects]} (handle-event sm state {:type :start-round})]

      ;; State transitions to proposing
      (is (= :proposing (:phase state)))

      ;; Effects include request-proposal and timer
      (is (contains-effect? effects [:request-value]))
      (is (contains-effect? effects [:set-timer])))))

(deftest validator-start-round-test
  (testing "Validator starts round by waiting for proposal"
    (let [sm (rr/create test-validators)
          ;; Validator B starts at height 0 (A is proposer)
          state (initial-state sm {:peer-id validator-b})
          {:keys [state effects]} (handle-event sm state {:type :start-round})]

      ;; State transitions to voting
      (is (= :voting (:phase state)))

      ;; Effects include timer
      (is (contains-effect? effects [:set-timer])))))

(deftest proposal-broadcast-test
  (testing "Proposer broadcasts proposal when ready"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-a})
          ;; Start round
          r1 (handle-event sm state {:type :start-round})
          ;; Provide proposal
          r2 (handle-event sm (:state r1) {:type :proposal-ready
                                           :proposal test-proposal})]

      ;; State updated with proposal
      (is (= test-proposal (:current-proposal (:state r2))))
      (is (= (:snapshot-id test-proposal) (:current-proposal-id (:state r2))))
      (is (= :voting (:phase (:state r2))))

      ;; Broadcast effect emitted
      (let [broadcast (get-effect (:effects r2) :broadcast)]
        (is (not (nil? broadcast)))
        (is (= :proposals (get-in broadcast [1 :topic])))
        (is (= test-proposal (get-in broadcast [1 :msg :proposal])))))))

(deftest validator-receives-proposal-test
  (testing "Validator receives and votes on proposal"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-b})
          ;; Receive proposal from validator A
          {:keys [state effects]} (handle-event sm state
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
               (get-in broadcast [1 :msg :proposal-id])))))))

(deftest stale-proposal-ignored-test
  (testing "Stale proposal (wrong height/round) is ignored"
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-b})
          ;; Receive proposal for wrong height
          {:keys [state effects]} (handle-event sm state
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
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :current-proposal-id (:snapshot-id test-proposal))
                    (assoc :phase :voting))

          ;; Receive vote 1
          r1 (handle-event sm state {:type :vote-received
                                     :proposal-id (:snapshot-id test-proposal)
                                     :voter validator-b
                                     :signature "sig-b"})

          ;; Not yet quorum (need 2 votes)
          _ (is (not (contains-effect? (:effects r1) :commit)))

          ;; Receive vote 2
          r2 (handle-event sm (:state r1) {:type :vote-received
                                           :proposal-id (:snapshot-id test-proposal)
                                           :voter validator-c
                                           :signature "sig-c"})]

      ;; Quorum reached - finalize effect emitted
      (is (contains-effect? (:effects r2) :commit))
      ;; Reaching quorum commits AND advances in the one transition. It used to
      ;; sit in `:finalizing` waiting for the runtime to hand back a
      ;; `:proposal-finalized` event, which is a design that cannot be reasoned
      ;; about locally -- and which stalls outright on a protocol that has no
      ;; such loop-back.
      (is (= :proposing (:phase (:state r2))) "advanced, not parked in :finalizing")
      (is (= 1 (:height (:state r2))) "and the height moved"))))

(deftest finalization-advances-height-test
  (testing "Finalization moves to next height"
    (let [sm (rr/create test-validators)
          state (-> (initial-state sm {:peer-id validator-a})
                    (assoc :current-proposal test-proposal)
                    (assoc :height 0))

          {:keys [state effects]} (handle-event sm state
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

(deftest timeout-retransmits-and-does-not-advance-the-round
  (testing "the round is NOT incremented, and that is the fix rather than the
            regression.

            The round selects nothing here -- `get-proposer-id` takes the height
            alone, which is what makes a majority quorum safe without locking --
            so bumping it only narrowed which proposals this node would accept.
            A validator that missed the broadcast bumped its round and then
            refused the very proposal it was waiting for, while the proposer
            never sent another. Measured before the fix: 5 nodes at 30% loss
            committed nothing at all in 300 ticks.

            A timeout now re-asks and re-arms."
    (let [sm (rr/create test-validators)
          state (initial-state sm {:peer-id validator-a})

          {:keys [state effects]} (handle-event sm state
                                                {:type :timeout
                                                 :timer-id :proposal-timeout})]

      (is (= 0 (:round state)) "the round does not move")
      (is (= 0 (:height state)))
      (is (contains-effect? effects :set-timer) "and the timer is re-armed"))))

(deftest complete-consensus-scenario-test
  (testing "Complete consensus round with 3 validators"
    (let [sm (rr/create test-validators)

          ;; Validator A (proposer) starts
          s0-a (initial-state sm {:peer-id validator-a})
          r1-a (handle-event sm s0-a {:type :start-round})
          _ (is (contains-effect? (:effects r1-a) [:request-value]))

          ;; A broadcasts proposal
          r2-a (handle-event sm (:state r1-a) {:type :proposal-ready
                                               :proposal test-proposal})
          _ (is (contains-effect? (:effects r2-a) :broadcast))

          ;; Validator B receives and votes
          s0-b (initial-state sm {:peer-id validator-b})
          r1-b (handle-event sm s0-b {:type :proposal-received
                                      :proposal test-proposal
                                      :height 0
                                      :round 0
                                      :sender validator-a})
          _ (is (contains-effect? (:effects r1-b) :broadcast))

          ;; Validator C receives and votes
          s0-c (initial-state sm {:peer-id validator-c})
          r1-c (handle-event sm s0-c {:type :proposal-received
                                      :proposal test-proposal
                                      :height 0
                                      :round 0
                                      :sender validator-a})

          ;; A receives the vote from B. With 3 validators the majority is 2,
          ;; and A's OWN vote is already counted -- it is recorded in state when
          ;; A broadcasts, rather than emitted as an `:add-own-vote` effect for a
          ;; runtime to remember on A's behalf. So this is the quorum.
          r3-a (handle-event sm (:state r2-a) {:type :vote-received
                                               :proposal-id (:snapshot-id test-proposal)
                                               :voter validator-b
                                               :signature "sig-b"})
          _ (is (contains-effect? (:effects r3-a) :commit)
                "quorum at 2 of 3, counting our own vote")

          ;; A further vote arrives after the decision. A has already advanced,
          ;; so it is a vote for a height that is behind and is ignored.
          r4-a (handle-event sm (:state r3-a) {:type :vote-received
                                               :proposal-id (:snapshot-id test-proposal)
                                               :voter validator-c
                                               :signature "sig-c"})]

      (is (not (contains-effect? (:effects r4-a) :commit))
          "a late vote must not commit the same height twice")
      ;; Committing ADVANCES, in the one transition. It used to park in
      ;; `:finalizing` until the runtime handed back a `:proposal-finalized`
      ;; event -- a round trip through the algorithm's own runtime, which the
      ;; core protocol has no way to express and should not.
      (is (= :proposing (:phase (:state r3-a))))
      (is (= 1 (:height (:state r3-a)))))))

;; ============================================================
;; On the simulator
;;
;; The whole point of the port: round-robin now gets the same harness the other
;; six algorithms have -- logical time, seeded schedules, fault injection.
;; ============================================================

(def sim-peers [:a :b :c :d :e])

(defn- sim-with [n cfg]
  (let [ps (vec (take n sim-peers))]
    (sim/make {:seed 1
               :nodes (zipmap ps (repeat (rr/create)))
               :node-config (zipmap ps (repeat (rr/test-attestations)))
               :config (merge {:value-fn (fn [_ p ctx]
                                           {:snapshot-id [p (:height ctx)] :payload :x})}
                              cfg)})))

(deftest the-proposer-rotates-by-height
  (let [s (sim/run (sim-with 3 {}) 120)
        committed (sim/committed s :a)]
    (is (sim/agreement? s))
    (is (< 10 (count committed)) "many heights decided")
    (is (= [[:a 0] [:b 1] [:c 2] [:a 3]]
           (mapv :snapshot-id (take 4 committed)))
        "the proposer rotates by HEIGHT, so the decided values cycle a, b, c")))

(deftest progress-survives-message-loss
  (testing "and this is the fix, measured.

            Before the timeout was changed to retransmit, five nodes at 30% loss
            committed NOTHING in 300 ticks: a validator that missed the proposal
            bumped its round, then refused the proposal it was waiting for, and
            the proposer never sent another."
    (doseq [rate [0.3 0.5]]
      (let [s (sim/run (sim-with 5 {:drop-rate rate}) 300)
            counts (mapv count (vals (sim/all-committed s)))]
        (is (sim/agreement? s) (str "agreement at " rate))
        (is (every? pos? counts) (str "progress at " rate ": " counts))))))

(deftest a-crashed-proposer-halts-the-chain
  (testing "the algorithm's real limitation, pinned rather than hidden.

            One proposer per height and no view change is exactly what makes a
            majority quorum safe here without locking -- but it means a single
            crashed validator stops the chain within n heights, at the first
            height that validator was due to propose. The round bump that looks
            like a view change is not one: `get-proposer-id` takes the height
            alone.

            Anyone reaching for this algorithm for a datahike writer needs to
            know that. It is a CFT reference, not a highly-available one."
    (let [s (-> (sim-with 3 {}) (sim/run 60) (sim/crash :c) (sim/run 400))
          live (mapv #(count (sim/committed s %)) [:a :b])
          stalled-at (apply max live)]
      (is (sim/agreement? s))
      (is (= 2 (mod stalled-at 3))
          (str "stalls at the first height :c is due to propose, got " stalled-at))
      ;; And it really is stuck, not merely slow.
      (let [s' (sim/run s 400)]
        (is (= live (mapv #(count (sim/committed s' %)) [:a :b]))
            "another 400 ticks changes nothing")))))

(deftest a-node-one-height-behind-catches-up
  (testing "the off-by-one, and it is the common case.

            `handle-finalization` asked for a state sync only when it was TWO or
            more heights behind: `(> height (inc (:height state)))`. A node
            exactly one behind -- miss a single finalization and you are there --
            fell into the branch that logs `already finalized` and does nothing.

            And it cannot recover on its own. It refuses every proposal for the
            next height, because `valid-proposal?` requires exact height
            equality; the finalizations that would carry it forward land in that
            same dead branch; and its `:want-proposal` requests are answered only
            by peers still at its height, of which there are none. Traced over
            kabel, a stranded node received 41 proposals and 143 finalizations
            and committed nothing."
    (let [impl (rr/create {:a nil :b nil :c nil})
          st (:state (n/init impl (merge (rr/test-attestations) {:peer-id :a :validators [:a :b :c]})))
          ;; A finalization for exactly one height ahead of us.
          r (n/step impl st {:type :message-received :from :b
                             :msg {:kind :finalized :height 1
                                   :proposal {:snapshot-id :p1}}})
          recovery (->> (:effects r)
                        (filter #(= :broadcast (n/effect-kind %)))
                        (map n/effect-params)
                        (filter #(= :recovery (:topic %))))]
      (is (seq recovery) "one height behind must ask for a state sync")
      (is (= :state-sync (:kind (:msg (first recovery))))))))

(deftest state-sync-commits-what-it-learns
  (testing "the defect the off-by-one was hiding, and a SAFETY one.

            Adopting a peer's height and finalized map while emitting nothing
            means the node skips past decisions it never reported: its committed
            sequence acquires a hole and two nodes disagree at those positions.
            `sim/agreement?` reports it as the safety violation it is.

            It stayed invisible while syncs were rare. Making them ordinary --
            by fixing the off-by-one above -- surfaced it on the first run at 30%
            loss."
    (let [impl (rr/create {:a nil :b nil :c nil})
          st (:state (n/init impl (merge (rr/test-attestations) {:peer-id :a :validators [:a :b :c]})))
          r (n/step impl st {:type :message-received :from :b
                             :msg {:kind :state-sync-response
                                   :current-height 3
                                   :finalized {0 {:snapshot-id :p0}
                                               1 {:snapshot-id :p1}
                                               2 {:snapshot-id :p2}}}})
          committed (->> (:effects r)
                         (filter #(= :commit (n/effect-kind %)))
                         (mapcat #(:vertices (n/effect-params %))))]
      (is (= [{:snapshot-id :p0} {:snapshot-id :p1} {:snapshot-id :p2}] committed)
          "every learned height is committed, in order, with no hole")
      (is (= 3 (:height (:state r)))))

    ;; A peer's history with a GAP must not produce a gapped commit sequence.
    (let [impl (rr/create {:a nil :b nil :c nil})
          st (:state (n/init impl (merge (rr/test-attestations) {:peer-id :a :validators [:a :b :c]})))
          r (n/step impl st {:type :message-received :from :b
                             :msg {:kind :state-sync-response
                                   :current-height 5
                                   :finalized {0 {:snapshot-id :p0}
                                               1 {:snapshot-id :p1}
                                               ;; 2 missing
                                               3 {:snapshot-id :p3}}}})
          committed (->> (:effects r)
                         (filter #(= :commit (n/effect-kind %)))
                         (mapcat #(:vertices (n/effect-params %))))]
      (is (= [{:snapshot-id :p0} {:snapshot-id :p1}] committed)
          "only the contiguous run is committed -- a commit sequence with a gap
           is exactly what this fix exists to prevent"))))

(deftest per-tick-traffic-does-not-grow-with-the-length-of-the-run
  (testing "the storm guard, on the algorithm the storm happened to.

            The state-sync fix was correct per MESSAGE -- a node one height
            behind should ask for a sync -- and wrong per second: every lagging
            node asked every peer, and each answer carried the responder's
            whole `:finalized` map. Five nodes over kabel went from ten heights
            finalized each to one, and the simulator reported nothing, because
            the message COUNT had barely moved.

            Two independent defences now hold it: `:sync-requested-at` throttles
            the asking, and `cleanup-old-data` bounds the map so an answer
            cannot grow. This asserts the consequence rather than either
            mechanism, so it still holds if they are replaced.

            Measured, and the bound is generous on purpose. With the map
            bounded, peak per-tick bytes are FLAT at 1090 from 100 ticks to 800.
            With `cleanup-old-data` made a no-op, the same run reaches 6066 --
            5.6x -- while the map grows from 10 entries to 139."
    (let [peak (fn [ticks]
                 (let [s (sim/run (sim/make
                                   {:seed 3
                                    :nodes (zipmap sim-peers (repeat (rr/create)))
                                    :node-config (zipmap sim-peers
                                                         (repeat (rr/test-attestations)))
                                    :config {:value-fn (fn [_ p ctx]
                                                         {:snapshot-id [p (:height ctx)]
                                                          :payload :x})
                                             :drop-rate 0.1}})
                                  ticks)]
                   [(apply max (vals (sim/peak-tick-bytes s)))
                    (count (sim/committed s :a))]))
          [short-peak short-heights] (peak 100)
          [long-peak long-heights] (peak 800)]
      (is (< 10 long-heights) "the long run must actually make progress")
      (is (> long-heights short-heights) "and more of it than the short one")
      (is (< long-peak (* 3 short-peak))
          (str "per-tick traffic must not grow with the run: "
               short-peak " bytes at 100 ticks, " long-peak " at 800")))))

;; ============================================================
;; Vote attestations
;;
;; A vote here is RELAYED. `:vote-bundle` answers a peer's quorum timeout and
;; `:catchup` answers a want-proposal, and both carry other nodes' votes -- so
;; the peer handing one over is almost never its author, and transport
;; authentication says nothing at all about the voters named inside.
;;
;; Until these tests existed a vote was a bare NAME. That is all a bundle could
;; carry and all a receiver could check, so "here are the validators that
;; voted" was a claim by the relayer, and one peer could hand a node a complete
;; quorum it had invented. Every test in this file was honest, and an honest
;; node's votes are its own, which is why the suite never noticed.
;; ============================================================

(deftest a-vote-must-carry-an-attestation-that-verifies
  (let [sm (rr/create test-validators)
        voting (-> (initial-state sm {:peer-id validator-a})
                   (assoc :current-proposal test-proposal
                          :current-proposal-id (:snapshot-id test-proposal)
                          :phase :voting))
        pid (:snapshot-id test-proposal)
        forged (handle-event sm voting {:type :vote-received
                                        :proposal-id pid
                                        :voter validator-b
                                        :att :not-a-real-attestation})
        missing (handle-event sm voting {:type :vote-received
                                         :proposal-id pid
                                         :voter validator-b
                                         :att nil})
        honest (handle-event sm voting {:type :vote-received
                                        :proposal-id pid
                                        :voter validator-b})]
    (is (empty? (get-in (:state forged) [:votes pid]))
        "a vote whose attestation does not verify is not a vote")
    (is (empty? (get-in (:state missing) [:votes pid]))
        "and neither is one with no attestation at all")
    (is (= #{validator-b} (set (keys (get-in (:state honest) [:votes pid]))))
        "while an attested vote is counted, so the guard is not just refusing
         everything")))

(deftest a-relayed-bundle-cannot-invent-a-quorum
  (testing "THE hole `:vote-bundle` opened. One peer answers our quorum timeout
            with a list naming every validator, and before attestations that
            list WAS the evidence -- a single connection could finalize a
            height on its own say-so."
    (let [sm (rr/create test-validators)
          pid (:snapshot-id test-proposal)
          voting (-> (initial-state sm {:peer-id validator-a})
                     (assoc :current-proposal test-proposal
                            :current-proposal-id pid
                            :phase :voting))
          invented (handle-event sm voting
                                 {:type :vote-bundle
                                  :sender validator-b
                                  :proposal-id pid
                                  :votes (mapv (fn [v] {:voter v :att :forged})
                                               (keys test-validators))})
          genuine (handle-event sm voting
                                {:type :vote-bundle
                                 :sender validator-b
                                 :proposal-id pid
                                 :votes (attested pid (keys test-validators))})]
      (is (empty? (get-in (:state invented) [:votes pid]))
          "not one invented vote is counted")
      (is (not (contains-effect? (:effects invented) :commit))
          "so no quorum, and nothing is finalized")
      (is (contains-effect? (:effects genuine) :commit)
          "while a bundle of real attestations still finalizes -- relaying
           votes is the POINT of this message, and it has to keep working"))))

(deftest a-relayed-catchup-cannot-invent-a-quorum
  (testing "the same hole in the other relay path. Fixing only the direct
            `:vote` message would have left both bundles open, which is where
            forging was cheapest anyway."
    (let [sm (rr/create test-validators)
          pid (:snapshot-id test-proposal)
          state (initial-state sm {:peer-id validator-a})
          invented (handle-event sm state
                                 {:type :proposal-catchup
                                  :sender validator-b
                                  :proposal test-proposal
                                  :height 0 :round 0
                                  :votes (mapv (fn [v] {:voter v :att :forged})
                                               (keys test-validators))})]
      (is (empty? (get-in (:state invented) [:votes pid])))
      (is (not (contains-effect? (:effects invented) :commit))))))

(deftest a-node-refuses-to-start-without-a-vote-verifier
  (testing "no permissive default, following Bullshark. A node that cannot
            check a relayed vote has no business counting one toward a quorum,
            and a default that quietly accepts everything is exactly how this
            survived an audit round."
    (is (thrown? clojure.lang.ExceptionInfo
                 (n/init (rr/create test-validators)
                         {:peer-id validator-a
                          :validators (vec (keys test-validators))})))
    (is (thrown? clojure.lang.ExceptionInfo
                 (n/init (rr/create test-validators)
                         {:peer-id validator-a
                          :validators (vec (keys test-validators))
                          :sign-vote (fn [_ _] :x)})))))

;; ============================================================
;; State sync must not erase live consensus state
;; ============================================================

(deftest a-state-sync-that-teaches-nothing-changes-nothing
  (testing "the reset used to be unconditional, and for the PROPOSER that is a
            safety violation

           A `state-sync-response` answers a question asked a while ago, so a
           stale one that carries nothing new is the common case, not the edge
           case. Wiping `:round`, `:current-proposal` and `:votes` on one meant:

             the proposer for height h had proposed, voted, and collected votes;
             a stale sync erased all of it and returned it to `:proposing`;
             `:next-round` fired, it was STILL the proposer for h, so it asked
             the application again -- and an application is entitled to answer
             differently, because `request-value` never promised to ask once.

           Two proposals for one height. Nodes holding the first keep it, nodes
           holding nothing take the second, votes pile up on both tallies, and
           with four validators both reach three. `handle-value-ready`'s rule --
           the first value for a height is THE value -- was right and could not
           hold, because the state it is written on was erased underneath it."
    (let [sm (rr/create test-validators)
          pid (:snapshot-id test-proposal)
          proposing (-> (initial-state sm {:peer-id validator-a})
                        (assoc :height 8
                               :current-proposal test-proposal
                               :current-proposal-id pid
                               :phase :voting
                               :votes {pid {validator-a (attest validator-a pid)
                                            validator-b (attest validator-b pid)}}))
          ;; A peer answers with a history we already have, at our own height.
          stale (handle-event sm proposing
                              {:type :state-sync-response
                               :sender validator-b
                               :finalized {}
                               :current-height 8})
          after (:state stale)]
      (is (= pid (:current-proposal-id after))
          "the proposal we already broadcast is still ours")
      (is (= 2 (count (get (:votes after) pid)))
          "and the votes cast for it are still counted")
      (is (= 8 (:height after)) "we did not move")))

  (testing "while a sync that DOES advance still resets, because at a new
            height the old proposal and its votes are meaningless"
    (let [sm (rr/create test-validators)
          pid (:snapshot-id test-proposal)
          proposing (-> (initial-state sm {:peer-id validator-a})
                        (assoc :height 8
                               :current-proposal test-proposal
                               :current-proposal-id pid
                               :phase :voting
                               :votes {pid {validator-a (attest validator-a pid)}}))
          advanced (:state (handle-event sm proposing
                                         {:type :state-sync-response
                                          :sender validator-b
                                          :finalized {8 test-proposal}
                                          :current-height 9}))]
      (is (= 9 (:height advanced)))
      (is (nil? (:current-proposal-id advanced)))
      (is (empty? (:votes advanced))))))

(deftest a-proposer-offers-one-value-per-height-across-a-stale-sync
  (testing "the divergence end to end, at the level it actually bites

           Reproduced in the simulator at seed 6 with 10% loss before the fix:
           `:a` proposed value 12 for height 8, a stale sync wiped it, `:a`
           proposed 13, and both reached a majority of the four validators. One
           node committed 12 where the other three committed 13."
    (let [sm (rr/create test-validators)
          first-proposal {:snapshot-id (random-uuid) :data "first"}
          second-proposal {:snapshot-id (random-uuid) :data "second"}
          st (-> (initial-state sm {:peer-id validator-a})
                 (assoc :height 0 :phase :proposing))
          proposed (:state (handle-event sm st {:type :value-ready
                                                :value first-proposal}))
          synced (:state (handle-event sm proposed
                                       {:type :state-sync-response
                                        :sender validator-b
                                        :finalized {}
                                        :current-height 0}))
          again (handle-event sm synced {:type :value-ready
                                         :value second-proposal})]
      (is (= (:snapshot-id first-proposal) (:current-proposal-id (:state again)))
          "the second value is refused: one proposal per height, and a stale
           sync does not reopen the question"))))

(deftest a-sync-never-advances-past-what-it-committed
  (testing "the hole. `new-height` used to take the peer's `current-height`
            into its `max`, so a node at 0 syncing from a peer at 500 arrived
            at 500 having committed NOTHING -- its committed sequence began at
            500 with 0..499 simply absent.

            Against the datahike ledger that transacts height 500 into a
            database that has never seen the preceding 499. It does not look
            like a fault; it looks like a node that caught up."
    (let [sm (rr/create test-validators)
          behind (assoc (initial-state sm {:peer-id validator-a}) :height 0)
          ;; A peer far ahead, whose bounded history retains only its last few
          ;; heights -- none of which continue ours.
          far (handle-event sm behind
                            {:type :state-sync-response
                             :sender validator-b
                             :finalized (into {} (map (fn [h] [h {:snapshot-id [:p h]}]))
                                              (range 490 500))
                             :current-height 500})]
      (is (= 0 (:height (:state far)))
          "we did not move, because we learned nothing that continues our
           history")
      (is (not (contains-effect? (:effects far) :commit))
          "and committed nothing, which is the same statement"))))

(deftest a-sync-advances-exactly-as-far-as-the-contiguous-run
  (let [sm (rr/create test-validators)
        behind (assoc (initial-state sm {:peer-id validator-a}) :height 3)
        ;; 3,4,5 continue us; 8,9 do not. The peer is at 10.
        r (handle-event sm behind
                        {:type :state-sync-response
                         :sender validator-b
                         :finalized (into {} (map (fn [h] [h {:snapshot-id [:p h]}]))
                                          [3 4 5 8 9])
                         :current-height 10})]
    (is (= 6 (:height (:state r)))
        "past the contiguous run and no further -- 8 and 9 are real decisions
         we have no path to yet, and adopting them would leave 6 and 7 as holes")
    (is (= 3 (count (filter #(= :commit (first %)) (:effects r))))
        "one commit per height learned, so the consumer's log has no gap")))

(deftest a-node-that-cannot-be-caught-up-says-so
  (testing "the limitation the old jump was hiding

           `:finalized` keeps ten heights. A node more than ten behind cannot
           be caught up by a peer that has GC'd the range it is missing, and
           there is no archival history to fall back on -- that is a real gap
           (see the compaction finding), not something an algorithm can solve
           locally.

           What it CAN do is say so. Jumping to the peer's height made the node
           look caught up while its committed sequence had a hole in it, which
           is strictly worse than being visibly stuck."
    (let [sm (rr/create test-validators)
          behind (assoc (initial-state sm {:peer-id validator-a}) :height 0)
          r (handle-event sm behind
                          {:type :state-sync-response
                           :sender validator-b
                           :finalized (into {} (map (fn [h] [h {:snapshot-id [:p h]}]))
                                            (range 490 500))
                           :oldest 490
                           :current-height 500})
          logs (filter #(= :log (first %)) (:effects r))]
      (is (= 0 (:height (:state r))) "still stuck, and honestly so")
      (is (some (fn [[_ p]] (= :warn (:level p))) logs)
          "and it is reported at :warn rather than passing for a normal sync"))))

;; ============================================================
;; One proposal per height, on EVERY path that can set one
;; ============================================================

(deftest a-catchup-cannot-replace-a-proposal-we-already-hold
  (testing "the third path, and the one most exposed

           `handle-value-ready` and `handle-proposal-received` each refuse a
           second proposal for a height. `handle-proposal-catchup` did not: it
           `assoc`ed `:current-proposal` unconditionally. That is the most
           dangerous path to leave open, because a catchup is by definition a
           proposal arriving from someone who is not its author.

           A node holding P, handed Q for the same height, adopted Q and voted
           for it -- having already voted for P. It then counted toward BOTH
           tallies, and with four validators both reach three. Two nodes commit
           different values at one position, from one relayed message.

           This is what remained of the conformance divergence after the stale
           state-sync fix: one failure in twenty full integration runs. Under
           four concurrent networks the guard fires thousands of times per
           batch, so the condition was not rare -- it was constant, and
           silently adopted."
    (let [sm (rr/create test-validators)
          ours {:snapshot-id (random-uuid) :data "ours"}
          theirs {:snapshot-id (random-uuid) :data "theirs"}
          held (-> (initial-state sm {:peer-id validator-a})
                   (assoc :height 0
                          :current-proposal ours
                          :current-proposal-id (:snapshot-id ours)
                          :phase :voting
                          :votes {(:snapshot-id ours)
                                  {validator-a (attest validator-a (:snapshot-id ours))}}))
          r (handle-event sm held
                          {:type :proposal-catchup
                           :sender validator-b
                           :proposal theirs
                           :height 0 :round 0
                           :votes (attested (:snapshot-id theirs)
                                            [validator-b validator-c])})]
      (is (= (:snapshot-id ours) (:current-proposal-id (:state r)))
          "we keep the proposal we already voted for")
      (is (nil? (get (:votes (:state r)) (:snapshot-id theirs)))
          "and cast no vote for the one we were handed")
      (is (not (contains-effect? (:effects r) :commit))
          "so a relayed quorum for a second proposal finalizes nothing")))

  (testing "while a catchup for the proposal we DO hold still works -- carrying
            votes for it is the entire purpose of the message"
    (let [sm (rr/create test-validators)
          pid (:snapshot-id test-proposal)
          held (-> (initial-state sm {:peer-id validator-a})
                   (assoc :height 0
                          :current-proposal test-proposal
                          :current-proposal-id pid
                          :phase :voting
                          :votes {pid {validator-a (attest validator-a pid)}}))
          r (handle-event sm held
                          {:type :proposal-catchup
                           :sender validator-b
                           :proposal test-proposal
                           :height 0 :round 0
                           :votes (attested pid [validator-b validator-c])})]
      (is (contains-effect? (:effects r) :commit)))))

(deftest a-finalization-naming-another-proposal-is-refused
  (testing "the fourth path. A peer's announcement is a claim; the proposal we
            hold is the one we voted for. Adopting the claim over it is how one
            peer rewrites another's committed prefix, and only one proposal per
            height can exist in an honest run -- so this branch firing means
            something upstream is already broken and must be loud, not silently
            resolved in favour of whatever arrived last."
    (let [sm (rr/create test-validators)
          ours {:snapshot-id (random-uuid) :data "ours"}
          theirs {:snapshot-id (random-uuid) :data "theirs"}
          held (-> (initial-state sm {:peer-id validator-a})
                   (assoc :height 0
                          :current-proposal ours
                          :current-proposal-id (:snapshot-id ours)))
          r (handle-event sm held {:type :proposal-finalized
                                   :proposal theirs
                                   :height 0})]
      (is (= 0 (:height (:state r))) "we do not advance on someone else's claim")
      (is (not (contains-effect? (:effects r) :commit)))
      (is (some (fn [[k p]] (and (= :log k) (= :warn (:level p)))) (:effects r))
          "and it is reported"))))

;; ============================================================
;; What one message may cost us
;; ============================================================

(deftest a-relayed-vote-list-costs-at-most-one-verification-per-validator
  (testing "`record-vote` records NOTHING when verification fails, so
            `(contains? votes voter)` stays false and the same junk pair can be
            repeated as many times as fit in a message -- each repeat costing a
            full Ed25519 verification, inside `step`, on the event loop.

           Deduping by voter and truncating to the committee size bounds the
           work by n however large the message is. n is ours; the message
           length was theirs."
    (let [sm (rr/create test-validators)
          pid (:snapshot-id test-proposal)
          verifications (atom 0)
          counting (fn [voter p att]
                     (swap! verifications inc)
                     ((:verify-vote test-atts) voter p att))
          held (-> (initial-state sm {:peer-id validator-a})
                   (assoc :verify-vote counting
                          :current-proposal test-proposal
                          :current-proposal-id pid
                          :phase :voting))
          ;; 5000 copies of one junk vote -- the cheapest possible flood.
          flood (vec (repeat 5000 {:voter validator-b :att :junk}))]
      (handle-event sm held {:type :vote-bundle :sender validator-b
                             :proposal-id pid :votes flood})
      (is (<= @verifications (count test-validators))
          (str "one verification per validator at most, not one per entry: "
               @verifications)))))

(deftest a-state-sync-answer-cannot-plant-permanent-entries
  (testing "`(merge ours finalized-heights)` stored the peer's WHOLE map, at
            any height, with no size bound -- and `cleanup-old-data` prunes
            only below `height - 10`, so entries above our height survived
            every future prune. `answer-state-sync` then re-served them, making
            each node a relay for whatever it had been fed.

           Only the contiguous run we actually learned is kept now, which is
           also exactly what we emit commits for -- so `:finalized` agrees with
           what the consumer was told."
    (let [sm (rr/create test-validators)
          behind (assoc (initial-state sm {:peer-id validator-a}) :height 0)
          poison (into {} (map (fn [h] [h {:snapshot-id [:junk h]}]))
                       (range 1000000 1001000))
          r (handle-event sm behind
                          {:type :state-sync-response
                           :sender validator-b
                           :finalized poison
                           :current-height 0})]
      (is (empty? (:finalized (:state r)))
          "a thousand unreachable heights are not adopted")
      (is (= 0 (:height (:state r)))
          "and nothing was learned, so nothing moved"))))

;; ============================================================
;; Catch-up depth, and the node that gives up forever
;; ============================================================

(deftest retention-sizes-how-far-behind-a-peer-may-fall
  (testing "`:finalized` is the ONLY history this algorithm can serve --
            `answer-state-sync` reads it and nothing else -- so its size is
            exactly how many heights a node may miss and still be recoverable.
            Ten was hard-coded, and ten heights is a few seconds of downtime.

           Configurable now, so a deployment can pay memory for reachable
           catch-up. It sizes the limitation rather than removing it; a peer
           further behind than this still needs a snapshot."
    (let [sm (rr/create test-validators)
          fin (into {} (map (fn [h] [h {:snapshot-id [:h h]}])) (range 0 100))
          at-99 (fn [retention]
                  (-> (initial-state sm (cond-> {:peer-id validator-a}
                                          retention (assoc :finalized-retention retention)))
                      (assoc :height 99 :finalized fin)
                      rr/cleanup-old-data
                      :finalized
                      keys
                      sort))]
      ;; The floor is `height - retention`, INCLUSIVE, so N retention keeps
      ;; N+1 heights. Asserted as it is rather than rounded off in the test:
      ;; the exact floor is what `answer-state-sync` reports as `:oldest`, and
      ;; a requester compares its own height against that number.
      (is (= 11 (count (at-99 nil))) "the default is unchanged")
      (is (= 89 (first (at-99 nil))) "floor = 99 - 10, kept")
      (is (= 51 (count (at-99 50))) "and a deployment can ask for more")
      (is (= 49 (first (at-99 50)))
          "which is the whole point: a peer at 50 is now recoverable and was not"))))

(deftest a-stranded-node-asks-again-instead-of-giving-up-for-good
  (testing "LIVENESS, and a silent one.

           `:sync-requested-at` is set to the current height so that one
           request goes out per height rather than one per finalization seen --
           necessary, because the unthrottled version was a message storm that
           took five kabel nodes from ten finalized heights each to one.

           But a stranded node never leaves its height. So it asked once, was
           told no peer could serve it, and then never asked again for the rest
           of the process's lifetime -- while a validator finishing its own
           catch-up, or rejoining with deeper history, sat there able to help.
           The throttle and the retry are in tension and the timer is what
           resolves it: the flag stays set, and a timer clears it later."
    (let [sm (rr/create test-validators)
          behind (assoc (initial-state sm {:peer-id validator-a})
                        :height 0 :sync-requested-at 0)
          r (handle-event sm behind
                          {:type :state-sync-response
                           :sender validator-b
                           :finalized {900 {:snapshot-id [:h 900]}}
                           :current-height 901
                           :oldest 890})]
      (is (= 0 (:height (:state r))) "genuinely stranded -- nothing was learnable")
      (is (some #(and (= :set-timer (n/effect-kind %))
                      (= :sync-retry (:timer-id (n/effect-params %))))
                (:effects r))
          "a retry is armed rather than the node falling silent")
      (is (= 0 (:sync-requested-at (:state r)))
          "and the throttle is still in force until it fires -- clearing it here
           would make the next finalization broadcast trigger another request,
           which is the storm")))

  (testing "and when the timer fires the gate opens for exactly one request"
    (let [sm (rr/create test-validators)
          stuck (assoc (initial-state sm {:peer-id validator-a})
                       :height 0 :sync-requested-at 0)
          r (handle-event sm stuck {:type :timer-fired :timer-id :sync-retry})]
      (is (nil? (:sync-requested-at (:state r)))
          "the flag is cleared, so the next finalization above us asks again")
      (is (empty? (filter #(= :broadcast (n/effect-kind %)) (:effects r)))
          "and nothing is sent from the timer itself -- a request needs a peer
           we know is ahead, and a finalization is how we learn that"))))

(deftest a-stranded-node-recovers-when-a-deeper-peer-appears
  (testing "the end-to-end shape the retry exists for: stranded, told nobody
            can help, retried, and caught up by a peer that could."
    (let [sm (rr/create test-validators)
          s0 (assoc (initial-state sm {:peer-id validator-a})
                    :height 0 :sync-requested-at 0)
          ;; A shallow peer answers first and cannot help.
          s1 (:state (handle-event sm s0 {:type :state-sync-response
                                          :sender validator-b
                                          :finalized {900 {:snapshot-id [:h 900]}}
                                          :current-height 901 :oldest 890}))
          ;; The timer fires.
          s2 (:state (handle-event sm s1 {:type :timer-fired :timer-id :sync-retry}))
          ;; A peer that kept its history from the start answers.
          deep (into {} (map (fn [h] [h {:snapshot-id [:h h]}])) (range 0 4))
          r3 (handle-event sm s2 {:type :state-sync-response
                                  :sender validator-b
                                  :finalized deep
                                  :current-height 4 :oldest 0})]
      (is (= 4 (:height (:state r3))) "caught up, having previously given up")
      (is (= 4 (count (filter #(= :commit (n/effect-kind %)) (:effects r3))))
          "and every learned height was handed to the application, in order"))))

;; ============================================================
;; Shape validation
;; ============================================================

(deftest a-malformed-message-is-refused-before-it-reaches-the-rules
  (testing "authentication says WHO sent a message, not that its fields mean
            anything -- and a Byzantine peer is authenticated too. Every field
            checked here is one an authenticated peer may choose freely.

           The TYPE checks are what carry weight. `get-proposer-id` computes
           `(mod height (count validators))` and `nth`s the result, so a string
           throws inside `step`; the runtime contains it and counts a dropped
           message, which is survivable and is not the same as the message
           being meaningless.

           The NON-NEGATIVE cases below are defence in depth and are marked so.
           Relaxing `nat-int?` to `int?` passes this whole test -- verified by
           mutation -- because `(mod -1 3)` is 2 in Clojure and a negative
           height is dropped by the height comparison regardless. They are
           asserted anyway, so the behaviour is pinned if a later change makes
           them matter; they are not evidence that they currently do."
    (let [sm (rr/create test-validators)
          s0 (initial-state sm {:peer-id validator-a})
          send (fn [msg] (handle-event sm s0 {:type :message-received
                                              :sender validator-b
                                              :from validator-b
                                              :msg msg}))]
      (testing "a height that is not a number"
        (is (= s0 (:state (send {:kind :finalized :height "500" :proposal {:x 1}})))
            "state is untouched -- and note this is the case that THROWS
             without the guard, rather than merely misbehaving"))
      (testing "a negative height (defence in depth -- see the docstring)"
        (is (= s0 (:state (send {:kind :proposal :height -1 :round 0
                                 :proposal {:x 1}})))))
      (testing "a negative round (defence in depth)"
        (is (= s0 (:state (send {:kind :proposal :height 0 :round -3
                                 :proposal {:x 1}})))))
      (testing "a vote naming no proposal"
        (is (= s0 (:state (send {:kind :vote :voter validator-b :att :a})))))
      (testing "a state-sync response whose history is not a map"
        (is (= s0 (:state (send {:kind :state-sync-response
                                 :finalized [1 2 3] :current-height 5})))))
      (testing "a state-sync request whose height is not a number"
        (is (= s0 (:state (send {:kind :state-sync :from :not-a-height})))))
      (testing "a vote bundle larger than any honest peer would send"
        (is (= s0 (:state (send {:kind :vote-bundle :proposal-id :p
                                 :votes (vec (repeat 20000 {:voter validator-b}))})))))
      (testing "but a well-formed message is still processed"
        (let [r (send {:kind :finalized :height 0 :proposal {:x 1}})]
          (is (not= s0 (:state r))
              "or the guard is refusing everything, which passes every
               assertion above while breaking the algorithm outright"))))))

;; ============================================================
;; The application's predicate
;; ============================================================

(deftest an-application-can-refuse-a-proposal-on-its-content
  (testing "round-robin had NO seam for this. It checked WHO sent a proposal
            and WHICH height it named, and nothing about what it contained --
            so the app-hash convention (`urd.consensus.apphash`) was
            enforceable in exactly one of the six algorithms, Tendermint being
            the only one with a `:valid-fn`.

           Defaulting to `(constantly true)` keeps every existing caller
           unchanged, which is also why this needs a test that watches the
           FALSE arm execute: Tendermint's `:valid-fn` sat unconfigured in src,
           test and docs for its whole life, and its false arm had never run
           once."
    (let [sm (rr/create test-validators)
          proposer (rr/get-proposer-id 0 test-validators)
          me (first (remove #{proposer} (keys test-validators)))
          ;; `:snapshot-id`, not `:id` -- round-robin's proposal identity.
          proposal {:snapshot-id :p1 :app-hash "agreed"}
          offer (fn [vf]
                  (handle-event sm
                                (initial-state sm {:peer-id me :valid-fn vf})
                                {:type :proposal-received :sender proposer
                                 :proposal proposal :height 0 :round 0}))]

      (testing "a proposal the application accepts is adopted and voted for"
        (let [r (offer (constantly true))]
          (is (= proposal (:current-proposal (:state r))))
          (is (some #(= :broadcast (n/effect-kind %)) (:effects r))
              "and a vote goes out")))

      (testing "a proposal the application refuses is neither adopted nor voted for"
        (let [r (offer (constantly false))]
          (is (nil? (:current-proposal (:state r)))
              "we do not hold a proposal we consider invalid")
          (is (empty? (filter #(= :broadcast (n/effect-kind %)) (:effects r)))
              "and above all we do not VOTE for it -- withholding the vote is
               the designed response to disagreeing about application state")))

      (testing "which carries the app-hash convention end to end"
        (is (some? (:current-proposal (:state (offer (rr-apphash-checker "agreed")))))
            "a node whose application agrees votes")
        (is (nil? (:current-proposal (:state (offer (rr-apphash-checker "diverged")))))
            "a node whose application has diverged does not")
        (is (nil? (:current-proposal
                   (:state (handle-event sm
                                         (initial-state sm {:peer-id me
                                                            :valid-fn (rr-apphash-checker "agreed")})
                                         {:type :proposal-received :sender proposer
                                          :proposal {:snapshot-id :p1} :height 0 :round 0}))))
            "and a proposal that simply OMITS the digest is refused too, which
             is the bypass that makes absence-is-invalid the default")))))
