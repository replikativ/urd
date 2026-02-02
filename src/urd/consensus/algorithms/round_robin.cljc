(ns urd.consensus.algorithms.round-robin
  "Round-robin consensus algorithm - pure state machine implementation.

  Proposer selection rotates by height:
  - Height 0: validator 0 proposes
  - Height 1: validator 1 proposes
  - etc.

  Each round:
  1. Proposer broadcasts proposal
  2. Validators vote if proposal is valid
  3. When quorum reached, finalize and move to next height
  4. On timeout, increment round and retry"
  (:require [urd.consensus.state-machine :as sm]))

;; ============================================================
;; State Structure
;; ============================================================

;; State map contains:
;; - :peer-id - This peer's UUID
;; - :validator-set - Map of {peer-id → public-key}
;; - :height - Current consensus height (starts at 0)
;; - :round - Current round within height (starts at 0)
;; - :phase - Current phase: :proposing, :voting, :finalizing
;; - :current-proposal - Proposal being considered (nil if none)
;; - :current-proposal-id - UUID of current proposal
;; - :votes - Map of {proposal-id → set-of-voter-ids}
;; - :finalized - Map of {height → proposal} for finalized proposals

;; ============================================================
;; Helper Functions
;; ============================================================

(defn get-proposer-id
  "Determine which validator should propose at given height.

  Round-robin: proposer rotates by height (not round).
  Validator IDs are sorted to ensure consistent ordering."
  [height validator-set]
  (let [validator-ids (vec (sort (keys validator-set)))
        proposer-idx (mod height (count validator-ids))]
    (nth validator-ids proposer-idx)))

(defn am-proposer?
  "Check if this peer is the proposer for current height."
  [state]
  (let [proposer (get-proposer-id (:height state) (:validator-set state))]
    (= proposer (:peer-id state))))

(defn quorum-size
  "Calculate quorum size (simple majority)."
  [validator-set]
  (inc (quot (count validator-set) 2)))

(defn has-quorum?
  "Check if proposal has enough votes for quorum."
  [state proposal-id]
  (let [votes (get (:votes state) proposal-id #{})
        required (quorum-size (:validator-set state))]
    (>= (count votes) required)))

(defn valid-proposal?
  "Check if proposal is valid for current state.

  Proposal must match current height and round."
  [state proposal height round]
  (and (= height (:height state))
       (= round (:round state))))

;; ============================================================
;; Input Validation (DoS Resistance)
;; ============================================================

(defn valid-proposer?
  "Check if sender is the designated proposer for given height."
  [sender height validator-set]
  (= sender (get-proposer-id height validator-set)))

(defn valid-voter?
  "Check if voter is in the validator set."
  [voter validator-set]
  (contains? validator-set voter))

(defn valid-height-round?
  "Check if height/round is current (not stale or too far in future)."
  [state height round]
  (let [current-height (:height state)
        current-round (:round state)]
    (and
      ;; Not from the past
     (or (> height current-height)
         (and (= height current-height)
              (>= round current-round)))
      ;; Not too far in the future (prevent memory exhaustion)
     (<= height (+ current-height 5)))))

(defn cleanup-old-data
  "Remove stale data to prevent unbounded growth."
  [state]
  (let [current-height (:height state)
        ;; Keep only last 10 finalized heights
        min-finalized-height (max 0 (- current-height 10))]
    (-> state
        ;; Clean up old finalized proposals
        (update :finalized
                (fn [finalized]
                  (into {}
                        (filter (fn [[h _]] (>= h min-finalized-height))
                                finalized)))))))

;; ============================================================
;; State Transitions
;; ============================================================

(defn handle-start-round
  "Handle start of a new consensus round.

  If we're the proposer, broadcast a proposal.
  Otherwise, wait for proposal."
  [state]
  (if (am-proposer? state)
    ;; We're the proposer - request proposal from application
    {:state (assoc state :phase :proposing)
     :effects [[:request-proposal {:height (:height state)
                                   :round (:round state)}]
               (sm/set-timer-effect :proposal-timeout 2000)]}
    ;; We're a validator - wait for proposal
    {:state (assoc state :phase :voting)
     :effects [(sm/set-timer-effect :proposal-timeout 2000)]}))

(defn handle-proposal-ready
  "Handle when application provides a proposal to broadcast.

  This happens after we emit [:request-proposal] effect."
  [state proposal]
  (let [proposal-id (:snapshot-id proposal)
        height (:height state)
        round (:round state)]
    {:state (assoc state
                   :current-proposal proposal
                   :current-proposal-id proposal-id
                   :phase :voting)
     :effects [(sm/broadcast-effect :proposals
                                    {:proposal proposal
                                     :height height
                                     :round round})
               [:add-own-vote {:proposal-id proposal-id
                               :height height
                               :round round}]]}))

(defn handle-proposal-received
  "Handle proposal received from network."
  [state proposal height round sender]
  (cond
    ;; Validate proposer identity (DoS resistance)
    (not (valid-proposer? sender height (:validator-set state)))
    (do
      (println "[" (:peer-id state) "] DEBUG - Rejecting proposal from non-proposer" sender)
      {:state state
       :effects [(sm/log-effect :warn
                                (str "Rejecting proposal from non-proposer: " sender
                                     " at height " height))]})

    ;; Validate height/round (DoS resistance)
    (not (valid-height-round? state height round))
    (do
      (println "[" (:peer-id state) "] DEBUG - Ignoring out-of-range proposal: received height=" height "round=" round
               "but I'm at height=" (:height state) "round=" (:round state) "phase=" (:phase state))
      {:state state
       :effects [(sm/log-effect :debug
                                (str "Ignoring out-of-range proposal: height=" height
                                     " round=" round
                                     " (current: height=" (:height state)
                                     " round=" (:round state) ")"))]})

    ;; Already have a proposal - ignore duplicate
    (:current-proposal state)
    (do
      (println "[" (:peer-id state) "] DEBUG - Ignoring duplicate proposal - already have one")
      {:state state
       :effects [(sm/log-effect :debug
                                (str "Ignoring duplicate proposal - already have proposal"))]})

    ;; Proposal is for current height/round - accept and vote
    (valid-proposal? state proposal height round)
    (let [proposal-id (:snapshot-id proposal)]
      (println "[" (:peer-id state) "] DEBUG - Accepting proposal and voting for" proposal-id)
      {:state (assoc state
                     :current-proposal proposal
                     :current-proposal-id proposal-id
                     :phase :voting)
       :effects [(sm/cancel-timer-effect :proposal-timeout)
                 (sm/broadcast-effect :votes
                                      {:proposal-id proposal-id
                                       :voter (:peer-id state)
                                       :height height
                                       :round round})
                 [:add-own-vote {:proposal-id proposal-id
                                 :height height
                                 :round round}]
                 (sm/set-timer-effect :quorum-timeout 2000)]})

    ;; Proposal doesn't match current height/round
    :else
    {:state state
     :effects [(sm/log-effect :debug
                              (str "Ignoring proposal for different height/round: height=" height
                                   " round=" round
                                   " (current: height=" (:height state)
                                   " round=" (:round state) ")"))]}))

(defn handle-vote-received
  "Handle vote received from network."
  [state proposal-id voter signature]
  (cond
    ;; Validate voter is in validator set (DoS resistance)
    (not (valid-voter? voter (:validator-set state)))
    {:state state
     :effects [(sm/log-effect :warn
                              (str "Rejecting vote from unknown validator: " voter))]}

    ;; Only accept votes for current proposal (bounded storage)
    (not= proposal-id (:current-proposal-id state))
    {:state state
     :effects [(sm/log-effect :debug
                              (str "Ignoring vote for non-current proposal: " proposal-id))]}

    ;; Already finalized - ignore late votes
    (= :finalizing (:phase state))
    {:state state
     :effects [(sm/log-effect :debug "Ignoring vote - already finalizing")]}

    ;; Duplicate vote from same validator - ignore
    (contains? (get-in state [:votes proposal-id]) voter)
    {:state state
     :effects [(sm/log-effect :debug (str "Ignoring duplicate vote from " voter))]}

    ;; Valid vote - process it
    :else
    (let [;; Add vote to votes map (only for current proposal)
          new-state (update-in state [:votes proposal-id] (fnil conj #{}) voter)

          ;; Check if we now have quorum
          reached-quorum? (has-quorum? new-state proposal-id)]

      (if reached-quorum?
        ;; Quorum reached - finalize
        {:state (assoc new-state :phase :finalizing)
         :effects [(sm/cancel-timer-effect :quorum-timeout)
                   (sm/finalize-effect (:current-proposal state) (:height state))]}
        ;; Not yet quorum - just update state
        {:state new-state
         :effects []}))))

(defn handle-proposal-finalized
  "Handle proposal finalization (move to next height)."
  [state proposal height]
  (cond
    ;; We're behind - request state sync
    (> height (inc (:height state)))
    {:state state
     :effects [(sm/log-effect :info (str "Detected behind - at height " (:height state)
                                         " but received finalization for " height))
               (sm/request-state-sync-effect (:height state) height)]}

    ;; Normal finalization - this is our current height
    (= height (:height state))
    (let [votes (get (:votes state) (:snapshot-id proposal) #{})]
      {:state (-> state
                  ;; Advance to next height
                  (assoc :height (inc height))
                  (assoc :round 0)
                  (assoc :phase :proposing)

                  ;; Clear current round data (bounded storage)
                  (assoc :current-proposal nil)
                  (assoc :current-proposal-id nil)
                  (assoc :votes {})  ; Clear ALL votes - fresh start

                  ;; Record finalized proposal
                  (assoc-in [:finalized height] proposal)

                  ;; Clean up old finalized data (prevent unbounded growth)
                  (cleanup-old-data))
       :effects [(sm/log-effect :info (str "Finalized height " height))
                 ;; Broadcast finalization to help peers catch up
                 (sm/broadcast-finalization-effect proposal height votes)
                 ;; Automatically trigger next round for all validators
                 (sm/trigger-next-round-effect)]})

    ;; Already finalized this height (duplicate finalization event)
    :else
    {:state state
     :effects [(sm/log-effect :debug (str "Already finalized height " height))]}))

(defn handle-timeout
  "Handle timer expiration."
  [state timer-id]
  (case timer-id
    :proposal-timeout
    ;; No proposal received - request from peers and move to next round
    {:state (update state :round inc)
     :effects [(sm/log-effect :debug "Proposal timeout - requesting from peers")
               (sm/request-missing-proposal-effect (:height state) (:round state))]}

    :quorum-timeout
    ;; Quorum not reached - request votes from peers and move to next round
    (let [proposal-id (:current-proposal-id state)]
      {:state (update state :round inc)
       :effects [(sm/log-effect :debug "Quorum timeout - requesting votes")
                 (if proposal-id
                   (sm/request-votes-effect proposal-id (:height state) (:round state))
                   (sm/log-effect :debug "No current proposal to request votes for"))]})

    ;; Unknown timer
    {:state state
     :effects [(sm/log-effect :warn (str "Unknown timer: " timer-id))]}))

;; ============================================================
;; Recovery Event Handlers
;; ============================================================

(defn handle-proposal-catchup
  "Handle proposal + votes received from peer during catchup."
  [state proposal height round votes]
  (if (valid-proposal? state proposal height round)
    ;; Process proposal
    (let [proposal-id (:snapshot-id proposal)
          ;; Accept proposal
          state-with-proposal (assoc state
                                     :current-proposal proposal
                                     :current-proposal-id proposal-id
                                     :phase :voting)

          ;; Add all provided votes (validating each)
          state-with-votes (reduce
                            (fn [s {:keys [voter signature]}]
                              (if (and (valid-voter? voter (:validator-set state))
                                       (not (contains? (get-in s [:votes proposal-id]) voter)))
                                (update-in s [:votes proposal-id] (fnil conj #{}) voter)
                                s))
                            state-with-proposal
                            votes)

          ;; Check if we now have quorum
          reached-quorum? (has-quorum? state-with-votes proposal-id)]

      (if reached-quorum?
        {:state (assoc state-with-votes :phase :finalizing)
         :effects [(sm/log-effect :info "Catchup: Quorum reached")
                   (sm/finalize-effect proposal height)]}
        {:state state-with-votes
         :effects [(sm/log-effect :info (str "Catchup: Received proposal with "
                                             (count votes) " votes"))
                   (sm/set-timer-effect :quorum-timeout 1000)]}))

    ;; Invalid proposal
    {:state state
     :effects [(sm/log-effect :debug "Catchup: Invalid proposal")]}))

(defn handle-state-sync-response
  "Handle state synchronization response from peer."
  [state finalized-heights current-height]
  (let [;; Merge finalized heights (only those we don't have)
        merged-finalized (merge (:finalized state) finalized-heights)

        ;; Update to peer's current height if ahead
        new-height (max (:height state) current-height)]

    {:state (-> state
                (assoc :finalized merged-finalized)
                (assoc :height new-height)
                (assoc :round 0)
                (assoc :phase :proposing)
                ;; Clear any partial state
                (assoc :current-proposal nil)
                (assoc :current-proposal-id nil)
                (assoc :votes {}))
     :effects [(sm/log-effect :info (str "State sync: Updated to height " new-height))]}))

(defn handle-vote-bundle
  "Handle bundle of votes received from peer."
  [state proposal-id votes]
  (if (= proposal-id (:current-proposal-id state))
    ;; Add all valid votes
    (let [state-with-votes (reduce
                            (fn [s {:keys [voter signature]}]
                              (if (and (valid-voter? voter (:validator-set state))
                                       (not (contains? (get-in s [:votes proposal-id]) voter)))
                                (update-in s [:votes proposal-id] (fnil conj #{}) voter)
                                s))
                            state
                            votes)

          ;; Check for quorum
          reached-quorum? (has-quorum? state-with-votes proposal-id)]

      (if reached-quorum?
        {:state (assoc state-with-votes :phase :finalizing)
         :effects [(sm/log-effect :info "Vote bundle: Quorum reached")
                   (sm/finalize-effect (:current-proposal state) (:height state))]}
        {:state state-with-votes
         :effects [(sm/log-effect :debug (str "Vote bundle: Added " (count votes) " votes"))]}))

    ;; Not for current proposal
    {:state state
     :effects [(sm/log-effect :debug "Vote bundle: Not for current proposal")]}))

;; ============================================================
;; State Machine Implementation
;; ============================================================

(defrecord RoundRobinSM [validator-set]
  sm/ConsensusAlgorithm

  (initial-state [this config]
    {:peer-id (:peer-id config)
     :validator-set validator-set
     :height 0
     :round 0
     :phase :proposing
     :current-proposal nil
     :current-proposal-id nil
     :votes {}
     :finalized {}})

  (handle-event [this state event]
    (case (:type event)
      :start-round
      (handle-start-round state)

      :proposal-ready
      (handle-proposal-ready state (:proposal event))

      :proposal-received
      (handle-proposal-received state
                                (:proposal event)
                                (:height event)
                                (:round event)
                                (:sender event))

      :vote-received
      (handle-vote-received state
                            (:proposal-id event)
                            (:voter event)
                            (:signature event))

      :proposal-finalized
      (handle-proposal-finalized state
                                 (:proposal event)
                                 (:height event))

      :timeout
      (handle-timeout state (:timer-id event))

      ;; Recovery events
      :proposal-catchup
      (handle-proposal-catchup state
                               (:proposal event)
                               (:height event)
                               (:round event)
                               (:votes event))

      :state-sync-response
      (handle-state-sync-response state
                                  (:finalized event)
                                  (:current-height event))

      :vote-bundle
      (handle-vote-bundle state
                          (:proposal-id event)
                          (:votes event))

      ;; Unknown event
      {:state state
       :effects [(sm/log-effect :warn (str "Unknown event: " (:type event)))]})))

;; ============================================================
;; Public API
;; ============================================================

(defn create
  "Create a round-robin consensus state machine.

  Args:
    validator-set - Map of {peer-id → public-key}

  Returns:
    RoundRobinSM instance"
  [validator-set]
  (->RoundRobinSM validator-set))
