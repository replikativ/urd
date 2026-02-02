(ns urd.consensus.state-machine
  "Generic consensus state machine abstraction.

  Consensus algorithms are implemented as pure state machines:
  - State is immutable data
  - Events are immutable data
  - Transitions are pure functions: (state, event) → {:state new-state :effects [effect...]}
  - Effects are data describing side-effects to perform

  This allows:
  - Deterministic testing without async
  - REPL-driven development
  - Different algorithms sharing the same runtime")

;; ============================================================
;; Protocol
;; ============================================================

(defprotocol ConsensusAlgorithm
  "Protocol for consensus state machines.

  Implementations provide pure functions for state transitions."

  (initial-state [this config]
    "Create initial state for the algorithm.

    Args:
      config - Map with :peer-id, :validator-set, etc.

    Returns:
      Initial state map")

  (handle-event [this state event]
    "Process an event and return new state + effects.

    Args:
      state - Current state map
      event - Event map with :type and event-specific data

    Returns:
      Map with:
        :state - New state (may be unchanged)
        :effects - Vector of effect data (may be empty)"))

;; ============================================================
;; Event Types (data)
;; ============================================================

(defn start-round-event
  "Consensus round should begin.

  Emitted by runtime when starting a new consensus round."
  []
  {:type :start-round})

(defn proposal-received-event
  "Proposal received from network.

  Args:
    proposal - The proposed value
    height - Consensus height
    round - Consensus round
    sender - Peer ID of proposer"
  [proposal height round sender]
  {:type :proposal-received
   :proposal proposal
   :height height
   :round round
   :sender sender})

(defn vote-received-event
  "Vote received from network.

  Args:
    proposal-id - UUID of proposal being voted on
    voter - Peer ID of voter
    signature - Vote signature"
  [proposal-id voter signature]
  {:type :vote-received
   :proposal-id proposal-id
   :voter voter
   :signature signature})

(defn timeout-event
  "Timer expired.

  Args:
    timer-id - ID of the timer that expired"
  [timer-id]
  {:type :timeout
   :timer-id timer-id})

(defn quorum-reached-event
  "Quorum of votes reached for a proposal.

  Args:
    proposal-id - UUID of proposal that reached quorum"
  [proposal-id]
  {:type :quorum-reached
   :proposal-id proposal-id})

;; ============================================================
;; Effect Types (data)
;; ============================================================

(defn broadcast-effect
  "Broadcast a message to all peers.

  Args:
    topic - Message topic keyword (:proposals, :votes, etc.)
    payload - Message payload map"
  [topic payload]
  [:broadcast {:topic topic :payload payload}])

(defn persist-effect
  "Persist data to consensus log.

  Args:
    key - Storage key
    value - Value to persist"
  [key value]
  [:persist {:key key :value value}])

(defn set-timer-effect
  "Set a timer that will fire a timeout event.

  Args:
    timer-id - Unique ID for this timer
    duration-ms - Duration in milliseconds"
  [timer-id duration-ms]
  [:set-timer {:timer-id timer-id :duration-ms duration-ms}])

(defn cancel-timer-effect
  "Cancel a previously set timer.

  Args:
    timer-id - ID of timer to cancel"
  [timer-id]
  [:cancel-timer {:timer-id timer-id}])

(defn finalize-effect
  "Finalize a proposal (consensus reached).

  Args:
    proposal - The finalized proposal
    height - Height at which it was finalized"
  [proposal height]
  [:finalize {:proposal proposal :height height}])

(defn log-effect
  "Log a message (for debugging/monitoring).

  Args:
    level - Log level (:debug, :info, :warn, :error)
    message - Log message"
  [level message]
  [:log {:level level :message message}])

;; ============================================================
;; Recovery Effects (for handling failures)
;; ============================================================

(defn request-missing-proposal-effect
  "Request missing proposal from peers.

  Args:
    height - Height for which we need proposal
    round - Round for which we need proposal"
  [height round]
  [:request-missing-proposal {:height height :round round}])

(defn request-state-sync-effect
  "Request state synchronization from peers.

  Args:
    from-height - Height we're currently at
    to-height - Height we need to catch up to"
  [from-height to-height]
  [:request-state-sync {:from-height from-height :to-height to-height}])

(defn broadcast-finalization-effect
  "Broadcast finalization to help others catch up.

  Args:
    proposal - The finalized proposal
    height - Height that was finalized
    votes - Set of votes that achieved quorum"
  [proposal height votes]
  [:broadcast-finalization {:proposal proposal
                            :height height
                            :votes votes}])

(defn request-votes-effect
  "Request votes from peers (when near quorum).

  Args:
    proposal-id - Proposal we're collecting votes for
    height - Current height
    round - Current round"
  [proposal-id height round]
  [:request-votes {:proposal-id proposal-id
                   :height height
                   :round round}])

(defn trigger-next-round-effect
  "Trigger the next consensus round after a delay.

  This effect schedules a :start-round event to be sent after a short delay,
  allowing the state machine to advance and prepare for the next round.

  Args:
    delay-ms - Delay in milliseconds before starting next round (default 100)"
  ([] (trigger-next-round-effect 100))
  ([delay-ms]
   [:trigger-next-round {:delay-ms delay-ms}]))
