(ns urd.consensus.runtime
  "Generic consensus runtime - interprets effects from state machines.

  The runtime:
  1. Maintains current state
  2. Processes events through state machine
  3. Interprets effects as actual operations
  4. Handles timers, network, storage, etc.

  This separates pure state machine logic from async execution."
  (:require [urd.consensus.state-machine :as sm]
            [urd.consensus.network :as net]
            [urd.log :as log]
            #?(:clj [clojure.core.async :refer [chan timeout alt! close! >! <! <!! go put!]]
               :cljs [clojure.core.async :refer [chan timeout alt! close! >! <! put!]])
            [superv.async :refer [go-try- <?- go-loop-try-]]))

;; ============================================================
;; Runtime State
;; ============================================================

(defrecord ConsensusRuntime
           [;; Configuration
            peer-id              ; UUID - this peer's ID
            state-machine        ; ConsensusAlgorithm instance
            network              ; ConsensusNetwork instance
            consensus-log        ; ConsensusLog instance

   ;; State
            sm-state             ; Atom<Map> - current state machine state
            timers               ; Atom<Map<timer-id → cancel-fn>>

   ;; Callbacks
            on-propose           ; (fn []) → proposal
            on-finalize          ; (fn [proposal height])

   ;; Control
            running?             ; Atom<Boolean>
            event-ch             ; Channel - for incoming events
            control-ch])         ; Channel - for control messages

;; ============================================================
;; Effect Interpretation
;; ============================================================

(defn interpret-broadcast-effect
  "Broadcast message to network."
  [runtime topic payload]
  (go-try-
   (println "[" (:peer-id runtime) "] DEBUG - Broadcasting" topic ":" (keys payload))
   (<?- (net/broadcast! (:network runtime) topic payload))))

(defn interpret-set-timer-effect
  "Set a timer that fires timeout event."
  [runtime timer-id duration-ms]
  (let [timers (:timers runtime)
        event-ch (:event-ch runtime)]
    (go-try-
      ;; Cancel existing timer if present
     (when-let [cancel-fn (get @timers timer-id)]
       (cancel-fn))

      ;; Start new timer
     (let [timeout-ch (timeout duration-ms)
           cancel-ch (chan)

            ;; Cancel function
           cancel-fn (fn [] (put! cancel-ch true))]

        ;; Store cancel function
       (swap! timers assoc timer-id cancel-fn)

        ;; Wait for timeout or cancel
       (alt!
         timeout-ch ([_]
                      ;; Timer fired - send timeout event
                     (>! event-ch {:type :timeout :timer-id timer-id})
                      ;; Remove from timers map
                     (swap! timers dissoc timer-id))

         cancel-ch ([_]
                     ;; Timer cancelled
                    (swap! timers dissoc timer-id)))))))

(defn interpret-cancel-timer-effect
  "Cancel a running timer."
  [runtime timer-id]
  (when-let [cancel-fn (get @(:timers runtime) timer-id)]
    (cancel-fn)))

(defn interpret-finalize-effect
  "Finalize a proposal."
  [runtime proposal height]
  (go-try-
    ;; Persist to consensus log
   (<?- (log/finalize! (:consensus-log runtime)
                       (:snapshot-id proposal)
                       height))

    ;; Send proposal-finalized event back to state machine first
    ;; This advances the state before callbacks are called
   (>! (:event-ch runtime)
       {:type :proposal-finalized
        :proposal proposal
        :height height})

    ;; Call finalization callback after state has advanced
   (when-let [on-finalize (:on-finalize runtime)]
     (on-finalize proposal height))))

(defn interpret-request-proposal-effect
  "Request proposal from application."
  [runtime params]
  (go-try-
   (println "[" (:peer-id runtime) "] DEBUG - I am proposer, requesting proposal")
   (when-let [on-propose (:on-propose runtime)]
     (when-let [proposal (on-propose)]
       (println "[" (:peer-id runtime) "] DEBUG - Got proposal, sending proposal-ready event")
        ;; Send proposal-ready event
       (>! (:event-ch runtime)
           {:type :proposal-ready
            :proposal proposal})))))

(defn interpret-add-own-vote-effect
  "Add our own vote to consensus log."
  [runtime params]
  (go-try-
   (println "[" (:peer-id runtime) "] DEBUG - Adding own vote for proposal" (:proposal-id params))
   (<?- (log/add-vote! (:consensus-log runtime)
                       (:proposal-id params)
                       (:peer-id runtime)
                       "self-vote"))))  ; TODO: actual signature

(defn interpret-log-effect
  "Log a message."
  [runtime level message]
  ;; Simple println for now
  (when (#{:info :warn :error} level)
    (println "[" (:peer-id runtime) "]" (name level) "-" message)))

(defn interpret-persist-effect
  "Persist data to storage."
  [runtime key value]
  (go-try-
    ;; TODO: Add generic persistence mechanism
   nil))

(defn interpret-request-missing-proposal-effect
  "Request missing proposal from peers (currently no-op in mock network)."
  [runtime height round]
  ;; TODO: With real network (Kabel), send request to peers
  ;; For now, this is a no-op - MockNetwork doesn't support peer requests
  (println "[" (:peer-id runtime) "] DEBUG - Would request proposal for height" height "round" round))

(defn interpret-request-state-sync-effect
  "Request state sync from peers (currently no-op in mock network)."
  [runtime from-height to-height]
  ;; TODO: With real network (Kabel), request state from peers
  (println "[" (:peer-id runtime) "] DEBUG - Would request state sync from" from-height "to" to-height))

(defn interpret-request-votes-effect
  "Request votes from peers (currently no-op in mock network)."
  [runtime proposal-id height round]
  ;; TODO: With real network (Kabel), request votes from peers
  (println "[" (:peer-id runtime) "] DEBUG - Would request votes for proposal" proposal-id))

(defn interpret-broadcast-finalization-effect
  "Broadcast finalization to network."
  [runtime proposal height votes]
  (go-try-
   (<?- (net/broadcast! (:network runtime)
                        :finalizations
                        {:proposal proposal
                         :height height
                         :votes votes}))))

(defn interpret-trigger-next-round-effect
  "Trigger next round by scheduling a :start-round event."
  [runtime delay-ms]
  ;; Schedule :start-round event after delay
  #?(:clj
     (future
       (Thread/sleep delay-ms)
       (put! (:event-ch runtime) {:type :start-round}))
     :cljs
     (js/setTimeout
      #(put! (:event-ch runtime) {:type :start-round})
      delay-ms)))

(defn interpret-effect
  "Interpret a single effect and execute it."
  [runtime effect]
  (let [[effect-type params] effect]
    (case effect-type
      :broadcast
      (interpret-broadcast-effect runtime (:topic params) (:payload params))

      :set-timer
      (interpret-set-timer-effect runtime (:timer-id params) (:duration-ms params))

      :cancel-timer
      (interpret-cancel-timer-effect runtime (:timer-id params))

      :finalize
      (interpret-finalize-effect runtime (:proposal params) (:height params))

      :request-proposal
      (interpret-request-proposal-effect runtime params)

      :add-own-vote
      (interpret-add-own-vote-effect runtime params)

      :log
      (interpret-log-effect runtime (:level params) (:message params))

      :persist
      (interpret-persist-effect runtime (:key params) (:value params))

      ;; Recovery effects
      :request-missing-proposal
      (interpret-request-missing-proposal-effect runtime (:height params) (:round params))

      :request-state-sync
      (interpret-request-state-sync-effect runtime (:from-height params) (:to-height params))

      :request-votes
      (interpret-request-votes-effect runtime (:proposal-id params) (:height params) (:round params))

      :broadcast-finalization
      (interpret-broadcast-finalization-effect runtime (:proposal params) (:height params) (:votes params))

      :trigger-next-round
      (interpret-trigger-next-round-effect runtime (:delay-ms params))

      ;; Unknown effect
      (println "[" (:peer-id runtime) "] WARN - Unknown effect type:" effect-type))))

(defn interpret-effects
  "Interpret all effects from a state transition."
  [runtime effects]
  (doseq [effect effects]
    (interpret-effect runtime effect)))

;; ============================================================
;; Event Processing
;; ============================================================

(defn process-event
  "Process an event through the state machine and interpret effects."
  [runtime event]
  (let [sm (:state-machine runtime)
        sm-state (:sm-state runtime)
        current-state @sm-state

        ;; Run event through state machine
        {:keys [state effects]} (sm/handle-event sm current-state event)]

    ;; Update state
    (reset! sm-state state)

    ;; Interpret effects
    (interpret-effects runtime effects)))

;; ============================================================
;; Main Loop
;; ============================================================

(defn run-event-loop
  "Main event processing loop."
  [runtime]
  (let [event-ch (:event-ch runtime)
        control-ch (:control-ch runtime)
        running? (:running? runtime)]
    (go-loop-try- []
                  (if @running?
                    (alt!
                      event-ch ([event]
                                (when event
                                  (process-event runtime event)
                                  (recur)))

                      control-ch ([msg]
                      ;; Control message received - stop
                                  nil))
        ;; Not running - exit
                    nil))))

;; ============================================================
;; Message Handlers
;; ============================================================

(defn setup-network-handlers
  "Setup handlers for network messages."
  [runtime]
  (go-try-
   (let [event-ch (:event-ch runtime)
         network (:network runtime)]

      ;; Handle proposals
     (<?- (net/subscribe! network :proposals
                          (fn [{:keys [proposal height round sender]}]
                            (println "[" (:peer-id runtime) "] DEBUG - Received proposal from" sender "for height" height "round" round)
                            (put! event-ch
                                  {:type :proposal-received
                                   :proposal proposal
                                   :height height
                                   :round round
                                   :sender sender}))))

      ;; Handle votes
     (<?- (net/subscribe! network :votes
                          (fn [{:keys [proposal-id voter signature height round]}]
                            (println "[" (:peer-id runtime) "] DEBUG - Received vote from" voter "for proposal" proposal-id)
                            (put! event-ch
                                  {:type :vote-received
                                   :proposal-id proposal-id
                                   :voter voter
                                   :signature signature}))))

      ;; Handle finalizations (for catching up)
     (<?- (net/subscribe! network :finalizations
                          (fn [{:keys [proposal height votes sender]}]
                            (put! event-ch
                                  {:type :proposal-finalized
                                   :proposal proposal
                                   :height height})))))))

;; ============================================================
;; Public API
;; ============================================================

(defn start-runtime!
  "Start consensus runtime with given state machine.

  Args:
    config - Map with:
      :peer-id - This peer's ID
      :state-machine - ConsensusAlgorithm instance
      :network - ConsensusNetwork instance
      :consensus-log - ConsensusLog instance
      :on-propose - (fn []) → proposal
      :on-finalize - (fn [proposal height])

  Returns:
    Channel that yields ConsensusRuntime instance when ready"
  [{:keys [peer-id state-machine network consensus-log
           on-propose on-finalize]
    :as config}]

  (go-try-
   (let [;; Create initial state
         sm-state (atom (sm/initial-state state-machine config))

          ;; Create runtime
         runtime (map->ConsensusRuntime
                  {:peer-id peer-id
                   :state-machine state-machine
                   :network network
                   :consensus-log consensus-log
                   :sm-state sm-state
                   :timers (atom {})
                   :on-propose on-propose
                   :on-finalize on-finalize
                   :running? (atom true)
                   :event-ch (chan 100)
                   :control-ch (chan)})]

      ;; Setup network handlers
     (<?- (setup-network-handlers runtime))

      ;; Start event loop
     (run-event-loop runtime)

      ;; Don't auto-start consensus - let caller trigger it
      ;; when all validators are ready

     runtime)))

(defn stop-runtime!
  "Stop consensus runtime.

  Args:
    runtime - ConsensusRuntime instance

  Returns:
    Channel that completes when stopped"
  [runtime]
  (go-try-
    ;; Cancel all timers
   (doseq [[timer-id cancel-fn] @(:timers runtime)]
     (cancel-fn))

    ;; Stop event loop
   (reset! (:running? runtime) false)
   (close! (:control-ch runtime))

   true))

(defn send-event!
  "Send an event to the runtime for processing.

  Args:
    runtime - ConsensusRuntime instance
    event - Event map

  Returns:
    true if event was sent"
  [runtime event]
  (put! (:event-ch runtime) event))

(defn get-state
  "Get current state machine state.

  Args:
    runtime - ConsensusRuntime instance

  Returns:
    Current state map"
  [runtime]
  @(:sm-state runtime))
