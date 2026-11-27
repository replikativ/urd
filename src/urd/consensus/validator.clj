(ns urd.consensus.validator
  "Main API for creating and managing consensus validators.

  A validator encapsulates:
  - Consensus state machine (the algorithm)
  - Network interface (simulation or real P2P)
  - Runtime (effect interpreter)
  - Storage (consensus log)

  This is the primary entry point for using the consensus system."
  (:require [clojure.core.async :refer [<! <!! timeout]]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [superv.async :refer [S <?? <?- go-try-]]
            [urd.consensus.runtime :as runtime]
            [urd.consensus.node :as node]
            [urd.consensus.network :as net]
            [urd.consensus.networks.kabel :as kabel]
            [urd.consensus.networks.simulation :as sim]
            [urd.consensus.algorithms.round-robin :as rr])
  (:gen-class))

;; ============================================================
;; Validator Record
;; ============================================================

(defrecord Validator
           [peer-id       ; UUID - this validator's ID
            state         ; Atom - internal state (network, runtime, etc.)
            config])      ; Config used to create this validator

;; ============================================================
;; Network Creation
;; ============================================================

(defn- create-network
  "Create network based on config.

  Config options:
  - :network-type - :simulation or :kabel (required)
  - :router - For simulation: shared router atom
  - :port - For kabel server: port to listen on
  - :connect-to - For kabel client: URL to connect to"
  [peer-id config]
  (go-try-
   (case (:network-type config)
     :simulation
     (let [router (:router config)]
       (when-not router
         (throw (ex-info "Simulation network requires :router" {})))
       (sim/create-simulation-network peer-id router))

     :kabel
     (if-let [port (:port config)]
        ;; Server mode
       (let [server (<?- (kabel/create-kabel-server S peer-id port))]
                 ;; The topics the NODE declares, not a hardcoded list. A topic
                 ;; the server has not registered never delivers, and it fails
                 ;; silently -- which is why only round-robin worked over kabel
                 ;; until this was threaded through.
         (<?- (kabel/register-consensus-topics! server (:topics config)))
          ;; Wait for server to be ready
         (<! (timeout 500))
         server)
        ;; Client mode
       (let [connect-to (:connect-to config)]
         (when-not connect-to
           (throw (ex-info "Kabel client mode requires :connect-to" {})))
         (let [client (<?- (kabel/create-kabel-client S peer-id connect-to))]
            ;; Wait for connection to establish
           (<! (timeout 1000))
           client)))

     (throw (ex-info "Unknown network type"
                     {:network-type (:network-type config)
                      :valid-types [:simulation :kabel]})))))

;; ============================================================
;; Public API
;; ============================================================

(defn start-validator!
  "Start a validator with given configuration.

  Required config:
    :peer-id - UUID for this validator
    :validator-set - Map of {peer-id -> public-key}
    :network-type - :simulation or :kabel

  Network-specific config:
    For :simulation:
      :router - Shared router atom (from sim/create-router)

    For :kabel:
      :port - Port to listen on (server mode)
      OR
      :connect-to - URL to connect to (client mode)

  Optional config:
    :on-propose - (fn [context]) -> proposal, or (fn []) (default: throws)
    :on-finalize - (fn [vertices]), or the legacy (fn [proposal height])

  Returns:
    Channel yielding Validator instance"
  [config]
  (go-try-
   (let [{:keys [peer-id validator-set on-propose on-finalize]} config

          ;; Validate required config
         ;; `(keys config)`, not `config`. The map carries `:private-key`, and
          ;; ex-data gets logged, printed and shipped to error trackers.
         _ (when-not peer-id
             (throw (ex-info "config missing :peer-id"
                             {:provided (sort (keys config))})))
         _ (when-not validator-set
             (throw (ex-info "config missing :validator-set"
                             {:provided (sort (keys config))})))

          ;; Create state machine
                 ;; A `urd.consensus.node/Node`. This used to be a
                 ;; `ConsensusAlgorithm` from the retired `state-machine`
                 ;; namespace -- one protocol now, see section 23.
                 ;;
                 ;; Overridable via `:node`, and that seam is not decoration.
                 ;; Building the node internally meant nothing could WRAP it,
                 ;; so `trace/tracing` -- the one tool that distinguishes "this
                 ;; validator is receiving nothing" from "it receives and does
                 ;; not act" -- could not be attached to a validator at all.
                 ;; Diagnosing the kabel layer then had no instrument, and five
                 ;; rounds went into inferring from symptoms what one traced run
                 ;; would have shown.
         node (or (:node config) (rr/create validator-set))

          ;; The network is created AFTER the node, because a kabel SERVER must
          ;; register exactly the topics the node declares -- an unregistered
          ;; topic never delivers, silently. Building the network first meant
          ;; the topic list could only ever be a hardcoded guess, which is why
          ;; round-robin was the only algorithm that worked over kabel.
         network (<?- (create-network peer-id
                                      (assoc config :topics
                                             (node/check-topics node))))

          ;; Default callbacks
         default-on-propose (fn []
                              (throw (ex-info "No :on-propose callback provided" {})))
         default-on-finalize (fn [proposal height] nil)

          ;; Start consensus runtime
          ;; Everything the runtime accepts is reachable from here. It used to
          ;; be six keys, so `:store`, `:validators`, `:on-error`, `:on-revert`,
          ;; `:on-resync` and `:on-equivocation` were unreachable through the
          ;; public API: a validator could not be given durable storage, and
          ;; Snowman's sampler received an empty validator list and silently
          ;; never polled.
                 ;; An ALLOW-LIST silently drops everything it has not heard
                 ;; of, and what it had not heard of was every algorithm's own
                 ;; configuration: `:gossip-interval`, `:gc-depth`,
                 ;; `:anchor-wait-ticks`, `:snapshot-interval`, and whatever
                 ;; the next algorithm needs. The runtime hands its whole
                 ;; config to `node/init`, so those keys are reachable there --
                 ;; they just never survived this function.
                 ;;
                 ;; Measured cost of that: Tendermint's `:gossip-interval` is
                 ;; the rate at which a lagging node catches up, one height per
                 ;; interval, and it could not be tuned through the only public
                 ;; way to start a validator.
                 ;;
                 ;; So it is a DENY-list now, naming the keys that belong to
                 ;; the validator rather than to the runtime. A new algorithm
                 ;; knob works without editing this file, which is the whole
                 ;; point of the runtime taking its config wholesale.
         runtime-config (merge
                         (apply dissoc config
                                [:network-type :port :connect-to :node
                                 :validator-set :on-propose :on-finalize])
                         {:peer-id peer-id
                          :node node
                          :network network
                          :validator-set validator-set
                                  ;; The sampler draws from this; without it
                                  ;; `do-sample` can only warn.
                          :validators (or (:validators config)
                                          (vec (sort (keys validator-set))))
                          :on-propose (or on-propose default-on-propose)
                          :on-finalize (or on-finalize default-on-finalize)})

         runtime (<?- (runtime/start-runtime! runtime-config))]

     (->Validator
      peer-id
      (atom {:runtime runtime
             :network network
             :config config})
      config))))

(defn stop-validator!
  "Stop a running validator.

  Returns:
    Channel yielding true when stopped"
  [validator]
  (go-try-
   (let [{:keys [runtime network]} @(:state validator)]
     (<?- (runtime/stop-runtime! runtime))
     (<?- (net/close-network! network))
     true)))

(defn send-event!
  "Send an event to the validator's consensus runtime.

  Args:
    validator - Validator instance
    event - Event map (e.g., {:type :start-round})

  Returns:
    true if event was sent"
  [validator event]
  (let [runtime (get-in @(:state validator) [:runtime])]
    (runtime/send-event! runtime event)))

(defn get-state
  "Get current state machine state.

  Returns:
    State map with :height, :round, :finalized, etc."
  [validator]
  (let [runtime (get-in @(:state validator) [:runtime])]
    (runtime/get-state runtime)))

(defn get-finalized
  "Get finalized proposals from validator's state machine.

  Returns:
    Map of {height -> proposal}"
  [validator]
  (:finalized (get-state validator)))

;; ============================================================
;; CLI Entry Point (For JVM process deployment)
;; ============================================================

(defn load-validator-config
  "Load validator configuration from file or use defaults.

  Config file should be EDN with:
  {:peer-id #uuid \"...\"
   :network-type :kabel
   :port 47291
   :validator-set {#uuid \"v1\" \"pubkey-1\" ...}
   :connect-to \"ws://localhost:47292\"}"
  [config-path]
  (if (and config-path (.exists (io/file config-path)))
    (edn/read-string (slurp config-path))
    ;; Default config for testing
    (let [v1 (java.util.UUID/randomUUID)
          v2 (java.util.UUID/randomUUID)
          v3 (java.util.UUID/randomUUID)]
      {:peer-id (java.util.UUID/randomUUID)
       :network-type :kabel
       :port 47291
       :validator-set {v1 "key-1"
                       v2 "key-2"
                       v3 "key-3"}})))

(def proposal-counter (atom 0))

(defn create-test-proposal
  "Create a test proposal for consensus."
  [peer-id]
  {:snapshot-id (java.util.UUID/randomUUID)
   :data (str "Proposal from " peer-id " #" (swap! proposal-counter inc))
   :timestamp (System/currentTimeMillis)})

(defn -main
  "Run a validator node.

  Usage:
    clojure -M -m urd.consensus.validator <config-file>

  Or with default config:
    clojure -M -m urd.consensus.validator"
  [& args]
  (let [config-path (first args)
        config (load-validator-config config-path)
        peer-id (:peer-id config)

        ;; Add CLI-specific callbacks
        config-with-callbacks (assoc config
                                     :on-propose #(create-test-proposal peer-id)
                                     :on-finalize (fn [proposal height]
                                                    (println "[" peer-id "] FINALIZED height" height
                                                             ":" (:data proposal))))

        validator (<?? S (start-validator! config-with-callbacks))]

    (println "\n========================================")
    (println "Validator Running")
    (println "========================================")
    (println "Peer ID:" peer-id)
    (println "Network:" (:network-type config))
    (println "Press Ctrl-C to stop")
    (println "========================================\n")

    ;; Start consensus
    (send-event! validator {:type :start-round})

    ;; Keep running until interrupted
    (try
      @(promise)
      (catch InterruptedException e
        (println "\nShutting down...")
        (<?? S (stop-validator! validator))
        (System/exit 0)))))
