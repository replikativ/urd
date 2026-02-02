(ns urd.consensus.network-helper
  "Helper functions for creating test networks of validators."
  (:require [clojure.core.async :refer [<!! timeout]]
            [superv.async :refer [S <?? go-try-]]
            [urd.consensus.validator :as validator]))

(defn create-test-validator-set
  "Create a test validator set with N validators."
  [n]
  (into {}
        (map (fn [i]
               [(java.util.UUID/randomUUID) (str "pubkey-" i)])
             (range n))))

(defn create-test-proposal
  "Create a test proposal for consensus."
  [validator-id counter]
  {:snapshot-id (java.util.UUID/randomUUID)
   :data (str "Proposal-" validator-id "-" counter)
   :timestamp (System/currentTimeMillis)})

(defn start-kabel-network!
  "Helper to start a network of validators using Kabel P2P.

  Args:
    n - Number of validators
    opts - Options map:
      :base-port - Starting port (default 47300)
      :on-propose - (fn [validator-id]) -> proposal (required)
      :on-finalize - (fn [validator-id proposal height]) (optional)

  Returns:
    Channel yielding map with:
      :validators - Vector of Validator instances
      :validator-set - The validator set used
      :validator-ids - Vector of validator IDs"
  [n opts]
  (go-try- S
           (let [validator-set (create-test-validator-set n)
                 validator-ids (vec (keys validator-set))
                 base-port (or (:base-port opts) 47300)
                 server-url (str "ws://localhost:" base-port)
                 on-propose (:on-propose opts)
                 on-finalize (:on-finalize opts)

          ;; Start server validator
                 server-id (nth validator-ids 0)
                 server-config {:peer-id server-id
                                :validator-set validator-set
                                :network-type :kabel
                                :port base-port
                                :on-propose (fn [] (on-propose server-id))
                                :on-finalize (when on-finalize
                                               (fn [p h] (on-finalize server-id p h)))}

                 server (<?? S (validator/start-validator! server-config))

          ;; Wait for server to be ready
                 _ (<!! (timeout 1000))

          ;; Start client validators
                 clients (loop [i 1, cs []]
                           (if (< i n)
                             (let [vid (nth validator-ids i)
                                   client-config {:peer-id vid
                                                  :validator-set validator-set
                                                  :network-type :kabel
                                                  :connect-to server-url
                                                  :on-propose (fn [] (on-propose vid))
                                                  :on-finalize (when on-finalize
                                                                 (fn [p h] (on-finalize vid p h)))}
                                   client (<?? S (validator/start-validator! client-config))
                                   _ (<!! (timeout 500))]
                               (recur (inc i) (conj cs client)))
                             cs))]

      ;; Wait for all connections to establish
             (<!! (timeout 2000))

             {:validators (into [server] clients)
              :validator-set validator-set
              :validator-ids validator-ids})))

(defn stop-network!
  "Stop all validators in a network.

  Args:
    network - Map returned from start-kabel-network!

  Returns:
    Channel yielding true when all stopped"
  [network]
  (go-try- S
           (doseq [v (:validators network)]
             (<?? S (validator/stop-validator! v)))
           true))

(defn start-all-consensus!
  "Start consensus on all validators in a network.

  Args:
    network - Map returned from start-kabel-network!"
  [network]
  (doseq [v (:validators network)]
    (validator/send-event! v {:type :start-round})))

(defn get-all-finalized
  "Get finalized heights from all validators.

  Returns:
    Vector of maps with :validator-id and :finalized"
  [network]
  (mapv (fn [v]
          {:validator-id (:peer-id v)
           :finalized (validator/get-finalized v)})
        (:validators network)))
