(ns urd.consensus.network
  "Network abstraction for consensus protocols.

  Provides both mock (in-memory) and real (kabel) implementations."
  (:require #?(:clj [clojure.core.async :refer [chan pub sub unsub put! close! >! <! timeout]]
               :cljs [clojure.core.async :refer [chan pub sub unsub put! close! >! <! timeout]])
            [superv.async :refer [go-try- <?-]]))

;; ============================================================
;; Network Protocol
;; ============================================================

(defprotocol ConsensusNetwork
  "Abstract network interface for consensus communication."

  (broadcast! [this topic message]
    "Broadcast message to all peers on topic.
     Returns channel that completes when sent.")

  (subscribe! [this topic handler]
    "Subscribe to messages on topic.
     Handler is (fn [message] ...) called for each message.
     Returns channel that yields subscription handle.")

  (unsubscribe! [this topic handle]
    "Unsubscribe from topic.
     Returns channel that completes when unsubscribed.")

  (get-peer-count [this]
    "Get number of connected peers.
     Returns channel yielding count.")

  (close-network! [this]
    "Close all connections and cleanup.
     Returns channel that completes when closed."))

;; ============================================================
;; Mock Network (In-Memory)
;; ============================================================

(defrecord MockNetwork
           [peer-id              ; UUID - this peer's ID
            peers                ; Atom<Map<peer-id → peer-state>>
            bus                  ; Channel - message bus
            pub-bus              ; Publication from bus
            subscriptions        ; Atom<Map<topic → #{handlers}>>
            partition-filter     ; Optional: Atom<Set<peer-ids>> that can receive messages
            message-delay]       ; Optional: Map with :min-ms :max-ms for latency simulation

  ConsensusNetwork

  (broadcast! [this topic message]
    (go-try-
      ;; Add metadata
     (let [msg (assoc message
                      :topic topic
                      :sender peer-id
                      :timestamp (System/currentTimeMillis))

            ;; Apply delay if configured
           delay-ms (when message-delay
                      (+ (:min-ms message-delay)
                         (rand-int (- (:max-ms message-delay)
                                      (:min-ms message-delay)))))]

        ;; Wait for simulated network delay
       (when delay-ms
         (<?- (timeout delay-ms)))

        ;; Put on bus (pub-bus will distribute)
       (>! bus {:type topic
                :payload msg})

        ;; Return immediately
       true)))

  (subscribe! [this topic handler]
    (go-try-
      ;; Create subscription channel
     (let [sub-ch (chan 100)]

        ;; Subscribe to pub-bus
       (sub pub-bus topic sub-ch)

        ;; Process messages in background
       (go-try-
        (loop []
          (when-let [msg (<?- sub-ch)]
            (let [payload (:payload msg)
                  sender (:sender payload)
                  partition @partition-filter
                  should-deliver (or (nil? partition)
                                     (contains? partition sender))]

                ;; DEBUG: Log partition filtering
              (when false ;; partition$
                (println "[PARTITION]" peer-id "received from" sender
                         "- deliver?" should-deliver
                         "partition:" partition))

                ;; Apply partition filter - only deliver if sender is in same partition
              (when should-deliver
                  ;; Call handler
                (try
                  (handler payload)
                  (catch #?(:clj Exception :cljs js/Error) e
                    #?(:clj (.printStackTrace e))))))
            (recur))))

        ;; Track subscription
       (swap! subscriptions update topic (fnil conj #{}) handler)

        ;; Return handle for unsubscribe
       {:topic topic
        :channel sub-ch
        :handler handler})))

  (unsubscribe! [this topic {:keys [channel handler]}]
    (go-try-
      ;; Unsubscribe from pub-bus
     (unsub pub-bus topic channel)
     (close! channel)

      ;; Remove from tracking
     (swap! subscriptions update topic disj handler)

     true))

  (get-peer-count [this]
    (go-try-
     (count @peers)))

  (close-network! [this]
    (go-try-
      ;; Close all subscription channels
     (doseq [[topic handlers] @subscriptions
             handler handlers]
       (<?- (unsubscribe! this topic {:handler handler})))

      ;; Close bus
     (close! bus)

     true)))

(defn create-mock-network
  "Create an in-memory mock network for testing.

   Args:
     peer-id - UUID for this peer
     shared-bus - Optional shared bus for multi-peer simulation

   Returns:
     MockNetwork instance"
  ([peer-id]
   (create-mock-network peer-id (chan 1000)))
  ([peer-id shared-bus]
   (let [pub-bus (pub shared-bus :type)]
     (->MockNetwork
      peer-id
      (atom {})
      shared-bus
      pub-bus
      (atom {})
      (atom nil)  ; partition-filter (none by default)
      nil  ; message-delay (none by default)
      ))))

;; ============================================================
;; Mock Network Cluster (Multi-Peer Simulation)
;; ============================================================

(defn create-mock-cluster
  "Create a cluster of interconnected mock networks.

   All peers share the same message bus, simulating perfect
   broadcast network (no partitions, no message loss).

   Args:
     peer-ids - Collection of peer UUIDs

   Returns:
     Map of {peer-id → MockNetwork}"
  [peer-ids]
  (let [;; Shared bus for all peers
        shared-bus (chan 10000)
        ;; Shared publication (so all peers receive from same pub)
        shared-pub (pub shared-bus :type)]

    ;; Create network for each peer, sharing both bus AND pub
    (into {}
          (map (fn [peer-id]
                 [peer-id (->MockNetwork
                           peer-id
                           (atom {})
                           shared-bus
                           shared-pub  ; Use shared publication
                           (atom {})
                           (atom nil)  ; partition-filter (none by default)
                           nil  ; message-delay (none by default)
                           )])
               peer-ids))))

(defn find-partition
  "Find which partition a peer belongs to.

   Args:
     peer-id - UUID of peer
     partitions - Vector of peer-id sets

   Returns:
     Set of peers in same partition, or nil if not found"
  [peer-id partitions]
  (first (filter #(contains? % peer-id) partitions)))

(defn simulate-network-partition
  "Simulate network partition by filtering messages.

   Creates partitions where peers can only communicate
   within their partition group. Messages between partitions are dropped.

   Args:
     networks - Map of {peer-id → MockNetwork}
     partitions - Vector of peer-id sets, e.g. [#{p1 p2} #{p3 p4}]

   Returns:
     Map of {peer-id → MockNetwork} (same instances, partition-filter atoms modified)"
  [networks partitions]
  ;; Modify partition-filter atoms in place
  (doseq [[peer-id network] networks]
    (let [my-partition (find-partition peer-id partitions)]
      (reset! (:partition-filter network) my-partition)))
  networks)

(defn simulate-message-delay
  "Add random delays to messages (simulates network latency).

   Adds delay-ms field to network that causes messages to be
   delivered after a random delay.

   Args:
     network - MockNetwork
     min-ms - Minimum delay in milliseconds
     max-ms - Maximum delay in milliseconds

   Returns:
     Network with delay configuration"
  [network min-ms max-ms]
  ;; Add delay configuration to network
  (assoc network :message-delay {:min-ms min-ms :max-ms max-ms}))

(defn heal-partition
  "Remove partition filter from networks, restoring full connectivity.

   Args:
     networks - Map of {peer-id → MockNetwork}

   Returns:
     Map of {peer-id → MockNetwork} (same instances, partition-filter atoms reset to nil)"
  [networks]
  ;; Reset partition-filter atoms to nil
  (doseq [[peer-id network] networks]
    (reset! (:partition-filter network) nil))
  networks)

(defn remove-message-delay
  "Remove message delay from network, restoring instant delivery.

   Args:
     network - MockNetwork

   Returns:
     Network with delay removed"
  [network]
  (assoc network :message-delay nil))

;; ============================================================
;; Network Statistics
;; ============================================================

(defn network-stats
  "Get statistics about network activity.

   Args:
     network - MockNetwork instance

   Returns:
     Map with :messages-sent, :messages-received, etc."
  [network]
  {:peer-id (:peer-id network)
   :subscriptions (into {}
                        (map (fn [[topic handlers]]
                               [topic (count handlers)])
                             @(:subscriptions network)))})
