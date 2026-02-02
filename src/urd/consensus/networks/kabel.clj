(ns urd.consensus.networks.kabel
  "Kabel-based P2P network implementation for consensus.

  Provides a real P2P network layer using Kabel WebSockets.
  This is one implementation of the ConsensusNetwork protocol."
  (:require [clojure.core.async :refer [chan close! put! <!! timeout]]
            [kabel.peer :as peer]
            [kabel.pubsub :as pubsub]
            [kabel.pubsub.protocol :as proto]
            [kabel.http-kit :as http-kit]
            [superv.async :refer [go-try- <? go-loop-try]]
            [urd.consensus.network :as net]))

;; ============================================================
;; Simple Pub/Sub Strategy for Consensus Messages
;; ============================================================

(defrecord ConsensusPubSubStrategy [handler-fn]
  proto/PSyncStrategy

  (-init-client-state [_]
    ;; No state needed - return empty state
    (let [ch (chan 1)]
      (put! ch {})
      (close! ch)
      ch))

  (-handshake-items [_ client-state]
    ;; No initial sync - just real-time messages
    (let [ch (chan 1)]
      (close! ch)
      ch))

  (-apply-handshake-item [_ item]
    ;; No handshake items to process
    (let [ch (chan 1)]
      (put! ch nil)
      (close! ch)
      ch))

  (-apply-publish [_ message]
    ;; Forward message to handler
    (when handler-fn
      (handler-fn message))
    (let [ch (chan 1)]
      (put! ch {:ok true})
      (close! ch)
      ch)))

(defn consensus-strategy
  "Create a simple pub/sub strategy that forwards messages to a handler."
  [handler-fn]
  (->ConsensusPubSubStrategy handler-fn))

;; ============================================================
;; Kabel Network Implementation
;; ============================================================

(defrecord KabelNetwork
           [peer-id              ; UUID - this peer's ID
            peer-atom            ; Atom<Kabel peer> - for broadcasting
            subscribe-peer-atom  ; Atom<Kabel peer> - for subscribing (may be same as peer-atom)
            supervisor           ; Supervisor for error handling
            url                  ; WebSocket URL (for logging/debugging)
            subscriptions]       ; Atom<Map<topic → handler>> - track active subscriptions

  net/ConsensusNetwork

  (broadcast! [this topic message]
    (go-try- supervisor
      ;; Add sender metadata
             (let [msg (assoc message
                              :sender peer-id
                              :timestamp (System/currentTimeMillis))]
               (<? supervisor (pubsub/publish! @peer-atom topic msg))
               true)))

  (subscribe! [this topic handler]
    (go-try- supervisor
      ;; Register in subscriptions map
             (swap! subscriptions assoc topic handler)

             (let [peer @subscribe-peer-atom
                   pubsub-state (or (:pubsub @peer) {})
                   has-out? (contains? pubsub-state :out)]

               (if has-out?
          ;; Client peer: use standard pubsub/subscribe!
                 (<? supervisor
                     (pubsub/subscribe! peer #{topic}
                                        {:strategies {topic (consensus-strategy handler)}}))

          ;; Server peer: create local subscription channel and add as subscriber
                 (let [local-sub-ch (chan 100)
                       strategy (consensus-strategy handler)]
            ;; Add local channel as a subscriber transport
                   (swap! peer update-in [:pubsub :topics topic :subscribers]
                          (fnil conj #{}) local-sub-ch)

            ;; Listen on local channel and forward to handler
                   (go-loop-try supervisor [msg (<? supervisor local-sub-ch)]
                                (when msg
                                  (let [{:keys [payload]} msg]
                  ;; Apply the strategy's publish handler
                                    (<? supervisor (proto/-apply-publish strategy payload)))
                                  (recur (<? supervisor local-sub-ch)))))))

      ;; Return subscription handle
             {:topic topic :handler handler}))

  (unsubscribe! [this topic handle]
    (go-try- supervisor
      ;; Remove from subscriptions map
             (swap! subscriptions dissoc topic)

             (let [peer @subscribe-peer-atom
                   pubsub-state (or (:pubsub @peer) {})
                   has-out? (contains? pubsub-state :out)]

               (if has-out?
          ;; Client peer: use standard unsubscribe
                 (<? supervisor (pubsub/unsubscribe! peer #{topic}))

          ;; Server peer: remove local subscription channel
          ;; (Channel will be closed when consensus shuts down)
                 nil))

             true))

  (get-peer-count [this]
    (go-try- supervisor
      ;; TODO: Track connected peers in Kabel
      ;; For now, return 1 (ourselves)
             1))

  (close-network! [this]
    (go-try- supervisor
      ;; Unsubscribe from all topics
             (doseq [topic (keys @subscriptions)]
               (<? supervisor (pubsub/unsubscribe! @subscribe-peer-atom #{topic})))

      ;; Stop both peers (if different)
             (when (not= @subscribe-peer-atom @peer-atom)
               (<? supervisor (peer/stop @subscribe-peer-atom)))
             (<? supervisor (peer/stop @peer-atom))
             true)))

;; ============================================================
;; Factory Functions
;; ============================================================

(defn create-kabel-server
  "Create a Kabel network peer that acts as a server.

  Uses a single server peer for both broadcasting and subscribing.
  Local subscriptions are handled by adding local channels as subscribers.

  Args:
    supervisor - superv.async supervisor
    peer-id - UUID for this peer
    port - Port to listen on (e.g., 47291)

  Returns:
    Channel yielding KabelNetwork instance"
  [supervisor peer-id port]
  (go-try- supervisor
           (let [url (str "ws://localhost:" port)

          ;; Create HTTP handler for WebSocket upgrades
                 handler (http-kit/create-http-kit-handler! supervisor url peer-id)

          ;; Create server peer with pubsub middleware
                 server-peer (peer/server-peer
                              supervisor
                              handler
                              peer-id
                              (pubsub/make-pubsub-peer-middleware {})
                              identity)]

      ;; Start the server peer (starts HTTP server)
             (<? supervisor (peer/start server-peer))
             (println "[" peer-id "] Kabel server started on" url)

      ;; Wait a bit for server to be ready
             (<!! (timeout 500))

      ;; Use server peer for both broadcasting and subscribing
      ;; No need for client peer loopback
             (->KabelNetwork
              peer-id
              (atom server-peer)      ; Use server peer for broadcasting
              (atom server-peer)      ; Use same peer for subscribing
              supervisor
              url
              (atom {})))))

(defn create-kabel-client
  "Create a Kabel network peer that connects to a server.

  Args:
    supervisor - superv.async supervisor
    peer-id - UUID for this peer
    server-url - URL to connect to (e.g., \"ws://localhost:47291\")

  Returns:
    Channel yielding KabelNetwork instance"
  [supervisor peer-id server-url]
  (go-try- supervisor
           (let [;; Create client peer with pubsub middleware
                 kabel-peer (peer/client-peer
                             supervisor
                             peer-id
                             (pubsub/make-pubsub-peer-middleware {})
                             identity)]  ;; No special serialization for now

      ;; Connect to server
             (<? supervisor (peer/connect supervisor kabel-peer server-url))

             (println "[" peer-id "] Kabel client connected to" server-url)

             (->KabelNetwork
              peer-id
              (atom kabel-peer)           ; Use same peer for broadcasting
              (atom kabel-peer)           ; Use same peer for subscribing
              supervisor
              server-url
              (atom {})))))

;; ============================================================
;; Topic Registration (Server-Side)
;; ============================================================

(defn register-consensus-topics!
  "Register consensus topics on a server peer.

  This should be called on the server peer after creation
  to enable pub/sub for consensus messages.

  Args:
    kabel-network - KabelNetwork instance (server)

  Returns:
    Channel that yields true when complete"
  [kabel-network]
  (go-try- (:supervisor kabel-network)
           (let [peer @(:peer-atom kabel-network)
                 supervisor (:supervisor kabel-network)
          ;; Create a simple pass-through strategy for server-side
          ;; No initial state to sync, just forward published messages
                 server-strategy (consensus-strategy nil)]

      ;; Register standard consensus topics with strategy
      ;; Note: register-topic! returns synchronously, not a channel
             (pubsub/register-topic! peer :proposals {:strategy server-strategy})
             (pubsub/register-topic! peer :votes {:strategy server-strategy})
             (pubsub/register-topic! peer :finalizations {:strategy server-strategy})

             (println "[" (:peer-id kabel-network) "] Consensus topics registered")
             true)))
