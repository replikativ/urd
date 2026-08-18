(ns urd.consensus.networks.kabel
  "Kabel-based P2P network implementation for consensus.

  Provides a real P2P network layer using Kabel WebSockets.
  This is one implementation of the ConsensusNetwork protocol."
  (:require [clojure.core.async :refer [chan close! put! <!! timeout]]
            [kabel.peer :as peer]
            [kabel.middleware.cbor :refer [cbor]]
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
      ;; The number of SUBSCRIBERS the pubsub layer holds, which on a server
      ;; peer is the local subscription plus one transport per connected client.
      ;;
      ;; This used to be `1`, with a TODO. That is worse than unimplemented: it
      ;; is a readiness predicate that always answers "ready", so a caller had
      ;; no way to tell a joined network from a partial one and every wait in
      ;; the test helper had to be a fixed sleep. When a sleep was too short the
      ;; network came up missing a member and -- since a majority of the rest is
      ;; still a quorum -- consensus proceeded without it, which reads exactly
      ;; like a broken algorithm. Several hours went into that misreading.
      ;;
      ;; MINIMUM across topics, and the previous `max` here was the bug.
      ;;
      ;; A client subscribes to each topic separately, so the counts climb
      ;; independently. The maximum reaches n the moment the FASTEST topic is
      ;; complete, which is the earliest instant at which anyone could call the
      ;; network assembled -- while a node may still be missing `:proposals` or
      ;; `:finalizations`. A node is a participant only once it is on every
      ;; topic, so readiness is the SLOWEST topic: the minimum.
      ;;
      ;; The old comment argued that a per-topic count is "a lower bound while
      ;; the handshakes are still landing", and then took the max. That is
      ;; backwards -- a lower bound per topic is exactly why the minimum is the
      ;; one that must reach n.
      ;;
      ;; Measured. Under `max`, five validators repeatedly split 3/0/0 and
      ;; 2/2/2/0/0: some finalize and the rest finalize EXACTLY zero, never
      ;; fewer-but-nonzero. A node that missed `:proposals` and
      ;; `:finalizations` hears nothing and commits nothing, ever, while the
      ;; remaining majority is still a quorum and proceeds without it.
             (let [peer @subscribe-peer-atom
                   counts (map (comp count :subscribers)
                               (vals (get-in @peer [:pubsub :topics])))]
               (if (seq counts) (reduce min counts) 0))))

  (close-network! [this]
    (go-try- supervisor
      ;; NO unsubscribe. Stopping the peer is the disconnect, and announcing it
      ;; first is politeness that can hang forever.
      ;;
      ;; `pubsub/unsubscribe!` ends in `(>? S out ...)` -- a PARKING put on the
      ;; peer's outbound channel. `stop-network!` stops the server first, which
      ;; closes every client's websocket, so by the time the clients tear down
      ;; the consumer of that channel is gone. The put then parks forever, and
      ;; whether a given client hangs depends on whether its out-channel buffer
      ;; still had room -- which is exactly why roughly one run in six hung and
      ;; the rest did not.
      ;;
      ;; Measured, with the steps traced: the server completed all five
      ;; unsubscribes and stopped cleanly; three of four clients printed
      ;; `unsubscribe :proposals` and never returned.
      ;;
      ;; The asymmetry that made this a trap has since been fixed upstream --
      ;; `publish!` used `put?` with a callback so it could detect a closed
      ;; subscriber and remove it, while `unsubscribe!` used `>?` and parked.
      ;; kabel 0.3.107 (replikativ/kabel#21) brings unsubscribe into line, and
      ;; the exact code below, restored verbatim, then completed 40 out of 40
      ;; teardowns against it where it had hung on the first attempt before.
      ;;
      ;; We still do not send it. The fix means an unsubscribe to a dead peer
      ;; no longer hangs; it does not make the message useful. Stopping the
      ;; peer is the disconnect, and the server drops the subscriber when its
      ;; next publish to that transport fails, so announcing it first buys
      ;; nothing on a path where the peer we would be telling is already gone.
      ;;
      ;; Dropping the message costs nothing here. The server removes a
      ;; subscriber when its transport put fails, so the disconnect
      ;; deregisters us anyway; the unsubscribe was only ever an optimisation
      ;; to deregister a little sooner. The `unsubscribe!` METHOD above still
      ;; sends it, because that is a live operation on a live connection --
      ;; the caller is staying connected and genuinely wants the server told.
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
                              ;; CBOR, not the `identity` stub. With no
                              ;; serialization middleware kabel falls back to
                              ;; `(.getBytes (pr-str m))` under codec id
                              ;; `:pr-str` (binary.clj:15-18) -- so every urd
                              ;; frame was EDN text that only a Clojure reader
                              ;; could parse, and a non-Clojure peer would have
                              ;; to implement EDN before it could say anything.
                              ;;
                              ;; kabel's CBOR is RFC 8949 with stringref
                              ;; deliberately OFF, so cbor-x, fxamacker/cbor
                              ;; and ciborium all read it. That is the whole
                              ;; interop story for one line.
                              cbor)]

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
                             cbor)]  ;; see the server peer above

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
  "Register the topics a node will use on the SERVER peer.

  `topics` is the set the node declares through `node/check-topics`, plus
  `:direct` for emulated unicast. It used to be a hardcoded list --
  `:proposals :votes :finalizations :recovery :direct` -- which is
  round-robin's vocabulary, and a topic the server has not registered simply
  never delivers.

  That made round-robin the ONLY algorithm that could work over kabel:
  Tendermint broadcasts on `:consensus`, SCP on `:scp`, Bullshark on
  `:bullshark`, Nakamoto on `:headers`, and every one of those went to a topic
  the server had never heard of. It fails silently -- a node that starts
  cleanly, reports no error, and makes no progress.

  The runtime's SUBSCRIPTION side of this was fixed when topics became part of
  the capability declaration; this registration side was missed in the same
  change, and the comment left here pointed at `runtime/consensus-topics`,
  which that change deleted. Half a fix reads exactly like a whole one.

  Args:
    kabel-network - KabelNetwork instance (server)
    topics        - set of topic keywords the node declares

  Returns:
    Channel that yields true when complete"
  ;; No defaulting arity. A call that registers nothing looks identical to a
  ;; call that registers everything until a message silently fails to deliver,
  ;; which is the whole failure this function was rewritten to prevent.
  [kabel-network topics]
  (go-try- (:supervisor kabel-network)
           (let [peer @(:peer-atom kabel-network)
                 server-strategy (consensus-strategy nil)
                 ;; `:direct` is not an algorithm's topic; it is where the
                 ;; runtime emulates `send-to`, so it is always needed.
                 all (conj (set topics) :direct)]
             (doseq [topic (sort-by str all)]
               (pubsub/register-topic! peer topic {:strategy server-strategy}))
             (println "[" (:peer-id kabel-network) "] registered topics"
                      (vec (sort-by str all)))
             true)))
