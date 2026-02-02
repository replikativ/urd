(ns urd.consensus.networks.simulation
  "Simulation network for in-process testing.

  Routes messages between validators in the same process, allowing
  fast deterministic testing of consensus logic without real networking."
  (:require [clojure.core.async :refer [chan go >! <!  put! close!]]
            [urd.consensus.network :as net]))

;; ============================================================
;; Simulation Network Router
;; ============================================================

(defn create-router
  "Create a message router for simulation.

  Routes messages between validators in-process."
  []
  (atom {:peers {}          ; {peer-id -> {topic -> handler}}
         :message-log []}))  ; Log of all messages (for debugging)

(defn register-peer!
  "Register a peer with the router."
  [router peer-id]
  (swap! router assoc-in [:peers peer-id] {}))

(defn unregister-peer!
  "Unregister a peer from the router."
  [router peer-id]
  (swap! router update :peers dissoc peer-id))

(defn register-handler!
  "Register a handler for a topic on a peer."
  [router peer-id topic handler]
  (swap! router assoc-in [:peers peer-id topic] handler))

(defn unregister-handler!
  "Unregister a handler for a topic on a peer."
  [router peer-id topic]
  (swap! router update-in [:peers peer-id] dissoc topic))

(defn deliver-message!
  "Deliver a message to all peers subscribed to topic.

  Simulates broadcasting - delivers to all peers except sender."
  [router sender-id topic message]
  (let [peers @router
        msg-with-meta (assoc message
                             :sender sender-id
                             :timestamp #?(:clj (System/currentTimeMillis)
                                           :cljs (.now js/Date)))]

    ;; Log message (for debugging)
    (swap! router update :message-log conj
           {:sender sender-id
            :topic topic
            :message msg-with-meta
            :timestamp (:timestamp msg-with-meta)})

    ;; Deliver to all peers with handlers for this topic
    (doseq [[peer-id topics] (get peers :peers)
            :when (not= peer-id sender-id)  ; Don't deliver to self
            :let [handler (get topics topic)]
            :when handler]
      ;; Deliver asynchronously (simulate network delay)
      (go
        ;; Optional: simulate network delay
        ;; (<! (timeout (rand-int 10)))
        (handler msg-with-meta)))))

;; ============================================================
;; SimulationNetwork Implementation
;; ============================================================

(defrecord SimulationNetwork
           [peer-id       ; UUID - this peer's ID
            router        ; Atom<Router> - shared message router
            subscriptions] ; Atom<Map<topic → handler>> - local subscriptions

  net/ConsensusNetwork

  (broadcast! [this topic message]
    (go
      (deliver-message! router peer-id topic message)
      true))

  (subscribe! [this topic handler]
    (go
      ;; Store subscription locally
      (swap! subscriptions assoc topic handler)

      ;; Register with router
      (register-handler! router peer-id topic handler)

      ;; Return subscription handle
      {:topic topic :handler handler}))

  (unsubscribe! [this topic handle]
    (go
      ;; Remove local subscription
      (swap! subscriptions dissoc topic)

      ;; Unregister from router
      (unregister-handler! router peer-id topic)

      true))

  (get-peer-count [this]
    (go
      (count (get-in @router [:peers]))))

  (close-network! [this]
    (go
      ;; Unsubscribe from all topics
      (doseq [topic (keys @subscriptions)]
        (unregister-handler! router peer-id topic))

      ;; Unregister peer
      (unregister-peer! router peer-id)

      true)))

;; ============================================================
;; Public API
;; ============================================================

(defn create-simulation-network
  "Create a simulation network for a peer.

  Args:
    peer-id - UUID for this peer
    router - Shared router atom (from create-router)

  Returns:
    SimulationNetwork instance"
  [peer-id router]
  (register-peer! router peer-id)
  (->SimulationNetwork peer-id router (atom {})))

(defn get-message-log
  "Get the message log from router (for debugging/testing)."
  [router]
  (:message-log @router))

(defn reset-router!
  "Reset router state (for testing)."
  [router]
  (reset! router {:peers {} :message-log []}))
