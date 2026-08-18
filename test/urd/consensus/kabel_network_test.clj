(ns urd.consensus.kabel-network-test
  "Tests for Kabel-based P2P networking."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [clojure.core.async :refer [<!! timeout]]
            [superv.async :refer [S <?? go-try-]]
            [urd.consensus.networks.kabel :as kabel]
            [urd.consensus.network :as net]))

;; ============================================================
;; Basic Connectivity Tests
;; ============================================================

(deftest ^:integration kabel-network-creation-test
  (testing "Can create Kabel server and client"
    (let [server-id (java.util.UUID/randomUUID)
          client-id (java.util.UUID/randomUUID)
          port 47290]

      ;; Create server
      (let [server (<?? S (kabel/create-kabel-server S server-id port))]
        (is (some? server))
        (is (= server-id (:peer-id server)))

        ;; Register topics on server
        (<?? S (kabel/register-consensus-topics! server #{:proposals :votes :finalizations :recovery}))

        ;; Create client
        (let [client (<?? S (kabel/create-kabel-client S client-id (str "ws://localhost:" port)))]
          (is (some? client))
          (is (= client-id (:peer-id client)))

          ;; Wait a bit for connection to establish
          (<!! (timeout 1000))

          ;; Cleanup
          (<?? S (net/close-network! client))
          (<?? S (net/close-network! server)))))))

(deftest ^:integration kabel-broadcast-subscribe-test
  (testing "Can broadcast and receive messages via Kabel"
    (let [server-id (java.util.UUID/randomUUID)
          client-id (java.util.UUID/randomUUID)
          port 47291
          received (atom [])]

      ;; Create server
      (let [server (<?? S (kabel/create-kabel-server S server-id port))]
        (<?? S (kabel/register-consensus-topics! server #{:proposals :votes :finalizations :recovery}))

        ;; Create client
        (let [client (<?? S (kabel/create-kabel-client S client-id (str "ws://localhost:" port)))]

          ;; Subscribe client to proposals
          (<?? S (net/subscribe! client :proposals
                                 (fn [msg]
                                   (swap! received conj msg))))

          ;; Wait for subscription to be established
          (<!! (timeout 1000))

          ;; Broadcast from server
          (<?? S (net/broadcast! server :proposals {:proposal "test-proposal"}))

          ;; Wait for message to be received
          (<!! (timeout 1000))

          ;; Verify message received
          (is (= 1 (count @received)))
          (is (= "test-proposal" (:proposal (first @received))))
          (is (= server-id (:sender (first @received))))

          ;; Cleanup
          (<?? S (net/close-network! client))
          (<?? S (net/close-network! server)))))))

(deftest ^:integration kabel-multiple-clients-test
  (testing "Server can broadcast to multiple clients"
    (let [server-id (java.util.UUID/randomUUID)
          client1-id (java.util.UUID/randomUUID)
          client2-id (java.util.UUID/randomUUID)
          port 47292
          received1 (atom [])
          received2 (atom [])]

      ;; Create server
      (let [server (<?? S (kabel/create-kabel-server S server-id port))]
        (<?? S (kabel/register-consensus-topics! server #{:proposals :votes :finalizations :recovery}))

        ;; Create clients
        (let [client1 (<?? S (kabel/create-kabel-client S client1-id (str "ws://localhost:" port)))
              client2 (<?? S (kabel/create-kabel-client S client2-id (str "ws://localhost:" port)))]

          ;; Subscribe both clients
          (<?? S (net/subscribe! client1 :votes (fn [msg] (swap! received1 conj msg))))
          (<?? S (net/subscribe! client2 :votes (fn [msg] (swap! received2 conj msg))))

          ;; Wait for subscriptions
          (<!! (timeout 1000))

          ;; Broadcast vote
          (<?? S (net/broadcast! server :votes {:vote "yes"}))

          ;; Wait for delivery
          (<!! (timeout 1000))

          ;; Both clients should receive
          (is (= 1 (count @received1)))
          (is (= 1 (count @received2)))
          (is (= "yes" (:vote (first @received1))))
          (is (= "yes" (:vote (first @received2))))

          ;; Cleanup
          (<?? S (net/close-network! client1))
          (<?? S (net/close-network! client2))
          (<?? S (net/close-network! server)))))))
