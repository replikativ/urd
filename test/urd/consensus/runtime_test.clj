(ns urd.consensus.runtime-test
  "Integration tests for consensus runtime with round-robin state machine."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.runtime :as runtime]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.network :as net]
            [urd.log :as log]
            [urd.crypto :as crypto]
            [yggdrasil.types :as yt]
            [konserve.memory :refer [new-mem-store]]
            [clojure.core.async :refer [<!! timeout]]))

;; ============================================================
;; Test Helpers
;; ============================================================

(defn create-test-validators
  "Create n validators with keypairs."
  [n]
  (let [keypairs (repeatedly n crypto/ed25519-keypair)
        validators (into {}
                         (map-indexed
                          (fn [idx kp]
                            (let [id (java.util.UUID/randomUUID)]
                              [id {:index idx
                                   :keypair kp
                                   :public-key (:public kp)
                                   :private-key (:private kp)}]))
                          keypairs))]
    validators))

(defn create-test-proposal
  "Create a test signed snapshot."
  [validator-info]
  (let [snapshot (yt/->SnapshotRef
                  "test-system"
                  (java.util.UUID/randomUUID)
                  #{}
                  (yt/hlc-now)
                  "sha256:test-hash")]
    (crypto/sign-snapshot snapshot
                          (:private-key validator-info)
                          (:public-key validator-info))))

;; ============================================================
;; Runtime Integration Tests
;; ============================================================

(deftest runtime-basic-consensus-test
  (testing "Runtime runs round-robin state machine through complete consensus"
    (let [;; Create 3 validators
          validators (create-test-validators 3)
          validator-set (into {}
                              (map (fn [[id info]]
                                     [id (:public-key info)])
                                   validators))
          validator-ids (vec (sort (keys validators)))

          ;; Create mock network cluster
          cluster (net/create-mock-cluster validator-ids)

          ;; Track finalized proposals
          finalized (atom {})

          ;; Start runtime for each validator
          runtimes
          (into {}
                (map (fn [[v-id v-info]]
                       (let [store (<!! (new-mem-store))
                             consensus-log (log/create-consensus-log store validator-set)
                             sm (rr/create validator-set)

                             on-propose (fn [] (create-test-proposal v-info))

                             on-finalize (fn [proposal height]
                                           (swap! finalized update v-id
                                                  (fnil conj [])
                                                  {:height height :proposal proposal}))

                             rt (<!! (runtime/start-runtime!
                                      {:peer-id v-id
                                       :state-machine sm
                                       :network (get cluster v-id)
                                       :consensus-log consensus-log
                                       :on-propose on-propose
                                       :on-finalize on-finalize}))]
                         [v-id rt]))
                     validators))]

      ;; Start consensus on all validators simultaneously
      (doseq [[v-id rt] runtimes]
        (runtime/send-event! rt {:type :start-round}))

      ;; Wait for consensus to complete
      (<!! (timeout 3000))

      (testing "All validators finalize proposal"
        (is (= 3 (count (filter #(seq (get @finalized %)) validator-ids)))
            "All 3 validators should finalize"))

      (testing "All validators agree on same proposal"
        (let [proposals (map (fn [v-id]
                               (-> @finalized (get v-id) first :proposal :snapshot-id))
                             validator-ids)
              unique-proposals (set (remove nil? proposals))]
          (is (= 1 (count unique-proposals))
              "All validators should finalize same proposal")))

      (testing "Finalized at height 0"
        (let [heights (map (fn [v-id]
                             (-> @finalized (get v-id) first :height))
                           validator-ids)]
          (is (every? #(= 0 %) (remove nil? heights))
              "All validators should finalize at height 0")))

      ;; Cleanup
      (doseq [[v-id rt] runtimes]
        (<!! (runtime/stop-runtime! rt))
        (<!! (net/close-network! (get cluster v-id)))))))

(deftest runtime-multi-round-test
  (testing "Runtime handles multiple consensus rounds"
    (let [validators (create-test-validators 3)
          validator-set (into {}
                              (map (fn [[id info]]
                                     [id (:public-key info)])
                                   validators))
          validator-ids (vec (sort (keys validators)))

          cluster (net/create-mock-cluster validator-ids)

          finalized (atom {})

          ;; Counter to track how many proposals each validator has provided
          proposal-count (atom {})

          ;; Use atom to allow on-finalize to reference runtimes
          runtimes-atom (atom {})

          runtimes
          (into {}
                (map (fn [[v-id v-info]]
                       (let [store (<!! (new-mem-store))
                             consensus-log (log/create-consensus-log store validator-set)
                             sm (rr/create validator-set)

                             on-propose (fn []
                                          (swap! proposal-count update v-id (fnil inc 0))
                                          (create-test-proposal v-info))

                             on-finalize (fn [proposal height]
                                           (swap! finalized update v-id
                                                  (fnil conj [])
                                                  {:height height :proposal proposal})
                                      ;; Trigger next round
                                           (runtime/send-event!
                                            (get @runtimes-atom v-id)
                                            {:type :start-round}))

                             rt (<!! (runtime/start-runtime!
                                      {:peer-id v-id
                                       :state-machine sm
                                       :network (get cluster v-id)
                                       :consensus-log consensus-log
                                       :on-propose on-propose
                                       :on-finalize on-finalize}))]
                     ;; Store runtime immediately so on-finalize can access it
                         (swap! runtimes-atom assoc v-id rt)
                         [v-id rt]))
                     validators))]

      ;; Start consensus on all validators simultaneously
      (doseq [[v-id rt] runtimes]
        (runtime/send-event! rt {:type :start-round}))

      ;; Wait for multiple rounds
      (<!! (timeout 6000))

      (testing "Multiple rounds complete"
        (let [heights-finalized (map (fn [v-id]
                                       (count (get @finalized v-id [])))
                                     validator-ids)]
          (is (every? #(>= % 2) heights-finalized)
              "All validators should finalize at least 2 rounds")))

      (testing "Proposer function was called"
        ;; Check that proposals were requested
        (is (> (reduce + (vals @proposal-count)) 0)
            "At least one proposal should have been requested"))

      ;; Cleanup
      (doseq [[v-id rt] runtimes]
        (<!! (runtime/stop-runtime! rt))
        (<!! (net/close-network! (get cluster v-id)))))))
