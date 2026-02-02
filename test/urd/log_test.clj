(ns urd.log-test
  "Tests for Urðarbrunnr (Urd's Well) - the consensus log."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [urd.log :as log]
            [urd.crypto :as crypto]
            [urd.types :as t]
            [yggdrasil.types :as yt]
            [konserve.core :as k]
            [konserve.memory :refer [new-mem-store]]
            [superv.async :refer [<?-]]
            [clojure.core.async :refer [<!!]]))

;; ============================================================
;; Test Fixtures
;; ============================================================

(defn create-test-log
  "Create a test consensus log with in-memory storage."
  [validator-set]
  (let [store (<!! (new-mem-store))]
    (log/create-consensus-log store validator-set)))

(defn create-test-validators
  "Create n test validators and return keypairs + validator-set."
  [n]
  (let [keypairs (repeatedly n crypto/ed25519-keypair)
        validator-set (into {}
                            (map (fn [kp]
                                   [(str "ed25519:" (crypto/bytes->base64 (:public kp)))
                                    (:public kp)])
                                 keypairs))]
    {:keypairs keypairs
     :validator-set validator-set}))

(defn create-test-snapshot
  "Create a test SnapshotRef."
  []
  (yt/->SnapshotRef
   "test-system"
   (java.util.UUID/randomUUID)  ; Native UUID, not string
   #{"parent-1"}
   (yt/hlc-now)
   "sha256:test-content-hash"))

;; ============================================================
;; Basic Proposal Tests
;; ============================================================

(deftest propose-test
  (testing "Submitting a proposal"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)
          signed (crypto/sign-snapshot snapshot
                                       (:private (first keypairs))
                                       (:public (first keypairs)))

          proposal-id (<!! (log/propose! consensus-log signed {:test "metadata"}))]

      (is (some? proposal-id) "Proposal ID should be returned")
      (is (instance? java.util.UUID proposal-id) "Proposal ID should be a UUID")

      (let [entry (<!! (log/get-proposal consensus-log proposal-id))]
        (is (some? entry) "Proposal should be retrievable")
        (is (instance? java.util.UUID (:proposal-id entry)) "Stored proposal-id should be a UUID")
        (is (= :proposed (:state entry)) "Initial state should be :proposed")
        (is (= :single (:snapshot-type entry)))
        (is (= signed (:signed-snapshot entry)))
        (is (empty? (:votes entry)) "Should have no votes initially")
        (is (nil? (:height entry)) "Should have no height initially")
        (is (= {:test "metadata"} (:metadata entry)))))))

(deftest get-proposal-not-found-test
  (testing "Getting a non-existent proposal"
    (let [consensus-log (create-test-log {})
          result (<!! (log/get-proposal consensus-log (java.util.UUID/randomUUID)))]
      (is (nil? result) "Should return nil for non-existent proposal"))))

;; ============================================================
;; Vote Accumulation Tests
;; ============================================================

(deftest add-vote-test
  (testing "Adding votes to a proposal"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)

          ;; Validator 1 proposes
          signed1 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 0))
                                        (:public (nth keypairs 0)))
          proposal-id (<!! (log/propose! consensus-log signed1 {}))

          ;; Validator 2 signs
          signed2 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 1))
                                        (:public (nth keypairs 1)))]

      (testing "First vote transitions to :voting"
        (let [entry (<!! (log/add-vote! consensus-log
                                        proposal-id
                                        (:author-id signed2)
                                        (:signature signed2)))]
          (is (= :voting (:state entry)))
          (is (= 1 (count (:votes entry))))))

      (testing "Third vote reaches quorum → :certified"
        ;; Validator 3 signs
        (let [signed3 (crypto/sign-snapshot snapshot
                                            (:private (nth keypairs 2))
                                            (:public (nth keypairs 2)))
              entry (<!! (log/add-vote! consensus-log
                                        proposal-id
                                        (:author-id signed3)
                                        (:signature signed3)))]
          (is (= :certified (:state entry)) "Should transition to :certified")
          (is (= 2 (count (:votes entry)))))))))

;; ============================================================
;; State Management Tests
;; ============================================================

(deftest update-state-test
  (testing "Manual state transitions"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)
          signed (crypto/sign-snapshot snapshot
                                       (:private (first keypairs))
                                       (:public (first keypairs)))
          proposal-id (<!! (log/propose! consensus-log signed {}))]

      (testing "Transition from :proposed to :voting"
        (let [entry (<!! (log/update-state! consensus-log proposal-id :voting))]
          (is (= :voting (:state entry)))))

      (testing "Verify state index updated"
        (let [proposed (<!! (log/get-proposals-by-state consensus-log :proposed))
              voting (<!! (log/get-proposals-by-state consensus-log :voting))]
          (is (empty? proposed) "Should not be in :proposed index")
          (is (= 1 (count voting)) "Should be in :voting index"))))))

;; ============================================================
;; Quorum and Certificate Tests
;; ============================================================

(deftest has-quorum-test
  (testing "Quorum detection with 4 validators"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)

          ;; Validator 1 proposes
          signed1 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 0))
                                        (:public (nth keypairs 0)))
          proposal-id (<!! (log/propose! consensus-log signed1 {}))]

      (testing "1 signature (proposer) = no quorum"
        (is (false? (<!! (log/has-quorum? consensus-log proposal-id validator-set)))))

      (testing "2 signatures = no quorum"
        (let [signed2 (crypto/sign-snapshot snapshot
                                            (:private (nth keypairs 1))
                                            (:public (nth keypairs 1)))]
          (<!! (log/add-vote! consensus-log proposal-id
                              (:author-id signed2) (:signature signed2)))
          (is (false? (<!! (log/has-quorum? consensus-log proposal-id validator-set))))))

      (testing "3 signatures = quorum (2f+1)"
        (let [signed3 (crypto/sign-snapshot snapshot
                                            (:private (nth keypairs 2))
                                            (:public (nth keypairs 2)))]
          (<!! (log/add-vote! consensus-log proposal-id
                              (:author-id signed3) (:signature signed3)))
          (is (true? (<!! (log/has-quorum? consensus-log proposal-id validator-set)))))))))

;; ============================================================
;; Finalization Tests
;; ============================================================

(deftest finalize-test
  (testing "Finalizing a certified proposal"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)

          ;; Create certified proposal
          signed1 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 0))
                                        (:public (nth keypairs 0)))
          proposal-id (<!! (log/propose! consensus-log signed1 {}))

          ;; Add votes to reach quorum
          signed2 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 1))
                                        (:public (nth keypairs 1)))
          signed3 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 2))
                                        (:public (nth keypairs 2)))

          _ (<!! (log/add-vote! consensus-log proposal-id
                                (:author-id signed2) (:signature signed2)))
          entry (<!! (log/add-vote! consensus-log proposal-id
                                    (:author-id signed3) (:signature signed3)))]

      (is (= :certified (:state entry)) "Should be certified before finalizing")

      (testing "Finalize at height 1"
        (let [finalized (<!! (log/finalize! consensus-log proposal-id 1))]
          (is (= :finalized (:state finalized)))
          (is (= 1 (:height finalized)))
          (is (some? (:finalized-at finalized)))))

      (testing "Verify finalization entry"
        (let [fin-entry (<!! (log/get-finalized-at-height consensus-log 1))]
          (is (some? fin-entry))
          (is (= 1 (:height fin-entry)))
          (is (contains? (:proposal-ids fin-entry) proposal-id))))

      (testing "Latest height updated"
        (let [latest (<!! (log/get-latest-height consensus-log))]
          (is (= 1 latest)))))))

(deftest finalize-non-certified-test
  (testing "Cannot finalize non-certified proposal"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)
          signed (crypto/sign-snapshot snapshot
                                       (:private (first keypairs))
                                       (:public (first keypairs)))
          proposal-id (<!! (log/propose! consensus-log signed {}))

          result (<!! (log/finalize! consensus-log proposal-id 1))]

      (is (nil? result) "Should return nil for non-certified proposal"))))

;; ============================================================
;; Multi-Height Finalization Tests
;; ============================================================

(deftest multi-height-finalization-test
  (testing "Finalizing proposals at multiple heights"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)

          ;; Helper to create certified proposal
          create-certified (fn []
                             (let [snapshot (create-test-snapshot)
                                   signed1 (crypto/sign-snapshot snapshot
                                                                 (:private (nth keypairs 0))
                                                                 (:public (nth keypairs 0)))
                                   pid (<!! (log/propose! consensus-log signed1 {}))
                                   signed2 (crypto/sign-snapshot snapshot
                                                                 (:private (nth keypairs 1))
                                                                 (:public (nth keypairs 1)))
                                   signed3 (crypto/sign-snapshot snapshot
                                                                 (:private (nth keypairs 2))
                                                                 (:public (nth keypairs 2)))]
                               (<!! (log/add-vote! consensus-log pid
                                                   (:author-id signed2) (:signature signed2)))
                               (<!! (log/add-vote! consensus-log pid
                                                   (:author-id signed3) (:signature signed3)))
                               pid))

          ;; Create and finalize at different heights
          pid1 (create-certified)
          pid2 (create-certified)
          pid3 (create-certified)]

      (<!! (log/finalize! consensus-log pid1 1))
      (<!! (log/finalize! consensus-log pid2 2))
      (<!! (log/finalize! consensus-log pid3 2))  ; Two at same height

      (testing "Height 1 has 1 proposal"
        (let [fin1 (<!! (log/get-finalized-at-height consensus-log 1))]
          (is (= 1 (count (:proposal-ids fin1))))))

      (testing "Height 2 has 2 proposals"
        (let [fin2 (<!! (log/get-finalized-at-height consensus-log 2))]
          (is (= 2 (count (:proposal-ids fin2))))))

      (testing "Latest height is 2"
        (is (= 2 (<!! (log/get-latest-height consensus-log))))))))

;; ============================================================
;; Query Tests
;; ============================================================

(deftest get-proposals-by-state-test
  (testing "Querying proposals by state"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)

          ;; Create proposals in different states
          snapshot1 (create-test-snapshot)
          snapshot2 (create-test-snapshot)
          snapshot3 (create-test-snapshot)

          signed1 (crypto/sign-snapshot snapshot1
                                        (:private (first keypairs))
                                        (:public (first keypairs)))
          signed2 (crypto/sign-snapshot snapshot2
                                        (:private (first keypairs))
                                        (:public (first keypairs)))
          signed3 (crypto/sign-snapshot snapshot3
                                        (:private (first keypairs))
                                        (:public (first keypairs)))

          pid1 (<!! (log/propose! consensus-log signed1 {}))
          pid2 (<!! (log/propose! consensus-log signed2 {}))
          pid3 (<!! (log/propose! consensus-log signed3 {}))]

      ;; Move pid2 to :voting
      (let [signed-v2 (crypto/sign-snapshot snapshot2
                                            (:private (nth keypairs 1))
                                            (:public (nth keypairs 1)))]
        (<!! (log/add-vote! consensus-log pid2
                            (:author-id signed-v2) (:signature signed-v2))))

      ;; Move pid3 to :certified
      (let [signed-v3a (crypto/sign-snapshot snapshot3
                                             (:private (nth keypairs 1))
                                             (:public (nth keypairs 1)))
            signed-v3b (crypto/sign-snapshot snapshot3
                                             (:private (nth keypairs 2))
                                             (:public (nth keypairs 2)))]
        (<!! (log/add-vote! consensus-log pid3
                            (:author-id signed-v3a) (:signature signed-v3a)))
        (<!! (log/add-vote! consensus-log pid3
                            (:author-id signed-v3b) (:signature signed-v3b))))

      (testing "Query :proposed state"
        (let [proposed (<!! (log/get-proposals-by-state consensus-log :proposed))]
          (is (= 1 (count proposed)))))

      (testing "Query :voting state"
        (let [voting (<!! (log/get-proposals-by-state consensus-log :voting))]
          (is (= 1 (count voting)))))

      (testing "Query :certified state"
        (let [certified (<!! (log/get-proposals-by-state consensus-log :certified))]
          (is (= 1 (count certified))))))))

(deftest get-proposals-for-snapshot-test
  (testing "Querying proposals for a specific snapshot"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)

          ;; Create multiple proposals for same snapshot
          signed1 (crypto/sign-snapshot snapshot
                                        (:private (first keypairs))
                                        (:public (first keypairs)))
          signed2 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 1))
                                        (:public (nth keypairs 1)))

          pid1 (<!! (log/propose! consensus-log signed1 {}))
          pid2 (<!! (log/propose! consensus-log signed2 {}))]

      (testing "Both proposals indexed by snapshot-id"
        (let [proposals (<!! (log/get-proposals-for-snapshot
                              consensus-log
                              (:snapshot-id snapshot)))]
          (is (= 2 (count proposals)))
          (is (contains? (set (map :proposal-id proposals)) pid1))
          (is (contains? (set (map :proposal-id proposals)) pid2)))))))

;; ============================================================
;; Helper Function Tests
;; ============================================================

(deftest build-certificate-test
  (testing "Building a certificate with helper function"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)

          ;; Proposer signs
          signed-proposer (crypto/sign-snapshot snapshot
                                                (:private (nth keypairs 0))
                                                (:public (nth keypairs 0)))

          ;; Other validators sign
          signed2 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 1))
                                        (:public (nth keypairs 1)))
          signed3 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 2))
                                        (:public (nth keypairs 2)))

          validator-sigs [[(:author-id signed2) (:signature signed2)]
                          [(:author-id signed3) (:signature signed3)]]

          proposal-id (<!! (log/build-certificate consensus-log
                                                  signed-proposer
                                                  validator-sigs))]

      (is (some? proposal-id))

      (let [entry (<!! (log/get-proposal consensus-log proposal-id))]
        (is (= :certified (:state entry)))
        (is (= 2 (count (:votes entry))))))))

(deftest get-certified-proposals-test
  (testing "Getting all certified proposals"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)
          snapshot (create-test-snapshot)

          signed1 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 0))
                                        (:public (nth keypairs 0)))
          pid (<!! (log/propose! consensus-log signed1 {}))

          ;; Certify
          signed2 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 1))
                                        (:public (nth keypairs 1)))
          signed3 (crypto/sign-snapshot snapshot
                                        (:private (nth keypairs 2))
                                        (:public (nth keypairs 2)))]

      (<!! (log/add-vote! consensus-log pid
                          (:author-id signed2) (:signature signed2)))
      (<!! (log/add-vote! consensus-log pid
                          (:author-id signed3) (:signature signed3)))

      (let [certified (<!! (log/get-certified-proposals consensus-log))]
        (is (= 1 (count certified)))
        (is (= pid (:proposal-id (first certified))))))))

(deftest get-finalization-history-test
  (testing "Getting finalization history across height range"
    (let [{:keys [keypairs validator-set]} (create-test-validators 4)
          consensus-log (create-test-log validator-set)

          ;; Helper to create certified proposal
          create-certified (fn []
                             (let [snapshot (create-test-snapshot)
                                   signed1 (crypto/sign-snapshot snapshot
                                                                 (:private (nth keypairs 0))
                                                                 (:public (nth keypairs 0)))
                                   pid (<!! (log/propose! consensus-log signed1 {}))
                                   signed2 (crypto/sign-snapshot snapshot
                                                                 (:private (nth keypairs 1))
                                                                 (:public (nth keypairs 1)))
                                   signed3 (crypto/sign-snapshot snapshot
                                                                 (:private (nth keypairs 2))
                                                                 (:public (nth keypairs 2)))]
                               (<!! (log/add-vote! consensus-log pid
                                                   (:author-id signed2) (:signature signed2)))
                               (<!! (log/add-vote! consensus-log pid
                                                   (:author-id signed3) (:signature signed3)))
                               pid))

          ;; Finalize at heights 1, 2, 4 (skip 3)
          pid1 (create-certified)
          pid2 (create-certified)
          pid4 (create-certified)]

      (<!! (log/finalize! consensus-log pid1 1))
      (<!! (log/finalize! consensus-log pid2 2))
      (<!! (log/finalize! consensus-log pid4 4))

      (testing "Get history from 1 to 4"
        (let [history (<!! (log/get-finalization-history consensus-log 1 4))]
          (is (= 3 (count history)) "Should have 3 entries (heights 1, 2, 4)")
          (is (= [1 2 4] (map :height history))))))))
