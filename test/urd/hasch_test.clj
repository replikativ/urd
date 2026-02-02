(ns urd.hasch-test
  "Tests for content-addressed UUIDs in urd."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.log :as log]
            [urd.crypto :as crypto]
            [yggdrasil.types :as yt]
            [hasch.core :as hasch]
            [konserve.memory :refer [new-mem-store]]
            [clojure.core.async :refer [<!!]]))

(deftest content-addressed-proposal-ids-test
  (testing "Same snapshot produces same proposal-id"
    (let [kp (crypto/ed25519-keypair)
          snapshot (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:test-hash")

          ;; Sign the same snapshot twice
          signed1 (crypto/sign-snapshot snapshot
                                        (:private kp)
                                        (:public kp))
          signed2 (crypto/sign-snapshot snapshot
                                        (:private kp)
                                        (:public kp))]

      (testing "Signed snapshots are identical"
        (is (= signed1 signed2)))

      (testing "Content-addressed UUIDs are deterministic"
        (let [uuid1 (hasch/uuid signed1)
              uuid2 (hasch/uuid signed2)]
          (is (= uuid1 uuid2) "Same content produces same UUID")))

      (testing "Proposal IDs are content-addressed"
        (let [store (<!! (new-mem-store))
              consensus-log (log/create-consensus-log store {})

              pid1 (<!! (log/propose! consensus-log signed1 {}))
              pid2 (<!! (log/propose! consensus-log signed2 {}))]

          (is (= pid1 pid2) "Same snapshot produces same proposal-id")

          ;; Should only have one entry in the store (deduplication)
          (let [entry1 (<!! (log/get-proposal consensus-log pid1))
                entry2 (<!! (log/get-proposal consensus-log pid2))]
            (is (some? entry1))
            (is (some? entry2))
            (is (= entry1 entry2) "Both IDs point to same entry")))))))

(deftest different-snapshots-different-ids-test
  (testing "Different snapshots produce different proposal-ids"
    (let [kp (crypto/ed25519-keypair)
          snapshot1 (yt/->SnapshotRef
                     "test-system"
                     "snap-1"
                     #{"parent-1"}
                     (yt/->HLC 1234567890 0)
                     "sha256:hash-1")
          snapshot2 (yt/->SnapshotRef
                     "test-system"
                     "snap-2"  ; Different snapshot-id
                     #{"parent-1"}
                     (yt/->HLC 1234567890 0)
                     "sha256:hash-2")  ; Different content-hash

          signed1 (crypto/sign-snapshot snapshot1
                                        (:private kp)
                                        (:public kp))
          signed2 (crypto/sign-snapshot snapshot2
                                        (:private kp)
                                        (:public kp))]

      (testing "Different content produces different UUIDs"
        (let [uuid1 (hasch/uuid signed1)
              uuid2 (hasch/uuid signed2)]
          (is (not= uuid1 uuid2) "Different content produces different UUIDs")))

      (testing "Different proposal IDs"
        (let [store (<!! (new-mem-store))
              consensus-log (log/create-consensus-log store {})

              pid1 (<!! (log/propose! consensus-log signed1 {}))
              pid2 (<!! (log/propose! consensus-log signed2 {}))]

          (is (not= pid1 pid2) "Different snapshots produce different proposal-ids"))))))

(deftest signature-changes-produce-different-ids-test
  (testing "Different signatures produce different proposal-ids"
    (let [kp1 (crypto/ed25519-keypair)
          kp2 (crypto/ed25519-keypair)
          snapshot (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:test-hash")

          ;; Same snapshot, different signers
          signed1 (crypto/sign-snapshot snapshot
                                        (:private kp1)
                                        (:public kp1))
          signed2 (crypto/sign-snapshot snapshot
                                        (:private kp2)
                                        (:public kp2))]

      (testing "Different signers produce different UUIDs"
        (let [uuid1 (hasch/uuid signed1)
              uuid2 (hasch/uuid signed2)]
          (is (not= uuid1 uuid2) "Different signatures produce different UUIDs")))

      (testing "Different proposal IDs for different signers"
        (let [store (<!! (new-mem-store))
              consensus-log (log/create-consensus-log store {})

              pid1 (<!! (log/propose! consensus-log signed1 {}))
              pid2 (<!! (log/propose! consensus-log signed2 {}))]

          (is (not= pid1 pid2) "Different signers produce different proposal-ids"))))))

(deftest uuid-type-test
  (testing "Hasch produces proper UUIDs"
    (let [kp (crypto/ed25519-keypair)
          snapshot (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:test-hash")
          signed (crypto/sign-snapshot snapshot
                                       (:private kp)
                                       (:public kp))
          uuid (hasch/uuid signed)]

      (is (instance? java.util.UUID uuid) "Should be a proper UUID instance")
      (is (string? (str uuid)) "Should be convertible to string")

      ;; UUID-5 format check (version 5, variant 1)
      (let [uuid-str (str uuid)]
        (is (re-matches #"^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$"
                        uuid-str)
            "Should be valid UUID-5 format")))))
