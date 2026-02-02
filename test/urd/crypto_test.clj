(ns urd.crypto-test
  "Tests for cryptographic signature support in urd."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.crypto :as crypto]
            [yggdrasil.types :as yt]
            [urd.types :as t]))

(deftest ed25519-keypair-test
  (testing "ED25519 keypair generation"
    (let [kp (crypto/ed25519-keypair)]
      (is (map? kp))
      (is (contains? kp :public))
      (is (contains? kp :private))
      (is (= 32 (alength (:public kp))) "Public key should be 32 bytes")
      (is (= 32 (alength (:private kp))) "Private key should be 32 bytes"))))

(deftest ed25519-sign-verify-test
  (testing "ED25519 signing and verification"
    (let [kp (crypto/ed25519-keypair)
          message (.getBytes "Hello, Urd!" "UTF-8")
          signature (crypto/ed25519-sign (:private kp) message)]

      (is (= 64 (alength signature)) "Signature should be 64 bytes")

      (testing "Valid signature verifies"
        (is (true? (crypto/ed25519-verify (:public kp) message signature))))

      (testing "Invalid signature fails"
        (let [bad-message (.getBytes "Wrong message" "UTF-8")]
          (is (false? (crypto/ed25519-verify (:public kp) bad-message signature)))))

      (testing "Wrong public key fails"
        (let [other-kp (crypto/ed25519-keypair)]
          (is (false? (crypto/ed25519-verify (:public other-kp) message signature))))))))

(deftest snapshot-canonical-message-test
  (testing "Canonical message generation is deterministic"
    (let [snap-ref (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1" "parent-2"}  ; Unordered set
                    (yt/->HLC 1234567890 42)
                    "sha256:abc123")

          msg1 (crypto/snapshot-canonical-message snap-ref)
          msg2 (crypto/snapshot-canonical-message snap-ref)]

      (is (= (seq msg1) (seq msg2)) "Same snapshot produces same canonical message")))

  (testing "Parent-ids are sorted for determinism"
    (let [snap1 (yt/->SnapshotRef "sys" "snap-1" #{"b" "a" "c"} (yt/->HLC 100 0) "hash1")
          snap2 (yt/->SnapshotRef "sys" "snap-1" #{"a" "b" "c"} (yt/->HLC 100 0) "hash1")
          msg1 (crypto/snapshot-canonical-message snap1)
          msg2 (crypto/snapshot-canonical-message snap2)]

      (is (= (seq msg1) (seq msg2)) "Parent-id ordering doesn't affect canonical message"))))

(deftest sign-snapshot-test
  (testing "Signing a SnapshotRef"
    (let [kp (crypto/ed25519-keypair)
          snap-ref (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:content")

          signed (crypto/sign-snapshot snap-ref (:private kp) (:public kp))]

      (is (instance? urd.types.SignedSnapshotRef signed))
      (is (= "test-system" (:system-id signed)))
      (is (= "snap-123" (:snapshot-id signed)))
      (is (string? (:author-id signed)))
      (is (string? (:signature signed)))
      (is (.startsWith (:author-id signed) "ed25519:"))
      (is (map? (:signatures signed)))
      (is (empty? (:signatures signed)) "New signature should have empty signatures map"))))

(deftest verify-signature-test
  (testing "Verifying a signature"
    (let [kp (crypto/ed25519-keypair)
          snap-ref (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:content")
          signed (crypto/sign-snapshot snap-ref (:private kp) (:public kp))]

      (testing "Valid signature verifies"
        (is (true? (crypto/verify-signature signed))))

      (testing "Modified signature fails"
        (let [tampered (assoc signed :signature "invalid-base64-signature")]
          (is (false? (crypto/verify-signature tampered)))))

      (testing "Modified data fails"
        (let [tampered (assoc signed :snapshot-id "different-id")]
          (is (false? (crypto/verify-signature tampered))))))))

(deftest add-signature-test
  (testing "Accumulating signatures for certificate"
    (let [kp1 (crypto/ed25519-keypair)
          kp2 (crypto/ed25519-keypair)
          snap-ref (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:content")

          ;; Validator 1 signs
          signed1 (crypto/sign-snapshot snap-ref (:private kp1) (:public kp1))

          ;; Validator 2 also signs
          signed2 (crypto/sign-snapshot snap-ref (:private kp2) (:public kp2))

          ;; Add validator 2's signature to validator 1's signed ref
          with-cert (crypto/add-signature signed1
                                          (:author-id signed2)
                                          (:signature signed2))]

      (is (= 1 (count (:signatures with-cert))))
      (is (contains? (:signatures with-cert) (:author-id signed2))))))

(deftest has-quorum-test
  (testing "Quorum detection with 4 validators (need 3 = 2f+1)"
    (let [kps (repeatedly 4 crypto/ed25519-keypair)
          validator-set (set (map #(str "ed25519:" (crypto/bytes->base64 (:public %))) kps))

          snap-ref (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:content")

          ;; Validator 1 signs
          signed (crypto/sign-snapshot snap-ref
                                       (:private (first kps))
                                       (:public (first kps)))]

      (testing "1 signature is not quorum"
        (is (false? (crypto/has-quorum? signed validator-set))))

      (testing "2 signatures is not quorum"
        (let [kp2 (second kps)
              signed2 (crypto/sign-snapshot snap-ref (:private kp2) (:public kp2))
              with-2 (crypto/add-signature signed
                                           (:author-id signed2)
                                           (:signature signed2))]
          (is (false? (crypto/has-quorum? with-2 validator-set)))))

      (testing "3 signatures reaches quorum (2f+1)"
        (let [kp2 (second kps)
              kp3 (nth kps 2)
              signed2 (crypto/sign-snapshot snap-ref (:private kp2) (:public kp2))
              signed3 (crypto/sign-snapshot snap-ref (:private kp3) (:public kp3))
              with-3 (-> signed
                         (crypto/add-signature (:author-id signed2) (:signature signed2))
                         (crypto/add-signature (:author-id signed3) (:signature signed3)))]
          (is (true? (crypto/has-quorum? with-3 validator-set))))))))

(deftest verify-certificate-test
  (testing "Certificate verification"
    (let [kps (repeatedly 4 crypto/ed25519-keypair)
          validator-set (into {}
                              (map (fn [kp]
                                     [(str "ed25519:" (crypto/bytes->base64 (:public kp)))
                                      (:public kp)])
                                   kps))

          snap-ref (yt/->SnapshotRef
                    "test-system"
                    "snap-123"
                    #{"parent-1"}
                    (yt/->HLC 1234567890 0)
                    "sha256:content")

          ;; Build certificate with 3 signatures
          signed1 (crypto/sign-snapshot snap-ref (:private (nth kps 0)) (:public (nth kps 0)))
          signed2 (crypto/sign-snapshot snap-ref (:private (nth kps 1)) (:public (nth kps 1)))
          signed3 (crypto/sign-snapshot snap-ref (:private (nth kps 2)) (:public (nth kps 2)))

          certificate (-> signed1
                          (crypto/add-signature (:author-id signed2) (:signature signed2))
                          (crypto/add-signature (:author-id signed3) (:signature signed3)))

          result (crypto/verify-certificate certificate validator-set)]

      (is (:valid? result) "Certificate with 3 valid signatures should be valid")
      (is (= 3 (:signer-count result)))
      (is (empty? (:invalid-signers result)))
      (is (:has-quorum? result)))))

(deftest merkle-root-test
  (testing "Merkle root computation"
    (let [hashes ["sha256:abc123" "sha256:def456" "sha256:ghi789"]
          root (crypto/compute-merkle-root hashes)]

      (is (string? root))
      (is (.startsWith root "sha256:"))

      (testing "Same hashes produce same root"
        (let [root2 (crypto/compute-merkle-root hashes)]
          (is (= root root2))))

      (testing "Order doesn't matter (hashes are sorted)"
        (let [shuffled ["sha256:ghi789" "sha256:abc123" "sha256:def456"]
              root3 (crypto/compute-merkle-root shuffled)]
          (is (= root root3)))))))

(deftest sign-multi-snapshot-test
  (testing "Multi-system snapshot signing"
    (let [kp (crypto/ed25519-keypair)
          hlc (yt/->HLC 1234567890 0)

          snapshot-refs {:account-ledger (yt/->SnapshotRef
                                          "account-ledger"
                                          "snap-1"
                                          #{"parent-1"}
                                          nil  ; HLC will be added
                                          "sha256:account-hash")
                         :cost-ledger (yt/->SnapshotRef
                                       "cost-ledger"
                                       "snap-2"
                                       #{"parent-2"}
                                       nil
                                       "sha256:cost-hash")}

          composite (crypto/sign-multi-snapshot snapshot-refs
                                                (:private kp)
                                                (:public kp)
                                                hlc)]

      (is (= :multi-system-snapshot (:type composite)))
      (is (contains? composite :snapshots))
      (is (= 2 (count (:snapshots composite))))
      (is (string? (:merkle-root composite)))
      (is (= hlc (:hlc composite)))
      (is (string? (:proposer composite)))
      (is (string? (:signature composite)))

      (testing "All snapshots have same HLC"
        (let [hlcs (map :hlc (vals (:snapshots composite)))]
          (is (apply = hlcs))))

      (testing "All snapshots are signed"
        (doseq [[sys-id signed-ref] (:snapshots composite)]
          (is (instance? urd.types.SignedSnapshotRef signed-ref))
          (is (string? (:signature signed-ref))))))))

(deftest verify-multi-snapshot-test
  (testing "Multi-system snapshot verification"
    (let [kp (crypto/ed25519-keypair)
          validator-set {(str "ed25519:" (crypto/bytes->base64 (:public kp))) (:public kp)}
          hlc (yt/->HLC 1234567890 0)

          snapshot-refs {:account-ledger (yt/->SnapshotRef
                                          "account-ledger"
                                          "snap-1"
                                          #{"parent-1"}
                                          nil
                                          "sha256:account-hash")
                         :cost-ledger (yt/->SnapshotRef
                                       "cost-ledger"
                                       "snap-2"
                                       #{"parent-2"}
                                       nil
                                       "sha256:cost-hash")}

          composite (crypto/sign-multi-snapshot snapshot-refs
                                                (:private kp)
                                                (:public kp)
                                                hlc)

          result (crypto/verify-multi-snapshot composite validator-set)]

      (is (:valid? result) "Valid composite should verify")
      (is (:merkle-valid? result))
      (is (:composite-signature-valid? result))
      (is (:hlc-consistent? result))
      (is (every? true? (vals (:individual-results result)))))))
