(ns urd.crypto
  "Urd's runes - cryptographic inscriptions of truth.

  Urd (Urðr) is the Norn who carves runes into Yggdrasil's bark,
  establishing immutable truth about what has become.

  This namespace provides ED25519 signature support for yggdrasil SnapshotRefs:
  - Single-validator signatures (author-id + signature)
  - Multi-validator certificates (2f+1 quorum)
  - Merkle root computation for multi-system snapshots

  Key operations:
  - sign-snapshot: Carve a rune (sign) into a SnapshotRef
  - verify-signature: Verify Urd's inscription
  - add-signature: Accumulate signatures for certificate
  - has-quorum?: Check if 2f+1 threshold reached
  - verify-certificate: Verify all signatures in certificate"
  (:require [yggdrasil.types :as yt]
            [urd.types :as t]
            #?(:clj [buddy.core.keys :as keys]
               :cljs [goog.crypt :as gcrypt])
            #?(:clj [buddy.core.codecs :as codecs]
               :cljs [goog.crypt.base64 :as base64])
            #?(:clj [buddy.sign.util :as sign-util]))
  #?(:clj (:import [org.bouncycastle.crypto.params Ed25519PrivateKeyParameters
                    Ed25519PublicKeyParameters]
                   [org.bouncycastle.crypto.signers Ed25519Signer]
                   [java.security MessageDigest]
                   [java.nio.charset StandardCharsets])))

;; ============================================================
;; ED25519 Signature Operations (JVM)
;; ============================================================

#?(:clj
   (defn ed25519-keypair
     "Generate a new ED25519 keypair.
      Returns {:public <32-byte-array> :private <32-byte-array>}"
     []
     (let [private-key (Ed25519PrivateKeyParameters. (java.security.SecureRandom.))
           public-key (.generatePublicKey private-key)]
       {:private (.getEncoded private-key)
        :public (.getEncoded public-key)})))

#?(:clj
   (defn ed25519-sign
     "Sign a message with ED25519 private key.

      Args:
        private-key - 32-byte private key
        message - bytes to sign

      Returns:
        64-byte signature"
     [private-key message]
     (let [signer (Ed25519Signer.)
           private-params (Ed25519PrivateKeyParameters. private-key 0)]
       (.init signer true private-params)
       (.update signer message 0 (alength message))
       (.generateSignature signer))))

#?(:clj
   (defn ed25519-verify
     "Verify an ED25519 signature.

      Args:
        public-key - 32-byte public key
        message - bytes that were signed
        signature - 64-byte signature

      Returns:
        Boolean - true if signature valid"
     [public-key message signature]
     (try
       (let [verifier (Ed25519Signer.)
             public-params (Ed25519PublicKeyParameters. public-key 0)]
         (.init verifier false public-params)
         (.update verifier message 0 (alength message))
         (.verifySignature verifier signature))
       (catch Exception _
         false))))

;; ============================================================
;; ED25519 Signature Operations (ClojureScript - Placeholder)
;; ============================================================

#?(:cljs
   (defn ed25519-keypair
     "Generate ED25519 keypair (ClojureScript placeholder).
      TODO: Implement using tweetnacl.js or similar"
     []
     (throw (js/Error. "ED25519 not yet implemented for ClojureScript"))))

#?(:cljs
   (defn ed25519-sign
     [private-key message]
     (throw (js/Error. "ED25519 not yet implemented for ClojureScript"))))

#?(:cljs
   (defn ed25519-verify
     [public-key message signature]
     (throw (js/Error. "ED25519 not yet implemented for ClojureScript"))))

;; ============================================================
;; Encoding Helpers
;; ============================================================

(defn bytes->base64
  "Encode byte array to base64 string."
  [bytes]
  #?(:clj (codecs/bytes->b64-str bytes)
     :cljs (base64/encodeByteArray bytes)))

(defn base64->bytes
  "Decode base64 string to byte array."
  [s]
  #?(:clj (codecs/b64->bytes s)
     :cljs (base64/decodeStringToByteArray s)))

(defn bytes->hex
  "Encode byte array to hex string."
  [bytes]
  #?(:clj (codecs/bytes->hex bytes)
     :cljs (gcrypt/byteArrayToHex bytes)))

(defn hex->bytes
  "Decode hex string to byte array."
  [s]
  #?(:clj (codecs/hex->bytes s)
     :cljs (gcrypt/hexToByteArray s)))

;; ============================================================
;; Canonical Message Construction
;; ============================================================

(defn snapshot-canonical-message
  "Generate canonical byte representation of SnapshotRef for signing.

   Uses pr-str for deterministic EDN serialization. Signs over:
   - system-id: Prevents cross-system signature replay
   - snapshot-id: Identifies specific snapshot
   - parent-ids: Prevents DAG rewriting attacks (sorted for determinism)
   - hlc: Prevents timestamp manipulation
   - content-hash: Binds signature to actual data content

   Does NOT sign metadata, signatures, or author-id (would be circular).

   Args:
     snapshot-ref - SnapshotRef or SignedSnapshotRef

   Returns:
     Byte array suitable for signing"
  [snapshot-ref]
  (let [canonical-map {:system-id (:system-id snapshot-ref)
                       :snapshot-id (:snapshot-id snapshot-ref)
                       :parent-ids (sort (:parent-ids snapshot-ref))  ; Sorted!
                       :hlc [(:physical (:hlc snapshot-ref))
                             (:logical (:hlc snapshot-ref))]
                       :content-hash (:content-hash snapshot-ref)}
        edn-str (pr-str canonical-map)]
    #?(:clj (.getBytes edn-str StandardCharsets/UTF_8)
       :cljs (.encode (js/TextEncoder.) edn-str))))

;; ============================================================
;; Merkle Root Computation
;; ============================================================

#?(:clj
   (defn sha256-bytes
     "Compute SHA-256 hash of bytes."
     [bytes]
     (let [digest (MessageDigest/getInstance "SHA-256")]
       (.digest digest bytes))))

#?(:cljs
   (defn sha256-bytes
     "Compute SHA-256 hash of bytes (ClojureScript placeholder).
      TODO: Implement using crypto-js or Web Crypto API"
     [bytes]
     (throw (js/Error. "SHA-256 not yet implemented for ClojureScript"))))

(defn compute-merkle-root
  "Compute Merkle root of content hashes.

   For multi-system snapshots, this creates a single hash
   binding all system states together.

   Args:
     content-hashes - Collection of content-hash strings

   Returns:
     String - 'sha256:base64-hash'"
  [content-hashes]
  (let [;; Sort for determinism
        sorted-hashes (sort content-hashes)
        ;; Concatenate all hashes
        concatenated (apply str sorted-hashes)
        ;; Hash the concatenation
        hash-bytes (sha256-bytes #?(:clj (.getBytes concatenated StandardCharsets/UTF_8)
                                    :cljs (.encode (js/TextEncoder.) concatenated)))]
    (str "sha256:" (bytes->base64 hash-bytes))))

;; ============================================================
;; High-Level Signing API
;; ============================================================

(defn sign-snapshot
  "Sign a SnapshotRef with validator's private key.

   Creates a SignedSnapshotRef with:
   - author-id: Base64-encoded public key (prefixed with 'ed25519:')
   - signature: Base64-encoded ED25519 signature
   - signatures: Empty map (for accumulating other validators' signatures)
   - metadata: Optional metadata map

   Args:
     snapshot-ref - SnapshotRef to sign
     private-key - 32-byte ED25519 private key
     public-key - 32-byte ED25519 public key
     metadata - Optional map of consensus metadata

   Returns:
     SignedSnapshotRef with signature"
  ([snapshot-ref private-key public-key]
   (sign-snapshot snapshot-ref private-key public-key {}))
  ([snapshot-ref private-key public-key metadata]
   (let [message (snapshot-canonical-message snapshot-ref)
         signature (ed25519-sign private-key message)
         author-id (str "ed25519:" (bytes->base64 public-key))]
     (t/->SignedSnapshotRef
      (:system-id snapshot-ref)
      (:snapshot-id snapshot-ref)
      (:parent-ids snapshot-ref)
      (:hlc snapshot-ref)
      (:content-hash snapshot-ref)
      author-id
      (bytes->base64 signature)
      {}  ; Empty signatures map
      metadata))))

(defn verify-signature
  "Verify signature on a SignedSnapshotRef.

   Args:
     signed-ref - SignedSnapshotRef with signature
     expected-public-key - Optional. If provided, verifies signature is from this key.
                          If nil, extracts public key from author-id.

   Returns:
     Boolean - true if signature valid"
  ([signed-ref]
   ;; Extract public key from author-id
   (let [author-id (:author-id signed-ref)
         public-key-b64 (subs author-id (count "ed25519:"))
         public-key (base64->bytes public-key-b64)]
     (verify-signature signed-ref public-key)))
  ([signed-ref expected-public-key]
   (try
     (let [message (snapshot-canonical-message signed-ref)
           signature (base64->bytes (:signature signed-ref))]
       (ed25519-verify expected-public-key message signature))
     (catch #?(:clj Exception :cljs js/Error) _
       false))))

(defn add-signature
  "Add a validator's signature to a SignedSnapshotRef.

   Used to accumulate signatures for building certificates (2f+1 quorum).

   Args:
     signed-ref - SignedSnapshotRef
     validator-id - Public key identifier (e.g., 'ed25519:base64-key')
     signature - Base64-encoded signature string

   Returns:
     Updated SignedSnapshotRef with signature added to :signatures map"
  [signed-ref validator-id signature]
  (update signed-ref :signatures assoc validator-id signature))

(defn has-quorum?
  "Check if SignedSnapshotRef has 2f+1 signatures from validator set.

   Byzantine fault tolerance requires 2f+1 signatures where:
   - f = maximum number of Byzantine (malicious) validators
   - Total validators = 3f+1
   - Quorum = 2f+1

   Args:
     signed-ref - SignedSnapshotRef with accumulated signatures
     validator-set - Set of validator public key identifiers

   Returns:
     Boolean - true if quorum reached"
  [signed-ref validator-set]
  (let [;; Include the author's signature
        all-signatures (assoc (:signatures signed-ref)
                              (:author-id signed-ref)
                              (:signature signed-ref))
        ;; Count valid signatures from validator set
        valid-sigs (filter #(contains? validator-set %) (keys all-signatures))
        num-validators (count validator-set)
        quorum-size (inc (quot (* 2 num-validators) 3))]  ; 2f+1 where n=3f+1
    (>= (count valid-sigs) quorum-size)))

(defn verify-certificate
  "Verify all signatures in a certificate.

   A certificate is a SignedSnapshotRef that has reached quorum (2f+1).
   This function verifies:
   1. Author's signature is valid
   2. All accumulated signatures are valid
   3. Quorum threshold is met

   Args:
     signed-ref - SignedSnapshotRef with certificate
     validator-set - Map of {validator-id → public-key-bytes}

   Returns:
     {:valid? Boolean
      :signer-count Int
      :invalid-signers [validator-id ...]
      :has-quorum? Boolean}"
  [signed-ref validator-set]
  (let [;; Verify author signature
        author-valid? (verify-signature signed-ref)

        ;; Verify all accumulated signatures
        invalid-signers (atom [])
        valid-count (atom (if author-valid? 1 0))

        ;; Check each signature in :signatures map
        _ (doseq [[validator-id sig-str] (:signatures signed-ref)]
            (when-let [public-key (get validator-set validator-id)]
              (let [;; Create temp ref with this signature to verify
                    temp-ref (assoc signed-ref
                                    :author-id validator-id
                                    :signature sig-str)]
                (if (verify-signature temp-ref public-key)
                  (swap! valid-count inc)
                  (swap! invalid-signers conj validator-id)))))

        ;; Check quorum
        total-validators (count validator-set)
        quorum-size (inc (quot (* 2 total-validators) 3))
        has-quorum? (>= @valid-count quorum-size)]

    {:valid? (and author-valid? (empty? @invalid-signers) has-quorum?)
     :signer-count @valid-count
     :invalid-signers @invalid-signers
     :has-quorum? has-quorum?}))

;; ============================================================
;; Multi-System Snapshot Signing
;; ============================================================

(defn sign-multi-snapshot
  "Sign a collection of SnapshotRefs as a composite multi-system snapshot.

   Creates a composite structure with:
   - Individual signed refs for each system
   - Shared HLC timestamp across all systems (causal binding)
   - Merkle root of all content hashes
   - Composite signature over merkle root

   Args:
     snapshot-refs - Map of {system-id → SnapshotRef}
     private-key - Validator's private key
     public-key - Validator's public key
     hlc - Shared HLC timestamp for all systems
     metadata - Optional composite metadata

   Returns:
     {:type :multi-system-snapshot
      :snapshots {system-id → SignedSnapshotRef ...}
      :merkle-root String
      :hlc HLC
      :proposer String (author-id)
      :signature String
      :metadata Map}"
  ([snapshot-refs private-key public-key hlc]
   (sign-multi-snapshot snapshot-refs private-key public-key hlc {}))
  ([snapshot-refs private-key public-key hlc metadata]
   (let [;; Add shared HLC to each ref and sign individually
         signed-refs (into {}
                           (map (fn [[sys-id ref]]
                                  [sys-id (sign-snapshot
                                           (assoc ref :hlc hlc)
                                           private-key
                                           public-key)])
                                snapshot-refs))

         ;; Compute merkle root of all content hashes
         content-hashes (map :content-hash (vals signed-refs))
         merkle-root (compute-merkle-root content-hashes)

         ;; Sign the merkle root as composite signature
         proposer-id (str "ed25519:" (bytes->base64 public-key))
         merkle-message #?(:clj (.getBytes merkle-root StandardCharsets/UTF_8)
                           :cljs (.encode (js/TextEncoder.) merkle-root))
         composite-sig (bytes->base64 (ed25519-sign private-key merkle-message))]

     {:type :multi-system-snapshot
      :snapshots signed-refs
      :merkle-root merkle-root
      :hlc hlc
      :proposer proposer-id
      :signature composite-sig
      :metadata metadata})))

(defn verify-multi-snapshot
  "Verify a multi-system composite snapshot.

   Verifies:
   1. Each individual system's signature
   2. Merkle root matches computed value
   3. Composite signature on merkle root
   4. All systems have same HLC timestamp

   Args:
     composite - Multi-system snapshot from sign-multi-snapshot
     validator-set - Map of {validator-id → public-key-bytes}

   Returns:
     {:valid? Boolean
      :individual-results {system-id → Boolean ...}
      :merkle-valid? Boolean
      :composite-signature-valid? Boolean
      :hlc-consistent? Boolean}"
  [composite validator-set]
  (let [;; Verify each individual signature
        individual-results (into {}
                                 (map (fn [[sys-id signed-ref]]
                                        [sys-id (verify-signature signed-ref)])
                                      (:snapshots composite)))

        ;; Verify merkle root
        content-hashes (map :content-hash (vals (:snapshots composite)))
        computed-merkle (compute-merkle-root content-hashes)
        merkle-valid? (= computed-merkle (:merkle-root composite))

        ;; Verify composite signature
        proposer-public-key (get validator-set (:proposer composite))
        composite-sig-valid? (when proposer-public-key
                               (try
                                 (let [merkle-message #?(:clj (.getBytes (:merkle-root composite)
                                                                         StandardCharsets/UTF_8)
                                                         :cljs (.encode (js/TextEncoder.)
                                                                        (:merkle-root composite)))
                                       signature (base64->bytes (:signature composite))]
                                   (ed25519-verify proposer-public-key merkle-message signature))
                                 (catch #?(:clj Exception :cljs js/Error) _
                                   false)))

        ;; Verify HLC consistency
        hlcs (map :hlc (vals (:snapshots composite)))
        hlc-consistent? (apply = hlcs)  ; All HLCs should be identical

        all-valid? (and (every? true? (vals individual-results))
                        merkle-valid?
                        composite-sig-valid?
                        hlc-consistent?)]

    {:valid? all-valid?
     :individual-results individual-results
     :merkle-valid? merkle-valid?
     :composite-signature-valid? composite-sig-valid?
     :hlc-consistent? hlc-consistent?}))
