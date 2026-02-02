(ns urd.types
  "Types for Byzantine Fault Tolerant yggdrasil.

  Urd (Urðr) is the Norn who carves runes into Yggdrasil's bark,
  establishing immutable truth about what has become."
  (:require [yggdrasil.types :as t]))

;; ============================================================
;; SignedSnapshotRef - cryptographically signed snapshot
;; ============================================================

(defrecord SignedSnapshotRef
           [system-id       ; String - which system instance
            snapshot-id     ; String - UUID or content-hash (native format)
            parent-ids      ; Set<String> - ancestry (DAG edges)
            hlc             ; HLC record - causal timestamp
            content-hash    ; String - REQUIRED for signed snapshots

   ;; Urd's inscriptions (cryptographic signatures):
            author-id       ; String - public key or validator ID (e.g., "ed25519:base64-key")
            signature       ; String - ED25519 signature (base64)
            signatures      ; Map<author-id → signature> - for certificates (2f+1)

   ;; Finalization metadata:
            metadata])      ; Map - {:finalized? Boolean, :height Long, :round Long, ...}

(defn snapshot-ref->signed
  "Convert plain yggdrasil SnapshotRef to SignedSnapshotRef (unsigned).

   Returns a SignedSnapshotRef with empty signature fields,
   ready to be signed with urd.crypto/sign-snapshot."
  [snapshot-ref]
  (map->SignedSnapshotRef
   (assoc snapshot-ref
          :author-id nil
          :signature nil
          :signatures {}
          :metadata {})))

;; ============================================================
;; JSON serialization
;; ============================================================

(defn signed-snapshot-ref->json
  "Convert SignedSnapshotRef to JSON-compatible map."
  [ref]
  {"system-id" (:system-id ref)
   "snapshot-id" (:snapshot-id ref)
   "parent-ids" (vec (:parent-ids ref))
   "hlc" (when-let [h (:hlc ref)]
           {"physical" (:physical h)
            "logical" (:logical h)})
   "content-hash" (:content-hash ref)
   "author-id" (:author-id ref)
   "signature" (:signature ref)
   "signatures" (:signatures ref)
   "metadata" (:metadata ref)})

(defn json->signed-snapshot-ref
  "Parse SignedSnapshotRef from JSON-compatible map."
  [m]
  (->SignedSnapshotRef
   (get m "system-id")
   (get m "snapshot-id")
   (set (get m "parent-ids"))
   (when-let [h (get m "hlc")]
     (t/->HLC (get h "physical") (get h "logical")))
   (get m "content-hash")
   (get m "author-id")
   (get m "signature")
   (get m "signatures")
   (get m "metadata")))
