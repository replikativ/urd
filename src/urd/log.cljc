(ns urd.log
  "Urðarbrunnr - Urd's Well, the consensus log.

  In Norse mythology, Urðarbrunnr (Urd's Well) is where the gods hold council
  beneath Yggdrasil's roots. This is where fate is decided.

  The consensus log stores:
  - Proposals: Signed snapshots proposed for finalization
  - Votes: Validator signatures accumulating toward quorum
  - Certificates: Snapshots that reached 2f+1 quorum
  - Finalization: Height ordering and finality markers

  This is the ONLY place where signatures are stored. Native systems
  (Datahike, Proximum, Scriptum) remain immutable and signature-free."
  (:require [konserve.core :as k]
            [urd.types :as t]
            [yggdrasil.types :as yt]
            [urd.crypto :as crypto]
            [hasch.core :as hasch]
            [superv.async :refer [go-try- <?-]]))

;; ============================================================
;; Proposal State Machine
;; ============================================================

(def proposal-states
  "Valid states for a proposal in the consensus log."
  #{:proposed      ; Initial state - signed by proposer
    :voting        ; Accumulating signatures
    :certified     ; Reached 2f+1 quorum
    :finalized     ; Ordered and finalized at specific height
    :rejected})    ; Failed to reach quorum or invalidated

;; ============================================================
;; Consensus Log Entry Types
;; ============================================================

(defrecord ProposalEntry
           [;; Identity
            proposal-id        ; UUID - unique identifier for this proposal

   ;; Snapshot reference (can be single or multi-system)
            snapshot-type      ; :single or :multi-system
            signed-snapshot    ; SignedSnapshotRef or multi-system composite

   ;; State tracking
            state              ; Keyword - one of proposal-states
            created-at         ; HLC - when proposal was created

   ;; Vote accumulation
            votes              ; Map<validator-id → signature> - accumulated votes

   ;; Finalization
            height             ; Long - consensus height (nil until finalized)
            finalized-at       ; HLC - when finalized (nil until finalized)

   ;; Metadata
            metadata])         ; Map - arbitrary metadata

(defrecord FinalizationEntry
           [;; Height ordering
            height             ; Long - consensus height
            hlc                ; HLC - timestamp of finalization

   ;; Finalized proposals at this height
            proposal-ids       ; Set<UUID> - proposals finalized at this height

   ;; Merkle commitment (for light client support)
            state-root         ; String - merkle root of all finalized state

   ;; Metadata
            metadata])         ; Map - round, block-hash, etc.

;; ============================================================
;; Consensus Log Protocol
;; ============================================================

(defprotocol ConsensusLog
  "Protocol for interacting with Urðarbrunnr (Urd's Well)."

  ;; Proposal operations
  (propose! [this signed-snapshot metadata]
    "Submit a signed snapshot for consensus.
     Returns proposal-id (UUID).")

  (get-proposal [this proposal-id]
    "Retrieve a proposal by ID.
     Returns ProposalEntry or nil.")

  (add-vote! [this proposal-id validator-id signature]
    "Add a validator's vote (signature) to a proposal.
     Returns updated ProposalEntry.")

  (update-state! [this proposal-id new-state]
    "Update proposal state (e.g., :voting → :certified).
     Returns updated ProposalEntry.")

  ;; Finalization operations
  (finalize! [this proposal-id height]
    "Mark a proposal as finalized at given height.
     Returns updated ProposalEntry.")

  (get-finalized-at-height [this height]
    "Get all proposals finalized at specific height.
     Returns FinalizationEntry or nil.")

  (get-latest-height [this]
    "Get the latest finalized height.
     Returns Long or nil if nothing finalized.")

  ;; Query operations
  (get-proposals-by-state [this state]
    "Get all proposals in a given state.
     Returns seq of ProposalEntry.")

  (get-proposals-for-snapshot [this snapshot-id]
    "Get all proposals for a specific snapshot-id.
     Returns seq of ProposalEntry.")

  (has-quorum? [this proposal-id validator-set]
    "Check if proposal has reached 2f+1 quorum.
     Returns boolean."))

;; ============================================================
;; Konserve-based Implementation
;; ============================================================

(defn- proposal-key
  "Generate storage key for proposal."
  [proposal-id]
  [:proposal proposal-id])

(defn- finalization-key
  "Generate storage key for finalization at height."
  [height]
  [:finalization height])

(defn- state-index-key
  "Generate storage key for state index."
  [state]
  [:index :state state])

(defn- snapshot-index-key
  "Generate storage key for snapshot index."
  [snapshot-id]
  [:index :snapshot snapshot-id])

(defn- metadata-key
  "Generate storage key for metadata."
  []
  [:metadata])

(defrecord KonserveConsensusLog
           [store          ; Konserve store
            validator-set] ; Map<validator-id → public-key> for quorum checking

  ConsensusLog

  (propose! [this signed-snapshot metadata]
    (go-try-
     (let [;; Content-addressed proposal ID from signed snapshot
            ;; Same snapshot content always produces same proposal-id
           proposal-id (hasch/uuid signed-snapshot)
           snapshot-type (if (= :multi-system-snapshot (:type signed-snapshot))
                           :multi-system
                           :single)
           snapshot-id (if (= snapshot-type :multi-system)
                         proposal-id  ; Multi-system uses proposal-id
                         (:snapshot-id signed-snapshot))

           entry (->ProposalEntry
                  proposal-id
                  snapshot-type
                  signed-snapshot
                  :proposed
                  (yt/hlc-now)
                  {}  ; Empty votes initially
                  nil nil  ; height, finalized-at
                  metadata)]

        ;; Store proposal
       (<?- (k/assoc-in store (proposal-key proposal-id) entry))

        ;; Update state index
       (let [state-idx (<?- (k/get-in store (state-index-key :proposed) #{}))]
         (<?- (k/assoc-in store (state-index-key :proposed)
                          (conj state-idx proposal-id))))

        ;; Update snapshot index
       (let [snap-idx (<?- (k/get-in store (snapshot-index-key snapshot-id) #{}))]
         (<?- (k/assoc-in store (snapshot-index-key snapshot-id)
                          (conj snap-idx proposal-id))))

       proposal-id)))

  (get-proposal [this proposal-id]
    (k/get-in store (proposal-key proposal-id)))

  (add-vote! [this proposal-id validator-id signature]
    (go-try-
     (let [entry (<?- (k/get-in store (proposal-key proposal-id)))]
       (if entry
         (let [updated (update entry :votes assoc validator-id signature)
                ;; Check if we should transition to :voting or :certified
                ;; Count includes proposer's signature + accumulated votes
               total-sigs (inc (count (:votes updated)))  ; +1 for proposer
               quorum-size (inc (quot (* 2 (count validator-set)) 3))
               new-state (cond
                           (>= total-sigs quorum-size) :certified
                           (> (count (:votes updated)) 0) :voting
                           :else (:state entry))

               final-entry (if (not= new-state (:state entry))
                             (do
                               ;; Update state indices
                               (<?- (update-state! this proposal-id new-state))
                               (assoc updated :state new-state))
                             updated)]

            ;; Store updated entry
           (<?- (k/assoc-in store (proposal-key proposal-id) final-entry))
           final-entry)
         nil))))

  (update-state! [this proposal-id new-state]
    (go-try-
     (let [entry (<?- (k/get-in store (proposal-key proposal-id)))]
       (when entry
         (let [old-state (:state entry)
               updated (assoc entry :state new-state)]

            ;; Remove from old state index
           (when old-state
             (let [old-idx (<?- (k/get-in store (state-index-key old-state) #{}))]
               (<?- (k/assoc-in store (state-index-key old-state)
                                (disj old-idx proposal-id)))))

            ;; Add to new state index
           (let [new-idx (<?- (k/get-in store (state-index-key new-state) #{}))]
             (<?- (k/assoc-in store (state-index-key new-state)
                              (conj new-idx proposal-id))))

            ;; Store updated entry
           (<?- (k/assoc-in store (proposal-key proposal-id) updated))
           updated)))))

  (finalize! [this proposal-id height]
    (go-try-
     (let [entry (<?- (k/get-in store (proposal-key proposal-id)))]
       (when (= :certified (:state entry))
         (let [finalized-at (yt/hlc-now)
               updated (-> entry
                           (assoc :state :finalized
                                  :height height
                                  :finalized-at finalized-at))]

            ;; Update proposal entry
           (<?- (update-state! this proposal-id :finalized))
           (<?- (k/assoc-in store (proposal-key proposal-id) updated))

            ;; Update finalization entry
           (let [fin-entry (<?- (k/get-in store (finalization-key height)))
                 updated-fin (if fin-entry
                               (update fin-entry :proposal-ids conj proposal-id)
                               (->FinalizationEntry
                                height
                                finalized-at
                                #{proposal-id}
                                nil  ; state-root computed separately
                                {}))]
             (<?- (k/assoc-in store (finalization-key height) updated-fin)))

            ;; Update latest height in metadata
           (let [meta (<?- (k/get-in store (metadata-key) {}))
                 current-height (get meta :latest-height 0)]
             (when (> height current-height)
               (<?- (k/assoc-in store (metadata-key)
                                (assoc meta :latest-height height)))))

           updated)))))

  (get-finalized-at-height [this height]
    (k/get-in store (finalization-key height)))

  (get-latest-height [this]
    (go-try-
     (let [meta (<?- (k/get-in store (metadata-key) {}))]
       (get meta :latest-height))))

  (get-proposals-by-state [this state]
    (go-try-
     (let [proposal-ids (<?- (k/get-in store (state-index-key state) #{}))]
       (when (seq proposal-ids)
         (loop [ids (seq proposal-ids)
                results []]
           (if-let [id (first ids)]
             (let [entry (<?- (k/get-in store (proposal-key id)))]
               (recur (rest ids) (conj results entry)))
             results))))))

  (get-proposals-for-snapshot [this snapshot-id]
    (go-try-
     (let [proposal-ids (<?- (k/get-in store (snapshot-index-key snapshot-id) #{}))]
       (when (seq proposal-ids)
         (loop [ids (seq proposal-ids)
                results []]
           (if-let [id (first ids)]
             (let [entry (<?- (k/get-in store (proposal-key id)))]
               (recur (rest ids) (conj results entry)))
             results))))))

  (has-quorum? [this proposal-id validator-set]
    (go-try-
     (let [entry (<?- (k/get-in store (proposal-key proposal-id)))]
       (when entry
         (let [;; Combine author signature + accumulated votes
               all-sigs (assoc (:votes entry)
                               (get-in entry [:signed-snapshot :author-id])
                               (get-in entry [:signed-snapshot :signature]))

                ;; Validator set maps UUID → public-key
                ;; Votes use either UUID (for votes) or public-key (for author)
               valid-public-keys (set (vals validator-set))

                ;; Count signatures that are either:
                ;; - A UUID in validator-set (votes), OR
                ;; - A public key in validator-set values (author)
               valid-count (count (filter (fn [signer-id]
                                            (or (contains? validator-set signer-id)
                                                (contains? valid-public-keys signer-id)))
                                          (keys all-sigs)))
                ;; Quorum = simple majority = ceiling(n/2)
                ;; For 3 validators: inc(quot 3 2) = inc(1) = 2
                ;; For 4 validators: inc(quot 4 2) = inc(2) = 3
               quorum-size (inc (quot (count validator-set) 2))]

           (>= valid-count quorum-size)))))))

;; ============================================================
;; Constructor
;; ============================================================

(defn create-consensus-log
  "Create a new ConsensusLog backed by konserve.

   Args:
     store - Konserve store instance
     validator-set - Map of {validator-id → public-key}

   Returns:
     ConsensusLog instance"
  [store validator-set]
  (->KonserveConsensusLog store validator-set))

;; ============================================================
;; Helper Functions
;; ============================================================

(defn build-certificate
  "Accumulate signatures from multiple validators into a certificate.

   Takes a signed snapshot and adds signatures from other validators
   until quorum is reached.

   Args:
     consensus-log - ConsensusLog instance
     signed-snapshot - Initial SignedSnapshotRef
     validator-signatures - Seq of [validator-id signature] pairs

   Returns:
     Channel with proposal-id when certificate is built"
  [consensus-log signed-snapshot validator-signatures]
  (go-try-
   (let [proposal-id (<?- (propose! consensus-log signed-snapshot {}))]
      ;; Add each validator's signature
     (doseq [[validator-id signature] validator-signatures]
       (<?- (add-vote! consensus-log proposal-id validator-id signature)))
     proposal-id)))

(defn get-certified-proposals
  "Get all proposals that have reached quorum but not yet finalized.

   Args:
     consensus-log - ConsensusLog instance

   Returns:
     Channel with seq of ProposalEntry"
  [consensus-log]
  (get-proposals-by-state consensus-log :certified))

(defn get-finalization-history
  "Get finalization history from start-height to end-height.

   Args:
     consensus-log - ConsensusLog instance
     start-height - Starting height (inclusive)
     end-height - Ending height (inclusive)

   Returns:
     Channel with seq of FinalizationEntry"
  [consensus-log start-height end-height]
  (go-try-
   (loop [h start-height
          results []]
     (if (<= h end-height)
       (let [fin-entry (<?- (get-finalized-at-height consensus-log h))]
         (recur (inc h)
                (if fin-entry
                  (conj results fin-entry)
                  results)))
       results))))
