(ns urd.consensus.algorithms.nakamoto
  "Nakamoto consensus -- the Bitcoin HEADER layer -- as a pure state machine on
  `urd.consensus.node`.

  Ported from `btcsuite/btcd` (read at Jul 2026). It is in the portfolio as a
  GENERALITY TEST, not a product: it is the only algorithm here with open
  membership and deep reorgs, and therefore the only remaining justification for
  the core protocol's revocable `:commit`/`:revert`. See the friction notes at
  the bottom of this docstring, which are the actual deliverable.

  ## Scope

  btcd draws the line for us. `maybeAcceptBlockHeader` (`accept.go:123-236`) is
  a complete consensus engine over headers alone, and `HeaderCtx`
  (`interfaces.go:36-55`) is a five-method interface -- Height, Bits, Timestamp,
  Parent, RelativeAncestorCtx -- that IS the generic Nakamoto surface. So:

    IN:  heaviest-chain fork choice, cumulative work, the compact target codec,
         difficulty retarget, double-SHA256 proof verification, median-time-past,
         the future bound, reorgs.
    OUT: the UTXO set, scripts, coinbase maturity, merkle root CONTENTS (an
         opaque payload commitment here), block size/weight, BIP30/34/65/66,
         versionbits, the testnet min-difficulty rule, and CHECKPOINTS -- which
         are deliberately dropped, because a checkpoint is exactly a violation
         of the open membership this algorithm is here to test.

  ## Mining is not in the state machine

  A nonce loop on the JVM is two to four orders of magnitude off an ASIC, and
  worse in a browser, so nothing here ever mines competitively. btcd agrees
  structurally: its CPU miner lives in `mining/`, not in `blockchain/`. `mine`
  below is a bounded, test-only toy, `step` never calls it, and a real deployment
  supplies solved headers from outside via `vertex-received` -- the same seam a
  `getblocktemplate` client uses. `template` is the pure query a miner needs.

  ## Arithmetic

  All 256-bit quantities go through `urd.consensus.bignat`, a portable limb
  implementation, rather than through BigInteger/BigInt reader conditionals.
  Fork choice compares cumulative work with a STRICT `>` (`chain.go:1257`), so
  ties go to the incumbent and first-seen wins; there is no height tie-break
  anywhere in Bitcoin. An approximate comparison would turn a tie into a reorg.

  ## Time

  `now` is an explicit parameter of every function that needs it, never an
  ambient clock. The node keeps `:now` in its state and advances it from a
  logical `:clock` timer, so a run is replayable. Note that the core protocol
  defines a `tick` EVENT for this and the simulator never delivers one -- see
  the friction notes.

  ## What this cost the core protocol

  1. `:revert` is under-specified. `[:revert {:to-vertex v}]` tells an
     interpreter where the committed prefix should now END, but not what was
     dropped, and it presumes the interpreter can LOCATE v in a sequence it was
     handed one `:commit` at a time. The simulator recorded reverts and never
     applied them, so its `agreement?` check could not have detected a
     reorg-induced divergence. Fixed here; the fix is what makes the deep-reorg
     test mean anything.

  2. `:commit`'s `:index` cannot be both \"globally increasing\" and \"the
     position of these vertices in the committed sequence\". For Raft and
     Snowman those coincide. Under a reorg they do not, and only the second is
     usable by a consumer that also honours `:revert`. We emit the position (the
     block height), which contradicts the docstring.

  3. `:persist-then`'s barrier does nothing here, and correctly so. The rule --
     gate exactly the messages that constitute this node's binding commitment --
     has an empty left-hand side under proof of work: a header is
     self-authenticating, a node signs nothing, and there is no equivocation to
     prevent. Nakamoto is the algorithm that shows the barrier is optional.

  4. `Membership` does not apply, for the second time (Snowman was the first).
     There is no validator set, so no predicate over statements is meaningful;
     eligibility is `hash <= target`, which is a property of the vertex, not of
     its author. `:validators` survives only as a gossip peer list."
  (:require [urd.consensus.node :as n]
            [urd.consensus.bignat :as bn]
            [hasch.core :as hasch]))

;; ============================================================
;; Chain parameters
;; ============================================================

(def mainnet-params
  "Bitcoin mainnet, minus everything out of scope.

  `:pow-limit-bits` 0x1d00ffff is mainnet's; tests use a far easier limit,
  because at this one a single block costs about 2^32 hashes."
  {:pow-limit-bits 0x1d00ffff
   :blocks-per-retarget 2016      ; targetTimespan / targetTimePerBlock
   :target-timespan 1209600       ; 14 days, in seconds
   :retarget-adjustment-factor 4  ; the [1/4, 4] clamp
   :median-time-blocks 11         ; `blockchain/blockindex.go`, medianTimeBlocks
   :max-future-drift 7200         ; `validate.go:26`, MaxTimeOffsetSeconds
   :no-retargeting? false})

(defn params
  "Merge overrides onto the mainnet rules and derive the clamp bounds.

  btcd derives these once in `New` (`chain.go:2250-2263`) rather than at each
  retarget, and so do we -- the min/max timespan are the same three constants
  every time."
  [overrides]
  (let [p (merge mainnet-params overrides)
        f (:retarget-adjustment-factor p)]
    (assoc p
           :min-retarget-timespan (quot (:target-timespan p) f)
           :max-retarget-timespan (* (:target-timespan p) f))))

;; ============================================================
;; The compact target codec  (workmath/difficulty.go:36-127)
;;
;; A 32-bit float-like encoding: 8 bits of base-256 exponent, one sign bit, 23
;; bits of mantissa, with N = (-1^sign) * mantissa * 256^(exponent-3).
;;
;; Field extraction uses quot/mod rather than shifts on purpose. A compact value
;; can exceed 2^31, and ClojureScript's `bit-shift-right` would treat it as a
;; SIGNED 32-bit integer -- 0xffffffff >> 24 is -1 there, not 255.
;; ============================================================

(defn compact-exponent [c] (quot c 16777216))
(defn compact-mantissa [c] (mod c 8388608))
(defn compact-negative?
  "Bit 23. Bitcoin never needs a negative target, but bitcoind encodes the sign
  bit anyway, so a header can claim one and must be rejected for it."
  [c]
  (odd? (quot c 8388608)))

(defn compact->target
  "The magnitude of a compact target, as a bignat. Callers must check
  `compact-negative?` separately -- see `target-valid?`."
  [c]
  (let [m (compact-mantissa c)
        e (compact-exponent c)]
    (if (<= e 3)
      (bn/from-int (quot m (bit-shift-left 1 (* 8 (- 3 e)))))
      (bn/shift-left (bn/from-int m) (* 8 (- e 3))))))

(defn target->compact
  "A bignat back to compact form.

  The renormalisation at the end is the subtle part: if the mantissa's high bit
  would land on the sign bit, the number is divided by 256 and the exponent
  incremented, so 0x01ff0000 (255) encodes as 0x0200ff00 rather than 0x01ff0000."
  [n]
  (if (bn/zero? n)
    0
    (let [e (bn/byte-length n)
          m (if (<= e 3)
              (* (bn/to-int n) (bit-shift-left 1 (* 8 (- 3 e))))
              (bn/to-int (bn/shift-right n (* 8 (- e 3)))))
          [m e] (if (pos? (bit-and m 0x00800000))
                  [(quot m 256) (inc e)]
                  [m e])]
      (+ (* e 16777216) m))))

(defn calc-work
  "floor(2^256 / (target + 1)) -- `workmath/difficulty.go:135-149`.

  The inverse of the target, because a LOWER target is harder. The +1 in the
  denominator avoids a division by zero at target 0 and makes the value fit;
  the 2^256 numerator keeps it an integer."
  [bits]
  (let [t (compact->target bits)]
    (if (or (compact-negative? bits) (bn/zero? t))
      bn/zero
      (bn/div (bn/pow2 256) (bn/add t bn/one)))))

(defn target-valid?
  "The target must be positive and no easier than the chain's limit
  (`validate.go:372-388`)."
  [p bits]
  (let [t (compact->target bits)]
    (and (not (compact-negative? bits))
         (not (bn/zero? t))
         (bn/le t (compact->target (:pow-limit-bits p))))))

;; ============================================================
;; Header serialization and proof of work
;; ============================================================

(def zero-hash (apply str (repeat 64 \0)))

(def ^:private hex-alphabet (set "0123456789abcdef"))

(defn- u32? [n]
  ;; Range BEFORE the integrality cast, and the order is the whole point. `long`
  ;; is a checked cast on the JVM: `(long 1e30)` throws `Value out of range for
  ;; long`, and so does a bigint beyond 2^63. Testing integrality first therefore
  ;; threw on exactly the adversarial input this predicate exists to reject,
  ;; inside the pure state machine, from the first line of `process-header`.
  ;; It was also a platform split -- cljs `long` truncates rather than throws, so
  ;; the same header was rejected there and fatal here.
  ;; The range checks also dispose of NaN and the infinities without any host
  ;; interop: every comparison against NaN is false, and the infinities fail one
  ;; bound or the other.
  (and (number? n)
       (>= n 0)
       (< n 4294967296)
       (== n (long n))))

(defn- hash-hex? [s]
  (and (string? s) (= 64 (count s)) (every? hex-alphabet s)))

(defn well-formed?
  "Are the six header fields of the right shape?

  Open membership means anyone may send anything, so this is checked BEFORE the
  header is hashed -- serializing a field that is not a uint32, or a parent hash
  that is not 64 hex characters, would throw inside the pure state machine and
  take the node down. btcd gets this for free from Go's static types and the
  wire decoder; we have to do it explicitly, and it belongs at the very front
  because everything downstream, `header-id` included, presumes it."
  [header]
  (and (map? header)
       (u32? (:version header))
       (u32? (:time header))
       (u32? (:bits header))
       (u32? (:nonce header))
       (hash-hex? (:prev header))
       (hash-hex? (:merkle-root header))))

(defn- u32-le [n]
  (when (or (neg? n) (>= n 4294967296))
    (throw (ex-info "header field is not a uint32" {:n n})))
  [(mod n 256)
   (mod (quot n 256) 256)
   (mod (quot n 65536) 256)
   (quot n 16777216)])

(defn serialize-header
  "The canonical 80 bytes -- `wire/blockheader.go:183-215`.

  version LE32 | prev 32 | merkle-root 32 | time LE32 | bits LE32 | nonce LE32.

  Hash-valued fields are carried here as DISPLAY hex, i.e. the reversed form
  everyone quotes block ids in, so they are reversed back to internal order on
  the way out. That is the same convention btcd's `chainhash.Hash.String` uses."
  [{:keys [version prev merkle-root time bits nonce]}]
  (vec (concat (u32-le version)
               (reverse (bn/hex->bytes prev))
               (reverse (bn/hex->bytes merkle-root))
               (u32-le time)
               (u32-le bits)
               (u32-le nonce))))

(defn- sha256d
  "Double SHA-256 over a vector of unsigned bytes.

  The only host interop in this namespace. `hasch.core/sha256` is synchronous on
  both platforms -- JVM `MessageDigest`, cljs `goog.crypt.Sha256` -- which is
  what lets proof verification run INSIDE the pure state machine. Ed25519
  verification cannot, because Web Crypto is promise-based; that asymmetry is
  the whole reason the core has a `:verified-by` edge."
  [bs]
  #?(:clj (let [d (hasch/sha256 (byte-array (map unchecked-byte bs)))]
            (mapv #(bit-and (int %) 0xff) (hasch/sha256 d)))
     :cljs (let [d (hasch/sha256 (.from js/Uint8Array (clj->js bs)))]
             (vec (array-seq (hasch/sha256 d))))))

(defn header-id
  "The block id: SHA256d of the 80 bytes, reversed into display order."
  [header]
  (bn/bytes->hex (reverse (sha256d (serialize-header header)))))

(defn- hash-number
  "The block hash as a 256-bit integer, LITTLE-endian -- btcd's `HashToBig`
  reverses the bytes before comparing. Since the display id is already the
  reversed form, reading it big-endian gives exactly that number."
  [id]
  (bn/from-hex id))

(defn pow-valid?
  "Does the header's own hash meet the target it claims?

  Note `>` and not `>=` in btcd's rejection (`validate.go:394`): a hash exactly
  EQUAL to the target passes."
  [header]
  (bn/le (hash-number (header-id header)) (compact->target (:bits header))))

;; ============================================================
;; The block index
;;
;; A block entry is
;;   {:id :header :parent :height :work-sum}
;; and every consensus quantity is a fold over the ancestor path, which is the
;; whole reason a reorg here is a pointer swap. There is no undo log because
;; there is nothing destructively mutated to undo.
;; ============================================================

(defn blk [state id] (get-in state [:blocks id]))
(defn tip [state] (:tip state))
(defn tip-work [state] (:work-sum (blk state (:tip state))))
(defn height [state id] (:height (blk state id)))

(defn ancestor-at-height
  "The ancestor of `id` at absolute height `h`, or nil."
  [state id h]
  (loop [id id]
    (let [b (blk state id)]
      (cond
        (nil? b) nil
        (= h (:height b)) id
        (< (:height b) h) nil
        :else (recur (:parent b))))))

(defn relative-ancestor
  "`HeaderCtx.RelativeAncestorCtx`: the ancestor `distance` blocks back."
  [state id distance]
  (ancestor-at-height state id (- (height state id) distance)))

(defn find-fork
  "The last common ancestor of two blocks -- `chainview.go:292-322`.

  Walk the deeper one up to the shallower one's height first, then step both up
  in lockstep. Returns nil if they are not in the same tree."
  [state a b]
  (let [h (min (height state a) (height state b))
        a (ancestor-at-height state a h)
        b (ancestor-at-height state b h)]
    (loop [a a, b b]
      (cond
        (or (nil? a) (nil? b)) nil
        (= a b) a
        :else (recur (:parent (blk state a)) (:parent (blk state b)))))))

(defn path-from
  "The blocks strictly after `from` up to and including `to`, in order.

  This is `getReorganizeNodes`'s attach list (`chain.go:512-558`), and it serves
  as the DETACH list too -- `reorg-effects` calls it a second time from the fork
  point to the old tip. What ours needs no counterpart for is btcd's undo DATA:
  every consensus quantity here is a fold over the ancestor path, so a detached
  block leaves nothing to roll back. The detached blocks still have to be NAMED,
  because `:revert` carries `:dropped` and the interpreter checks it -- see the
  note on `reorg-effects`.

  ASCENDING, which is the inverse of btcd's descending `detachNodes`. btcd walks
  down because it undoes one block at a time; here the list is compared against
  the interpreter's committed vector, which is ascending."
  [state from to]
  (loop [id to, acc ()]
    (if (or (nil? id) (= id from))
      (vec acc)
      (recur (:parent (blk state id)) (conj acc id)))))

;; ============================================================
;; Median time past  (blockindex.go:318-353)
;; ============================================================

(defn median-time-past
  "The median of the last `median-time-blocks` timestamps INCLUDING this block.

  btcd takes `timestamps[n/2]` after sorting -- integer division, deliberately
  not the average of the middle two when n is even. The constant is 11, so n is
  even only in the first ten blocks of a chain, but the rule is consensus and is
  reproduced exactly. The result is therefore always an ELEMENT of its input."
  [p state id]
  (let [ts (loop [id id, n 0, acc []]
             (let [b (blk state id)]
               (if (or (nil? b) (>= n (:median-time-blocks p)))
                 acc
                 (recur (:parent b) (inc n) (conj acc (get-in b [:header :time]))))))
        sorted (vec (sort ts))]
    (when (seq sorted)
      (nth sorted (quot (count sorted) 2)))))

;; ============================================================
;; Difficulty retarget  (difficulty.go:136-231)
;; ============================================================

(defn retarget
  "The pure retarget arithmetic, given the two boundary timestamps.

  Separated from chain walking so it can be property-tested directly: the
  result is always within [old/4, old*4] and never easier than the pow limit."
  [p old-bits first-time last-time]
  (let [actual (- last-time first-time)
        adjusted (cond
                   (< actual (:min-retarget-timespan p)) (:min-retarget-timespan p)
                   (> actual (:max-retarget-timespan p)) (:max-retarget-timespan p)
                   :else actual)
        old-target (compact->target old-bits)
        ;; Floor division, exactly as bitcoind does it -- the rounding is
        ;; consensus-visible.
        new-target (bn/div-small (bn/mul-small old-target adjusted)
                                 (:target-timespan p))
        pow-limit (compact->target (:pow-limit-bits p))
        capped (if (bn/gt new-target pow-limit) pow-limit new-target)]
    (target->compact capped)))

(defn next-work-required
  "The `bits` the child of `last-id` must carry -- `calcNextRequiredDifficulty`.

  The famous off-by-one is in `first`: btcd asks for the ancestor
  `blocksPerRetarget - 1` back, so the span runs over 2015 inter-block
  intervals but is divided by a target timespan computed for 2016. Mainnet
  therefore aims at 600.2977 seconds per block rather than 600. It is
  reproduced, not fixed: it is consensus.

  The testnet min-difficulty reduction is deliberately absent -- out of scope."
  [p state last-id]
  (cond
    (:no-retargeting? p) (:pow-limit-bits p)
    (nil? last-id) (:pow-limit-bits p)
    :else
    (let [last-b (blk state last-id)
          next-height (inc (:height last-b))]
      (if-not (zero? (mod next-height (:blocks-per-retarget p)))
        (get-in last-b [:header :bits])
        (let [first-id (relative-ancestor state last-id
                                          (dec (:blocks-per-retarget p)))]
          (if (nil? first-id)
            (throw (ex-info "unable to obtain previous retarget block"
                            {:last last-id :height (:height last-b)}))
            (retarget p (get-in last-b [:header :bits])
                      (get-in (blk state first-id) [:header :time])
                      (get-in last-b [:header :time]))))))))

;; ============================================================
;; Validation
;; ============================================================

(defn check-header-sanity
  "Context-free checks -- `CheckBlockHeaderSanity` (`validate.go:495-530`).

  `now` is a parameter, not a clock read. btcd consults a `MedianTimeSource`
  here, an adjusted network time; we take the caller's word, which is the same
  thing with the adjustment moved outside the state machine."
  [p header now]
  (cond
    (not (well-formed? header)) :malformed
    (not (target-valid? p (:bits header))) :unexpected-difficulty
    (not (pow-valid? header)) :high-hash
    (> (:time header) (+ now (:max-future-drift p))) :time-too-new
    :else nil))

(defn check-header-context
  "Checks that depend on the header's position -- `CheckBlockHeaderContext`
  (`validate.go:744-800`), minus the version-bit and checkpoint rules.

  The timestamp must be STRICTLY after the median time past of the parent;
  `!header.Timestamp.After(medianTime)` rejects equality."
  [p state header parent-id]
  (let [expected (next-work-required p state parent-id)]
    (cond
      (not= (:bits header) expected) :unexpected-difficulty
      (<= (:time header) (median-time-past p state parent-id)) :time-too-old
      :else nil)))

;; ============================================================
;; Connecting a header
;; ============================================================

(defn- index-block
  "Add a validated header to the index, folding height and cumulative work off
  its parent -- `initBlockNode` (`blockindex.go:119-135`)."
  [state id header]
  (let [parent (blk state (:prev header))
        ;; The PARENT'S OWN id object, not the equal-but-distinct string that
        ;; arrived on the wire.
        ;;
        ;; Every block holds three 64-character hex strings -- its id, its
        ;; parent's id, and a merkle root -- and measured, those strings are
        ;; the single largest part of the index: 287 bytes of a 712-byte
        ;; block. The parent's id is stored twice over, once as the key it is
        ;; filed under and once as the `:prev` the child parsed, with identical
        ;; content and no sharing.
        ;;
        ;; `(blk state (:prev header))` already resolved the parent, so its
        ;; canonical id is in hand for free. Substituting it is
        ;; value-preserving -- `hasch/edn-hash` hashes by value, so `header-id`
        ;; is unchanged and so is anything serialised from it -- and it removes
        ;; one of the three strings per block outright.
        prev (or (:id parent) (:prev header))]
    (assoc-in state [:blocks id]
              {:id id
               :header (assoc header :prev prev)
               :parent prev
               :height (inc (:height parent))
               :work-sum (bn/add (:work-sum parent) (calc-work (:bits header)))})))

(def default-snapshot-interval
  "Headers accepted between rewrites of the durable log.

  Nakamoto writes one record per header and `restore` replays every one of
  them, so a node that has been following the chain for a year pays a year of
  reads to start. This collapses them: one record standing in for all the
  headers before it.

  What this does NOT do is bound MEMORY. The header index still holds every
  block ever seen, and that is deliberate rather than unfinished -- dropping
  old headers caps how deep a reorg can be validated, which is a consensus
  policy and not a storage optimisation. Bitcoin keeps all headers forever for
  exactly this reason; they are 80 bytes and the alternative is a chain that
  silently refuses a reorganisation it cannot check. The decision belongs to
  whoever is choosing the finality depth, so it is not made here."
  2000)

(defn- snapshot-record
  "Every header in the index, as one durable record.

  Ordered by HEIGHT, which is what makes it replayable: `index-block` reads the
  parent's height and work-sum, and `restore` skips a header whose parent it
  has not indexed yet. A snapshot in map order would silently drop every
  header that happened to precede its parent -- not an error, just a shorter
  chain, which is the shape of bug that survives a test suite.

  `::tip` is carried explicitly rather than re-derived. Restore adopts the
  first block to reach the highest work, so among EQUAL-work candidates the
  replay order decides, and a snapshot is in height order rather than arrival
  order. Re-deriving would let a node pick a different tip than the one it held
  a moment earlier, which is a fork produced by restarting."
  [state]
  {:writes {::snapshot (->> (vals (:blocks state))
                            (sort-by :height)
                            (mapv :header))
            ::tip (:tip state)}
   :durable? true})

(defn- reorg-effects
  "Move the tip to `new-tip`, emitting the commit/revert pair that describes it.

  This is the payoff of the header layer: `detach` needs no undo data at all, so
  a reorg of any depth is one `:revert` naming the fork point plus one `:commit`
  of the new branch. btcd's two-phase reorg, spend journal and undo machinery
  exist only because its UTXO set is a destructively-mutated map."
  [state new-tip]
  (let [old-tip (:tip state)
        fork (find-fork state old-tip new-tip)
        attach (path-from state fork new-tip)
        detached? (not= fork old-tip)]
    (n/result (assoc state :tip new-tip)
              (concat (when detached?
                        ;; The detached path is named explicitly rather than
                        ;; left for the interpreter to search for: reverting to
                        ;; a vertex that was never committed -- genesis, where
                        ;; every reorg-to-root lands -- is otherwise
                        ;; indistinguishable from a mistyped id, and both would
                        ;; wipe committed history.
                        [(n/revert fork (path-from state fork old-tip))
                         (n/log-effect :info
                                       {:event :reorg
                                        :fork fork
                                        :detached (count (path-from state fork old-tip))
                                        :attached (count attach)})])
                      [(n/commit attach)]))))

(defn- connect-one
  "Validate and index a single header whose parent is already known.

  Returns {:state s :effects fx :status k} where status is :accepted,
  :duplicate, or a rejection keyword."
  [state header]
  (let [p (:params state)
        id (header-id header)]
    (cond
      (blk state id)
      (assoc (n/result state) :status :duplicate)

      :else
      (if-let [err (or (check-header-sanity p header (:now state))
                       (check-header-context p state header (:prev header)))]
        (assoc (n/result (update-in state [:rejected err] (fnil inc 0)))
               :status err)
        (let [state (-> (index-block state id header)
                        (update :headers-since-snapshot (fnil inc 0)))
              due? (>= (:headers-since-snapshot state)
                       (:snapshot-interval state default-snapshot-interval))
              state (cond-> state due? (assoc :headers-since-snapshot 0))
              relay (n/broadcast :headers {:kind :header :header header})
              new? (bn/gt (:work-sum (blk state id)) (tip-work state))
              {state :state fx :effects} (if new?
                                           (reorg-effects state id)
                                           (n/result state))
              ;; AFTER the tip has moved, not before. Built here rather than
              ;; alongside the write it rides on, because `snapshot-record`
              ;; reads `:tip` and the tip for this header is set by
              ;; `reorg-effects` below the point where the write is assembled.
              ;; Snapshotting first recorded the PREVIOUS tip while the index
              ;; already held the new header -- so a restored node came back
              ;; one block behind, holding a header with more work than its own
              ;; tip and no arrival left to make it move. Stuck, silently, and
              ;; only ever on the block where a snapshot happened to fall.
              persist (n/persist-then
                       (cond->
                        {:writes {[:header id] header}
                        ;; No `:then`. Under proof of work a node signs nothing,
                        ;; so it has no binding commitment to gate -- the header
                        ;; is self-authenticating and safe to relay before the
                        ;; write lands. See the friction notes.
                         :durable? true
                         :token id}
                         due? (assoc :checkpoint [(snapshot-record state)])))]
          (assoc (n/result state (concat [persist relay] fx)) :status :accepted))))))

(defn- drain-orphans
  "Connect any orphans that the newly-connected block is the parent of.

  A fixpoint rather than a single pass: connecting one orphan can unlock the
  next, which is how a whole competing branch delivered out of order lands."
  [state id]
  (loop [state state, pending [id], acc []]
    (if (empty? pending)
      (n/result state acc)
      (let [parent (first pending)
            kids (get-in state [:orphans parent])
            state (-> state
                      (update :orphans dissoc parent)
                      (update :orphan-at #(apply dissoc % (map header-id kids))))]
        (if (empty? kids)
          (recur state (rest pending) acc)
          (let [[state acc unlocked]
                (reduce (fn [[st acc unlocked] h]
                          (let [r (connect-one st h)]
                            [(:state r)
                             (into acc (:effects r))
                             (if (= :accepted (:status r))
                               (conj unlocked (header-id h))
                               unlocked)]))
                        [state acc []]
                        ;; SORTED. The orphan pool is a set, and set iteration
                        ;; order is not guaranteed to be equal on the JVM and in
                        ;; a browser. Connection order decides which of two
                        ;; equal-work siblings is seen first, and first-seen is
                        ;; the tie-break -- so an unsorted iteration here would
                        ;; be a platform-dependent fork.
                        (sort-by header-id kids))]
            (recur state (into (vec (rest pending)) unlocked) acc)))))))

(def ^:private max-orphans
  "A bound, because an unbounded orphan pool is a memory-exhaustion vector on an
  open-membership network where anyone may send anything."
  256)

(def ^:private orphan-expiry-seconds
  "`chain.go:298-315` -- btcd stamps each orphan with `expiration: now + 1h` and
  sweeps the expired ones before admitting a new one."
  3600)

(defn- forget-orphan [state id]
  (-> state
      (update :orphan-at dissoc id)
      (update :orphans
              (fn [m]
                (reduce-kv (fn [acc parent kids]
                             (let [kids' (into #{} (remove #(= id (header-id %))) kids)]
                               (if (seq kids') (assoc acc parent kids') acc)))
                           {}
                           m)))))

(defn- reap-orphans
  "Make room for one more orphan: drop the expired, then, if still full, the
  oldest.

  btcd EVICTS to make room (`chain.go:318-340`); refusing the new one instead --
  which this did -- is strictly more grief-able. 256 junk headers naming parents
  that will never arrive wedged the pool permanently, after which every
  legitimate out-of-order header was dropped, and the only way back was the
  invented `:announce` re-broadcast."
  [state]
  (let [cutoff (- (:now state) orphan-expiry-seconds)
        expired (keep (fn [[id {at :at}]] (when (< at cutoff) id)) (:orphan-at state))
        state (reduce forget-orphan state expired)]
    (if (< (count (:orphan-at state)) max-orphans)
      state
      ;; Oldest by ARRIVAL SEQUENCE, not by the clock. Timestamps here are whole
      ;; seconds, so a burst of orphans within one second is entirely tied, and
      ;; breaking that tie by id -- or worse, by map iteration order, which
      ;; differs between the JVM and a browser -- makes eviction arbitrary: a
      ;; legitimate header delivered child-first could evict its own parent one
      ;; message later. btcd has the same granularity and the same exposure; a
      ;; monotonic counter costs nothing and makes the policy actually FIFO.
      (let [oldest (first (sort-by (comp :seq val) (:orphan-at state)))]
        (cond-> state oldest (forget-orphan (key oldest)))))))

(defn process-header
  "The whole acceptance path -- `ProcessBlockHeader` / `maybeAcceptBlockHeader`.

  Returns {:state s :effects fx}. An orphan (parent unknown) is parked and its
  parent requested; btcd's equivalent lives one layer up, in `ProcessBlock`."
  [state header from]
  (if-not (well-formed? header)
    ;; Checked before anything hashes it; see `well-formed?`.
    (n/result (update-in state [:rejected :malformed] (fnil inc 0))
              [(n/log-effect :warn {:event :malformed-header :from from})])
    (let [header (select-keys header [:version :time :bits :nonce :prev :merkle-root])
          id (header-id header)]
      (cond
        (blk state id)
        (n/result state)

        (blk state (:prev header))
        (let [r (connect-one state header)]
          (if (= :accepted (:status r))
            (let [d (drain-orphans (:state r) id)]
              (n/result (:state d) (concat (:effects r) (:effects d))))
            (n/result (:state r) (:effects r))))

        ;; Unknown parent, and the CONTEXT-FREE checks fail: refuse outright.
        ;;
        ;; `check-header-sanity` was only reached inside `connect-one`, i.e.
        ;; only once the parent is known. So the orphan pool used to accept
        ;; headers on SHAPE alone: valid field types, a random `:prev`, and any
        ;; nonce at all. No hashing required.
        ;;
        ;; That is the cheapest input on an open network, and the pool evicts
        ;; FIFO at `max-orphans`, so a stream of free junk keeps it permanently
        ;; full and every legitimate out-of-order header is evicted within
        ;; milliseconds of arriving. Out-of-order header sync simply stops
        ;; working, and it costs the attacker nothing. Each junk header also
        ;; elicits a `:get-header` reply.
        ;;
        ;; btcd runs `checkBlockSanity` BEFORE the orphan path
        ;; (`blockchain/validate.go`), precisely so an orphan costs its sender
        ;; real work. Every check in `check-header-sanity` is CONTEXT-FREE --
        ;; it takes params and a clock, never the parent -- so a missing parent
        ;; is no reason to skip any of them.
        ;;
        ;; `target-valid?` matters as much as `pow-valid?` here, and this is
        ;; the limit of what can be done without the parent: `pow-valid?`
        ;; checks the hash against the difficulty the header CLAIMS, and the
        ;; sender chooses that. `target-valid?` is what stops them claiming an
        ;; arbitrarily easy one, so the floor is the params' pow limit rather
        ;; than the chain's real difficulty. Closing that gap needs a
        ;; work-threshold on the claimed chain, which is Bitcoin's
        ;; `GetAntiDoSWorkThreshold` and its presync commitment scheme, and is
        ;; not something one header can answer.
        (check-header-sanity (:params state) header (:now state))
        (n/result (update-in state [:rejected :orphan-insane] (fnil inc 0))
                  [(n/log-effect :warn {:event :orphan-failed-sanity
                                        :from from})])

        (contains? (:orphan-at state) id)
        (n/result state (when from [(n/send-to from {:kind :get-header :id (:prev header)})]))

        ;; Unknown parent, but the work is real: park it, and ask whoever sent
        ;; it for the parent.
        :else
        (let [state (reap-orphans state)]
          (n/result (-> state
                        (update-in [:orphans (:prev header)] (fnil conj #{}) header)
                        (assoc-in [:orphan-at id] {:seq (:orphan-seq state 0)
                                                   :at (:now state)})
                        (update :orphan-seq (fnil inc 0)))
                    (when from
                      [(n/send-to from {:kind :get-header :id (:prev header)})])))))))

;; ============================================================
;; Mining -- TEST ONLY
;; ============================================================

(defn template
  "The header a miner should try to solve on top of the current tip.

  A pure query, not an effect: the consensus engine does not mine, it only says
  what a valid next header would look like. `:time` is raised to one second past
  the median time past when the clock is behind it, which is what keeps a chain
  with a bad timestamp from stalling.

  `:on` names the block to build on, defaulting to the tip. A miner would never
  pass it, but building a competing branch from well back in a test is exactly
  the deep-reorg case, and it needs no privileged access to do it."
  [state {:keys [merkle-root time version on]}]
  (let [p (:params state)
        t (or on (:tip state))
        mtp (median-time-past p state t)]
    {:version (or version 1)
     :prev t
     :merkle-root (or merkle-root zero-hash)
     :time (max (or time (:now state)) (inc mtp))
     :bits (next-work-required p state t)
     :nonce 0}))

(defn mine
  "TEST-ONLY toy miner: try `max-tries` nonces from `start`.

  Deliberately bounded and deliberately not called from `step`. Never mine for
  real with this -- a JVM nonce loop is orders of magnitude off an ASIC, and
  worse in a browser. Tests configure an easy `:pow-limit-bits` so a solution
  costs a handful of hashes."
  ([header max-tries] (mine header 0 max-tries))
  ([header start max-tries]
   (loop [nonce start, tried 0]
     (cond
       (>= tried max-tries) nil
       (>= nonce 4294967296) nil
       :else (let [h (assoc header :nonce nonce)]
               (if (pow-valid? h)
                 h
                 (recur (inc nonce) (inc tried))))))))

;; ============================================================
;; The node
;; ============================================================

(defn- index-restored
  "Index one durable header, moving the tip if it now carries the most work."
  [st h]
  (let [id (header-id h)]
    (if (or (blk st id) (nil? (blk st (:prev h))))
      st
      (let [st (index-block st id h)]
        (if (bn/gt (:work-sum (blk st id)) (tip-work st))
          (assoc st :tip id)
          st)))))

(defn- restore
  "Rebuild the index from durable headers, in the order they were written.

  Headers in the index were validated when first accepted, so btcd does not
  re-check them on load and neither do we -- re-validating would need a `now`
  that a restarting node does not have. Replaying in write order keeps the
  first-seen tie-break deterministic.

  A `::snapshot` record stands in for every header write that preceded it; see
  `snapshot-record`. It is folded exactly like the individual writes it
  replaces, and then its `::tip` is adopted, because equal-work candidates are
  resolved by arrival order and a snapshot is not in arrival order."
  [state writes]
  (reduce (fn [st w]
            (let [ws (:writes w)]
              (if-let [snap (::snapshot ws)]
                (let [st (reduce index-restored st snap)
                      t  (::tip ws)]
                  ;; Only if we actually indexed it. A tip naming a header the
                  ;; snapshot does not contain would leave the node pointing at
                  ;; nothing, and every `tip-work` lookup after that reads nil.
                  (cond-> st (and t (blk st t)) (assoc :tip t)))
                (reduce index-restored st (filter :bits (vals ws))))))
          state
          writes))

(defn- anchor-clock
  "Advance `:now` to the tip's timestamp if the tip is ahead of it.

  `:now` defaults to the GENESIS timestamp and `restore` never touched it, so a
  restarted node came back with a clock reading from the beginning of the
  chain while its restored tip was thousands of blocks ahead. Every subsequent
  header then failed the two-hour future bound and was rejected as
  `:time-too-new` -- the node had rebuilt its chain perfectly and could not
  extend it. A freshly syncing node had the same problem from the other end: on
  mainnet parameters `:now` starts at 1231006505, so block 1 is already too far
  in the future.

  btcd never derives its clock from a header: `CheckBlockHeaderSanity` takes
  the bound from `timeSource.AdjustedTime()` (`validate.go:495-521`), which is
  wall time plus a peer-median offset clamped to +/-70 minutes
  (`mediantime.go:93-100`), and it survives a restart because it was never in
  the chain to begin with.

  The simulator has no wall clock -- `:now` is advanced by a timer, which is what makes
  runs replayable -- so the honest fix within the model is to take the maximum
  of the configured clock and what the chain itself proves has already
  happened. A header we have accepted is evidence that its timestamp is in the
  past.

  Every existing test hid this by passing `:now 2000000000`, a constant far in
  the future, including the restart test."
  [state]
  (let [tip-time (get-in (blk state (:tip state)) [:header :time])]
    (cond-> state
      (and tip-time (> tip-time (:now state))) (assoc :now tip-time))))

(defrecord Nakamoto []
  n/Node

  (capabilities [_]
    ;; THE revocable one. Of the seven algorithms here this is the only `:revert`,
    ;; and a consumer that integrates it needs code for a decision being taken
    ;; back -- against datahike that is `force-branch!`, a pointer move on a
    ;; copy-on-write commit DAG rather than an undo log.
    ;;
    ;; `:resync` too, for the restart announcement, which is a different thing
    ;; and used to be spelled as a revert.
    {:emits #{:broadcast :send :persist-then :set-timer
              :commit :revert :resync :log}
     :topics #{:headers}})

  (init [_ config]
    (let [p (params (:params config))
          genesis (:genesis config)
          _ (when-not genesis
              (throw (ex-info "nakamoto needs a :genesis header in config" {})))
          gid (header-id genesis)
          base {:peer-id (:peer-id config)
                ;; No `:peers`. It was written here and read nowhere: gossip
                ;; fans out through `n/broadcast`, which the interpreter routes,
                ;; and Nakamoto has no validator set to consult -- eligibility is
                ;; `hash <= target`, a property of the vertex rather than of its
                ;; author. A field written and never read is a claim the code
                ;; does not make.
                :params p
                :genesis gid
                :blocks {gid {:id gid
                              :header genesis
                              :parent nil
                              :height 0
                              :work-sum (calc-work (:bits genesis))}}
                :tip gid
                :orphans {}
                :orphan-at {}
                :orphan-seq 0
                :rejected {}
                ;; Wall-clock seconds, advanced by a logical timer. The core
                ;; defines a `tick` event for exactly this and the simulator
                ;; never delivers one, so a repeating timer is the only clock
                ;; available to a node.
                :now (or (:unix-time config) (:now config) (:time genesis))
                :seconds-per-tick (or (:seconds-per-tick config) 60)
                :clock-ticks (or (:clock-ticks config) 1)
                :announce-ticks (or (:announce-ticks config) 3)
                :snapshot-interval (or (:snapshot-interval config)
                                       default-snapshot-interval)
                :headers-since-snapshot 0}
          restored (:writes (:restored config))
          state (if (seq restored)
                  (cond-> (restore base restored)
                    (nil? (:unix-time config)) anchor-clock)
                  base)
          chain (path-from state (:genesis state) (:tip state))]
      (n/result state
                (concat [(n/set-timer :clock (:clock-ticks state))
                         (n/set-timer :announce (:announce-ticks state))]
                        ;; `resync`, not a revert. On restart we do not know
                        ;; what the interpreter still holds, so we announce our
                        ;; whole prefix rather than revoking a decision -- and
                        ;; NOTHING is being revoked here, which is the point.
                        ;;
                        ;; This was `(revert genesis [])` plus a commit, leaning
                        ;; on an empty `dropped` meaning "truncate to whatever
                        ;; you hold". That reading is what forced `dropped` to be
                        ;; optional, and with it optional the check that makes a
                        ;; real revert safe could always be skipped. Nakamoto is
                        ;; the algorithm that genuinely revokes, so it is the one
                        ;; that most needs the two kept apart.
                        (when (or (contains? config :restored) (seq chain))
                          [(n/resync chain)])))))

  (step [_ state input]
    (case (:type input)

      :vertex-received
      (process-header state (:vertex input) nil)

      :message-received
      (let [{:keys [kind header id]} (:msg input)]
        (case kind
          :header (process-header state header (:from input))
          ;; A peer is missing a header we have; send it back.
          :get-header
          (if-let [b (blk state id)]
            (n/result state [(n/send-to (:from input)
                                        {:kind :header :header (:header b)})])
            (n/result state))
          (n/result state)))

      :timer-fired
      (case (:timer-id input)
        :clock
        (n/result (if-some [now (:unix-time input)]
                    (assoc state :now now)
                    (update state :now + (* (:clock-ticks state) (:seconds-per-tick state))))
                  [(n/set-timer :clock (:clock-ticks state))])

        ;; Re-announce the tip periodically.
        ;;
        ;; Relaying on acceptance alone is not enough, and the simulator proved
        ;; it: two halves of a partition each broadcast their branch into a
        ;; black hole, and after healing NEITHER re-announced, so a network that
        ;; had already forked never reconverged. Bitcoin has the same problem
        ;; and solves it with an inv/getheaders handshake on connect; the same
        ;; effect is had here by re-broadcasting the tip, since a peer that does
        ;; not know it parks it and walks backwards to the fork point one
        ;; `get-header` at a time.
        :announce
        (n/result state
                  [(n/broadcast :headers
                                {:kind :header
                                 :header (:header (blk state (:tip state)))})
                   (n/set-timer :announce (:announce-ticks state))])

        (n/result state))

      ;; A `persisted` completion needs no action: nothing was gated behind it.
      :persisted (n/result state)

      ;; The core protocol defines this event; the simulator never delivers one,
      ;; so it is reachable only from a runtime that does. `(:n input 1)` rather
      ;; than `(:n input)` because a nil there would NPE inside a pure state
      ;; machine, which is the one thing the machine must not do -- and being
      ;; unreachable today is not a reason to leave a crash in it.
      :tick (n/result (update state :now + (* (:n input 1) (:seconds-per-tick state))))

      (n/result state))))

(defn create
  "Create a Nakamoto node. Config: {:genesis header :params {...}
  :seconds-per-tick n :clock-ticks n}."
  []
  (->Nakamoto))
