(ns urd.consensus.algorithms.bullshark
  "Narwhal + Bullshark: a certified DAG mempool with a zero-message ordering
  layer, on urd's core protocol.

  Ported from MystenLabs/narwhal at `e67f915` (read Aug 2026). The repo was
  archived in 2022 when the work moved into sui, so where the code and the
  papers disagree the papers win -- Narwhal/Tusk arXiv:2105.11827, Bullshark
  arXiv:2201.05677, and the partially synchronous variant at
  sonnino.com/papers/bullshark-simple.pdf. One such disagreement is load-bearing
  and is documented at `order-anchors` below.

  This is the PARTIALLY SYNCHRONOUS Bullshark (2 rounds per wave), not Tusk.
  The distinction is the reason it is in the portfolio: Tusk needs a threshold
  common coin, and Bullshark-PS does not, so this algorithm adds **no new
  cryptography at all**. Where Narwhal aggregates BLS12-381 signatures into one
  certificate signature plus a roaring bitmap of committee indices, we carry the
  set of signer ids and the Ed25519 signatures `geheimnis` already has -- 2f+1 x
  64 bytes on the wire rather than 96 plus a bitmap. That is the entire cost of
  the substitution; the state machine's predicate is unchanged, because what it
  checks is that the SET of signers is decisive, never the bytes.

  ## Two layers, and only one of them talks

  1. **Narwhal** builds a certified DAG. A vertex is a CERTIFICATE: a header
     (author, round, payload, parents) plus signatures from >= 2f+1 stake. The
     2f+1 is what makes the DAG safe rather than merely shaped like a DAG. At
     most one certificate per (author, round) can be certified, so equivocation
     cannot survive certification; and >= f+1 signers are honest, so the payload
     is retrievable. A round r+1 header must name >= 2f+1 stake of certificates
     from EXACTLY round r as parents (`primary/src/core.rs:229-245` -- note this
     check is in the Core, not in `Header::verify`, and it is the invariant the
     whole ordering layer silently assumes).

  2. **Bullshark** orders it. `commit-sequence` is a pure function of the DAG
     and emits NOTHING. Every honest node runs it on its own copy and gets the
     identical total order. This is the first algorithm in urd's portfolio whose
     decision layer sends no messages, and the first that commits a multi-vertex
     sequence retroactively.

  ## The ordering rule, exactly

  - Anchors exist only at EVEN rounds (`bullshark.rs:49-52`). The anchor of
    round r is `anchor-fn(r, validators, stake)` -- a deterministic function of
    the round alone, evaluated identically by everyone.
  - **Commit rule**: sum the stake of round-(r+1) certificates whose parents
    include the anchor; commit iff `>= f+1` (`bullshark.rs:66-82`). Only f+1 is
    needed, and that is the elegant part: the 2f+1 intersection argument was
    already discharged at DAG-construction time, so the ordering layer gets to
    be cheap.
  - **Retroactive back-fill** (`utils.rs:11-40`): from the newly committed
    anchor, walk backwards by 2 to the last committed round, including each
    earlier anchor iff it is REACHABLE from the newer one. One certificate can
    therefore commit an anchor plus several earlier anchors and all of their
    sub-DAGs at once.
  - **Deterministic flatten** (`utils.rs:58-100`): pre-order DFS from each
    anchor over parents, skipping vertices already queued or already committed
    for that author, then a STABLE sort by round. That final stable sort is what
    makes arrival order irrelevant, and it is the only reason two nodes that
    learned the same certificates in different orders agree.
  - GC drops rounds more than `gc-depth` below the last committed round, and
    each author's certificates below its own last committed round.

  ## Three mechanisms stop the DFS, and all three are needed

  1. `already-queued` dedups within one flatten;
  2. `last-committed[author] == cert-round` -- STRICT equality, not `>=`;
  3. the GC in `record-committed`, which removes everything strictly below that
     frontier so the equality test is sufficient.

  The bootstrap case falls out of (2): `last-committed` starts at 0 for EVERY
  validator, and genesis certificates are at round 0, so the DFS stops there and
  genesis is never emitted. Miss that seeding and the very first commit contains
  n phantom vertices -- and, worse, agrees with itself across nodes, so nothing
  catches it.

  ## Portability: why digests are strings

  The DFS pushes parents in sorted digest order and the stable sort by round
  preserves DFS discovery order WITHIN a round, so the digest comparator decides
  the total order. `hasch/uuid` gives content-addressed identity on both
  platforms, but a raw UUID must never be compared: the JVM's `UUID/compareTo`
  compares the two 64-bit halves as SIGNED longs, while ClojureScript's `UUID`
  compares the printed string. Those orders differ for any pair whose high bit
  differs -- half of all pairs -- so a JVM node and a browser node would produce
  different total orders from the identical DAG, silently. Digests are therefore
  STRINGS everywhere. Pinned in `portability-test`.

  ## Payload

  Opaque to consensus, and supplied through `request-value`. The intended
  payload is the map of snapshot ids datahike already hands to
  `coordinated-commit!`; Narwhal's own is `{batch-digest -> worker-id}`, which
  is the same shape. See the PR for why the certificate DAG is a urd-owned
  structure rather than a yggdrasil one."
  (:require [urd.consensus.node :as n]
            [urd.consensus.rng :as rng]
            [hasch.core :as hasch]))

;; ============================================================
;; Thresholds  (config/src/lib.rs:548-561)
;;
;; Both are over total STAKE, not over validator count. With uniform stake
;; `quorum-threshold` coincides with `node/byzantine-threshold` and
;; `validity-threshold` with f+1; with non-uniform stake neither identity
;; holds, which is exactly why `node/threshold-membership` cannot be used here.
;; ============================================================

(defn quorum-threshold
  "2f+1: `2 * total / 3 + 1`, integer division."
  [total]
  (inc (quot (* 2 total) 3)))

(defn validity-threshold
  "f+1: `(total + 2) / 3`, integer division -- i.e. ceil(total/3)."
  [total]
  (quot (+ total 2) 3))

;; ============================================================
;; Identity
;;
;; Content-addressed via hasch, which aligns with yggdrasil and answers the
;; design doc's open question 1 for this algorithm: the digest is a function of
;; the header, so two nodes that build the same certificate name it identically
;; without coordinating.
;; ============================================================

(defn header-id
  "The digest of a header. Excludes the author's signature, as Narwhal's does."
  [{:keys [author round payload parents]}]
  (str (hasch/uuid {:author author :round round :payload payload
                    :parents (set parents)})))

(defn certificate-id
  "The digest of a certificate: (header-id, round, author).

  Narwhal hashes exactly those three and deliberately EXCLUDES the signature
  set (`types/src/primary.rs`, `impl Hash for Certificate`). The exclusion is
  not an optimisation. Two honest nodes may aggregate different 2f+1 subsets of
  the same votes; if the signer set were part of the identity those would be
  different vertices, the DAG would fork along an honest path, and parent
  lookups would fail. Its `PartialEq` agrees, comparing only those fields."
  [{:keys [header]}]
  (str (hasch/uuid {:header-id (header-id header)
                    :round (:round header)
                    :author (:author header)})))

(defn certificate
  "Build a certificate value with its digest attached."
  [header signers]
  (let [c {:header header :signers (set signers)}]
    (assoc c :id (certificate-id c))))

(defn genesis-certificates
  "One empty round-0 certificate per validator (`Certificate::genesis`).

  Uncertified, and correctly so: every node derives the same set from the
  committee, so there is nothing to agree about. (Narwhal leaves their
  `header.id` as 32 zero bytes and then short-circuits `Certificate::verify` on
  genesis membership, which means any round-0 certificate with a zeroed header
  id from a committee member verifies unconditionally. We give them real
  digests instead.)"
  [validators]
  (into {}
        (map (fn [a]
               [a (certificate {:author a :round 0 :payload nil :parents #{}}
                               #{})]))
        validators))

;; ============================================================
;; Anchor selection: a pure function of (round, validators, stake)
;;
;; Narwhal's `Committee::leader(seed)` is a stake-weighted choice seeded by the
;; round, drawn with `rand`'s ChaCha12 `StdRng` and `WeightedIndex<f32>`. Bit
;; compatibility with that would mean porting ChaCha12, so we draw from urd's
;; own portable PRNG instead -- same shape, same determinism, different stream.
;; A Rust interop deployment would have to agree here; nothing else in the
;; algorithm depends on the choice.
;;
;; The 2022 repo's own tests are worth ignoring: `#[cfg(test)]` swaps the leader
;; function for one that returns the SAME authority at every round, so the whole
;; suite exercises a degenerate fixed schedule.
;; ============================================================

(defn round-robin-anchor
  "The round-th validator in sorted order. Stake-blind; useful in tests."
  [round validators _stake]
  (nth validators (mod round (count validators))))

(defn stake-weighted-anchor
  "Draw an anchor proportional to stake, deterministically in the round.

  A seeded draw rather than `round mod n`, so a validator with three times the
  stake anchors three times as often. The PRNG is urd's portable one, whose
  sequences are pinned identical on both platforms -- an anchor rule that
  disagreed between a browser and the JVM would split the network on the total
  order without a single message being lost."
  [round validators stake]
  (let [total (reduce + 0 (map #(get stake % 1) validators))
        [x _] (rng/next-int (rng/make round) (max 1 total))]
    (loop [[v & more] validators, acc 0]
      (let [acc' (+ acc (get stake v 1))]
        (if (or (nil? more) (< x acc'))
          v
          (recur more acc'))))))

;; ============================================================
;; The consensus state -- a GRAPH, not a vote tally
;;
;;   {:dag                  {round {author certificate}}
;;    :last-committed       {author round}
;;    :last-committed-round n
;;    :gc-depth             d}
;;
;; That is the whole of `ConsensusState` (`consensus/src/consensus.rs:27-40`).
;; There is no per-round tally anywhere, because there are no votes at this
;; layer. It is held inline in the node state rather than under a key, so the
;; ordering functions can be called on a node state directly.
;; ============================================================

(defn- cert-round [c] (:round (:header c)))
(defn- cert-author [c] (:author (:header c)))
(defn- cert-parents [c] (:parents (:header c)))

(defn- cert-at
  "The certificate with digest `d` at round `r`, or nil.

  A linear scan over one round's authors, as Narwhal does. A digest index would
  be faster and would be one more thing that can silently disagree with the DAG
  after a GC pass."
  [dag r d]
  (some (fn [c] (when (= (:id c) d) c)) (vals (get dag r))))

(defn- linked?
  "Is there a path from `anchor` back through the DAG to `prev`?

  `utils::linked`. A level-by-level backward frontier rather than a general
  reachability search, which is correct only because every certificate names
  parents from exactly the previous round.

  Narwhal writes `.expect(\"We should have the whole history by now\")` on each
  round lookup here, which panics outright if a round was garbage collected out
  from under it. A missing round means `not reachable`, so we return false."
  [dag anchor prev]
  (let [target (:id prev)
        pr (cert-round prev)]
    (loop [frontier [anchor], r (dec (cert-round anchor))]
      (if (< r pr)
        false
        (let [digests (into #{} (mapcat cert-parents) frontier)
              nxt (filterv #(contains? digests (:id %)) (vals (get dag r)))]
          (if (= r pr)
            (boolean (some #(= (:id %) target) nxt))
            (recur nxt (dec r))))))))

(defn- order-anchors
  "The anchors to commit, NEWEST FIRST (`utils::order_leaders`).

  Walks back by 2 from the newly committed anchor down to the last committed
  round, keeping each earlier anchor reachable from the one after it. An
  unreachable anchor is skipped permanently -- nobody committed it, because a
  reachable path is exactly what the f+1 support rule guarantees for anything
  that was.

  ## The reference implementation walks the wrong rounds

  `utils.rs:22-25` is `(last_committed_round + 2 .. leader.round()).rev()
  .step_by(2)`. In Rust that builds the DESCENDING sequence first and steps it
  afterwards, so it yields `leader.round()-1, leader.round()-3, ...` -- ODD
  rounds, where by construction there is never an anchor. It has read that way
  since the original Bullshark commit, inherited from the Facebook Tusk code.
  The test suite cannot see it because `#[cfg(test)]` makes the leader function
  return the same authority at every round, so the odd-round certificate it
  picks up is an ancestor of the even anchor anyway and its sub-DAG is a subset.

  The published algorithm walks even rounds, and so do we:
  `leader.round()-2, -4, ..., >= last_committed_round + 2`. This is the one
  place the port deliberately diverges from the code it was ported from, and it
  is why the papers were named as the authority up front."
  [state anchor anchor-fn]
  (let [lcr (:last-committed-round state)]
    (loop [acc [anchor], cur anchor, r (- (cert-round anchor) 2)]
      (if (< r (+ lcr 2))
        acc
        (let [prev (anchor-fn state r)]
          (if (and prev (linked? (:dag state) cur prev))
            (recur (conj acc prev) prev (- r 2))
            (recur acc cur (- r 2))))))))

(defn- order-sub-dag
  "Flatten one anchor's causal history into a deterministic sequence.

  `utils::order_dag`, reproduced detail for detail, because every detail is
  load-bearing for the central claim:

  - a LIFO buffer, so the walk is a pre-order DFS;
  - parents visited in sorted digest order, so the DFS is deterministic;
  - a vertex is skipped if already queued here, or if this author's last
    committed round EQUALS that round (strict equality; the GC handles below);
  - a parent missing from the DAG is skipped, not an error -- it was already
    committed and pruned, or garbage collected;
  - vertices more than `gc-depth` below the last committed round are dropped;
  - and finally a STABLE sort by round, which leaves DFS order intact within a
    round.

  A non-stable sort would still produce a valid causal order, would still look
  right in every single-node test, and would make two nodes disagree whenever
  their DFS tie-break differed. Both platforms' `sort-by` is stable (TimSort on
  the JVM, `goog.array/stableSort` in ClojureScript)."
  [state anchor]
  (let [{:keys [dag gc-depth last-committed last-committed-round]} state]
    (loop [stack [anchor], queued #{}, ordered []]
      (if (empty? stack)
        (->> ordered
             (filterv #(>= (+ (cert-round %) gc-depth) last-committed-round))
             (sort-by cert-round)
             vec)
        (let [x (peek stack)
              stack (pop stack)
              pr (dec (cert-round x))
              [stack queued]
              (reduce (fn [[st q] d]
                        (if-let [c (cert-at dag pr d)]
                          (if (or (contains? q d)
                                  (= (get last-committed (cert-author c))
                                     (cert-round c)))
                            [st q]
                            [(conj st c) (conj q d)])
                          [st q]))
                      [stack queued]
                      ;; Strings, sorted as strings. See the namespace note.
                      (sort (cert-parents x)))]
          (recur stack queued (conj ordered x)))))))

(defn- record-committed
  "Fold one committed certificate into the state and garbage-collect.

  `ConsensusState::update`. Two things happen and both matter: this author's
  watermark rises, which is what stops the next anchor's DFS from re-ordering
  it, and rounds more than `gc-depth` behind are dropped entirely.

  Called per certificate, INTERLEAVED with emission, so the next anchor's
  flatten sees a state that already reflects this one. An implementation that
  computed every sub-DAG first and updated afterwards would emit duplicates."
  [state c]
  (let [a (cert-author c)
        r (cert-round c)
        lc (update (:last-committed state) a (fnil max 0) r)
        lcr (reduce max 0 (vals lc))
        gc (:gc-depth state)
        dag (reduce-kv
             (fn [acc round authors]
               (if (< (+ round gc) lcr)
                 acc
                 (let [authors' (reduce-kv (fn [m author cert]
                                             (if (< round (get lc author 0))
                                               m
                                               (assoc m author cert)))
                                           {} authors)]
                   (if (seq authors') (assoc acc round authors') acc))))
             {}
             (:dag state))]
    (assoc state :last-committed lc :last-committed-round lcr :dag dag)))

(defn anchor-for
  "The anchor certificate at `round`, or nil if we do not hold it."
  [state round]
  (let [a ((:anchor-fn state) round (:validators state) (:stake state))]
    (get-in state [:dag round a])))

(defn commit-sequence
  "THE ordering layer. Pure, total, and it sends nothing.

  Given a state and the round of a certificate just inserted, returns
  `[state' sequence]`. `sequence` is the ordered certificates to commit --
  usually empty, occasionally one anchor's sub-DAG, and after a gap potentially
  several anchors' sub-DAGs at once.

  The anchor considered is at `inserted-round - 1`, so support is counted among
  certificates of `inserted-round` itself -- the ones provably already present."
  [state inserted-round anchor-fn]
  (let [r (dec inserted-round)]
    (if (or (odd? r) (< r 2) (<= r (:last-committed-round state)))
      [state []]
      (if-let [anchor (anchor-fn state r)]
        (let [support (->> (vals (get-in state [:dag (inc r)]))
                           (filter #(contains? (cert-parents %) (:id anchor)))
                           (map #(get (:stake state) (cert-author %) 0))
                           (reduce + 0))]
          (if (< support (validity-threshold (:total-stake state)))
            [state []]
            (reduce (fn [[st acc] a]
                      (let [sub (order-sub-dag st a)]
                        [(reduce record-committed st sub) (into acc sub)]))
                    [state []]
                    ;; Oldest anchor first.
                    (reverse (order-anchors state anchor anchor-fn)))))
        [state []]))))

;; ============================================================
;; The committed vertex
;;
;; Derived only from the header, never from the signer set: two honest nodes
;; may certify one header with different 2f+1 subsets of the votes, and a
;; consumer comparing committed prefixes must not read that as disagreement.
;; ============================================================

(defn vertex [c]
  {:id (:id c) :author (cert-author c) :round (cert-round c)
   :payload (:payload (:header c))})

;; ============================================================
;; DAG construction (Narwhal)
;;
;; ## The certificate store is NOT the consensus DAG, and this is not a detail
;;
;; `record-committed` prunes each author's certificates below its own last
;; committed round, so a healthy node's `:dag` retains almost nothing old. Serve
;; a peer's catch-up request out of it and a node that fell behind can never
;; catch up: it asks for round 10, and every node that could answer has already
;; dropped round 10 from the structure the ordering layer walks. This port did
;; exactly that at first, and it looked fine -- three of four nodes agreed
;; perfectly and the fourth sat at round 3 forever, which reads as a partition
;; that did not heal rather than as a bug.
;;
;; Narwhal keeps the two apart for this reason: `ConsensusState.dag` is the
;; lossy working set and `CertificateStore` is the durable archive, and the
;; Synchronizer answers from the store. `:certificates` here is that store; it
;; also holds the genesis certificates, which the consensus GC removes as soon
;; as anything commits and which round-1 parent resolution still needs.
;; ============================================================

(defn- stored [state d] (get (:certificates state) d))

(defn- quorum-of-parents?
  "Do these parents name >= 2f+1 stake of DISTINCT authors at round r-1?

  `primary/src/core.rs:229-245`. Counting digests instead of distinct authors
  would let one author be named twice; counting authors instead of stake would
  be wrong under non-uniform stake. This is the check that makes the DAG safe,
  and Narwhal keeps it OUT of `Header::verify` -- a header that passes signature
  verification can still be structurally invalid."
  [state round parents]
  (or (zero? round)
      (let [authors (into #{} (keep (fn [d]
                                      (let [c (stored state d)]
                                        (when (= (dec round) (cert-round c))
                                          (cert-author c)))))
                          parents)]
        (>= (reduce + 0 (map #(get (:stake state) % 0) authors))
            (quorum-threshold (:total-stake state))))))

(defn- have-all-parents? [state round parents]
  (or (zero? round)
      (every? #(some? (stored state %)) parents)))

(defn- certified?
  "Do the signers carry >= 2f+1 stake?

  The signature BYTES were checked at the edge and arrive as `:verified-by`;
  what the state machine checks is that the SET of signers is decisive. This is
  the whole of the BLS-aggregate-to-Ed25519-bitmap substitution: same
  predicate, more bytes on the wire, no new cryptography."
  [state c]
  (or (zero? (cert-round c))
      (>= (reduce + 0 (map #(get (:stake state) % 0) (:signers c)))
          (quorum-threshold (:total-stake state)))))

(defn well-formed?
  "The checks that need nothing but the certificate itself and the committee.

  Separated from `quorum-of-parents?` deliberately. That check resolves parent
  digests in OUR dag, so it answers `no` both for a malformed certificate and
  for a perfectly good one whose history has not arrived yet. Running the two
  together -- which is what the first version of this port did -- turns every
  out-of-order arrival into a permanent rejection, and the algorithm still
  looks like it works, because gossip eventually redelivers everything in an
  order that happens to succeed."
  [state c]
  (and (map? (:header c))
       (int? (cert-round c))
       (not (neg? (cert-round c)))
       (contains? (:stake state) (cert-author c))
       (= (:id c) (certificate-id c))
       (certified? state c)))

(defn valid-certificate?
  "Well formed AND structurally valid against a dag that holds its parents."
  [state c]
  (and (well-formed? state c)
       (quorum-of-parents? state (cert-round c) (cert-parents c))))

(defn- known?
  "Have we ever accepted this certificate? Asked of the STORE, not the DAG.

  Asking the DAG would say `no` again for anything the consensus GC pruned, and
  the certificate would be re-inserted into a round the ordering layer has
  already passed."
  [state c]
  (some? (stored state (:id c))))

(defn- conflicting
  "A certificate we already hold for this (author, round) with another digest.

  Narwhal's DAG is `HashMap<Round, HashMap<Author, Certificate>>`, so a second
  certificate for one slot silently OVERWRITES the first. It cannot happen with
  honest signers -- 2f+1 signers per certificate and one vote per author per
  round make two certified headers for one slot impossible without f+1 honest
  double-voters -- but `cannot happen` and `is not checked` are different
  claims, and the code only makes the second. Tracked in `:slots`, which
  survives the GC that empties the DAG."
  [state c]
  (let [prev (get-in state [:slots [(cert-author c) (cert-round c)]])]
    (when (and prev (not= prev (:id c))) (stored state prev))))

;; ============================================================
;; Node state
;; ============================================================

(defn- initial-consensus
  [{:keys [validators stake gc-depth anchor-fn]}]
  (let [genesis (genesis-certificates validators)]
    {:dag {0 genesis}
     ;; Seeded at 0 for EVERY validator. This is what stops the DFS at genesis;
     ;; see the namespace docstring.
     :last-committed (into {} (map (fn [v] [v 0])) validators)
     :last-committed-round 0
     ;; The archive. Unbounded here; a deployment bounds it the way Narwhal
     ;; does, by refusing certificates below the GC horizon and pruning behind
     ;; them. Genesis lives here as well as in the DAG, because the consensus GC
     ;; empties round 0 as soon as anything commits while round-1 parent
     ;; resolution still needs it.
     :certificates (into {} (map (fn [[_ c]] [(:id c) c])) genesis)
     :slots (into {} (map (fn [[a c]] [[a 0] (:id c)])) genesis)
     :gc-depth gc-depth
     :stake stake
     :total-stake (reduce + 0 (vals stake))
     :validators validators
     :anchor-fn anchor-fn}))

(defn- round-parents
  "The certificates to name as parents of a header at `round`.

  Everything we hold at round-1, not just the first 2f+1. Narwhal's
  `CertificatesAggregator` deliberately does not reset once the quorum is
  reached, precisely so that extra parents keep reaching the proposer -- a
  comment there says it is required when running Bullshark, and it is: a parent
  set that stopped at 2f+1 could systematically exclude the anchor."
  [state round]
  (into #{} (map :id) (vals (get-in state [:dag (dec round)]))))

(defn- have-quorum-at?
  "Do we hold >= 2f+1 stake of certificates at `round`?"
  [state round]
  (>= (reduce + 0 (map #(get (:stake state) % 0)
                       (keys (get-in state [:dag round]))))
      (quorum-threshold (:total-stake state))))

;; ============================================================
;; Ordering, driven
;; ============================================================

(defn- deliver-commits
  "Run the ordering layer and turn its output into a `:commit` effect.

  Returns no effect at all most of the time and, when it does, exactly one
  `:commit` and nothing else. There is no message to accompany it: every other
  node computes the same sequence from the same DAG."
  [state inserted-round]
  (let [[state' seq'] (commit-sequence state inserted-round anchor-for)]
    (if (empty? seq')
      (n/result state)
      (let [idx (:commit-index state)
            vs (mapv vertex seq')]
        (n/result (assoc state' :commit-index (+ idx (count vs)))
                  ;; `:index` is the POSITION of the first vertex in the
                  ;; committed prefix. Bullshark never reverts, so here the
                  ;; position and a running count coincide -- but the position
                  ;; is what is meant.
                  [(n/commit vs idx)])))))

;; ============================================================
;; Round advancement, and Bullshark's partial-synchrony pacing
;; ============================================================

(declare propose-header)

(defn- advance-round
  "Move to round r+1 once we hold 2f+1 stake of certificates at round r.

  With one addition that is the whole partial-synchrony part of Bullshark-PS:
  at an EVEN round we also wait for the anchor's own certificate before sealing
  our parent set, up to a timeout. Without it a node can reach 2f+1 parents
  from a subset that excludes the anchor, and if enough nodes do that the anchor
  never gathers f+1 support and the wave is wasted. The timeout is what keeps it
  a liveness heuristic rather than a safety dependency -- an anchor that never
  arrives is simply skipped, and a later anchor back-fills whatever was linked.

  Narwhal puts the same idea in `Proposer::ready`, whose partially-synchronous
  branch waits on `update_leader` / `enough_votes`. That code is stale (it looks
  for the current round's leader among the previous round's parents), so this is
  the paper's rule rather than the repo's."
  [state]
  (let [r (:round state)]
    (cond
      (not (have-quorum-at? state r))
      (n/result state)

      (and (even? r) (pos? r)
           (nil? (anchor-for state r))
           (not (:anchor-timeout state)))
      (if (:anchor-armed state)
        (n/result state)
        (n/result (assoc state :anchor-armed true)
                  [(n/set-timer :anchor (:anchor-wait-ticks state))]))

      :else
      (let [state (assoc state
                         :round (inc r)
                         :anchor-armed false
                         :anchor-timeout false)
            {state :state fx :effects} (propose-header state)]
        (n/result state (into [(n/cancel-timer :anchor)] fx))))))

(defn- propose-header
  "Ask the application for a payload for the current round."
  [state]
  (n/result state [(n/request-value {:round (:round state)})]))

;; ============================================================
;; Certificate insertion
;; ============================================================

(defn- missing-parents [state c]
  (vec (remove #(some? (stored state %)) (sort (cert-parents c)))))

(defn- missing-parent-requests
  "One `:want` per round we are short of, for everything currently parked.

  Grouped by round because that is how the responder indexes its DAG, and
  deduplicated because a node that fell far behind parks one certificate per
  author per round and would otherwise ask n times for the same round."
  [state]
  (->> (vals (:pending state))
       (reduce (fn [m c]
                 (update m (dec (cert-round c)) (fnil into #{}) (missing-parents state c)))
               {})
       (sort-by key)
       (mapv (fn [[r ds]]
               (n/broadcast :bullshark {:kind :want :from (:peer-id state)
                                        :round r :digests (vec (sort ds))})))))

(defn- insert-certificate
  "Add a certificate to the DAG, order what that makes orderable, advance.

  Certificates whose parents we do not hold are parked in `:pending` and
  retried, so the DAG is only ever extended CAUSALLY. That is what lets the
  ordering layer assume it has the whole history instead of checking -- Narwhal
  gets the same guarantee from its Synchronizer."
  [state c]
  (cond
    (not (well-formed? state c))
    (n/result (update-in state [:rejected :malformed] (fnil inc 0)))

    (known? state c)
    (n/result state)

    ;; Two certified headers for one slot. Unreachable with honest signers; if
    ;; it happens, f+1 honest validators double-voted or edge verification is
    ;; broken. Either way the DAG must not absorb it -- Narwhal's would, with a
    ;; `HashMap::insert` that overwrites and says nothing.
    (conflicting state c)
    (let [prev (conflicting state c)]
      (n/result (update-in state [:rejected :equivocation] (fnil inc 0))
                [(n/report-equivocation
                  (cert-author c)
                  {:kind :conflicting-certificates
                   :round (cert-round c)
                   :first (:id prev) :second (:id c)})]))

    (not (have-all-parents? state (cert-round c) (cert-parents c)))
    (n/result (assoc-in state [:pending (:id c)] c)
              [(n/broadcast :bullshark {:kind :want
                                        :from (:peer-id state)
                                        :round (dec (cert-round c))
                                        :digests (missing-parents state c)})])

    ;; Parents are all present, so this check now means what it says.
    (not (quorum-of-parents? state (cert-round c) (cert-parents c)))
    (n/result (update-in state [:rejected :thin-parents] (fnil inc 0)))

    :else
    (let [r (cert-round c)
          state (-> state
                    (assoc-in [:certificates (:id c)] c)
                    (assoc-in [:slots [(cert-author c) r]] (:id c))
                    (update :pending dissoc (:id c)))
          ;; Into the working DAG only if the ordering layer can still use it.
          ;; A certificate older than the GC horizon is archived and no more:
          ;; re-inserting it would put a vertex into a round the ordering layer
          ;; has already walked past.
          state (if (< (+ r (:gc-depth state)) (:last-committed-round state))
                  state
                  (assoc-in state [:dag r (cert-author c)] c))
          persisted (n/persist-then {:writes {[:cert (:id c)] c}
                                     :durable? true
                                     :token [:cert (:id c)]})
          {state :state fx1 :effects} (deliver-commits state r)
          {state :state fx2 :effects} (advance-round state)
          ready (->> (vals (:pending state))
                     (filterv #(have-all-parents? state (cert-round %) (cert-parents %)))
                     ;; Sorted so replay does not depend on map iteration order.
                     (sort-by (juxt cert-round :id)))]
      (reduce (fn [res p]
                (let [{s :state f :effects} (insert-certificate (:state res) p)]
                  (n/result s (into (:effects res) f))))
              (n/result state (into [persisted] (concat fx1 fx2)))
              ready))))

;; ============================================================
;; Header proposal and voting
;; ============================================================

(defn- vote-for
  "Vote for a header, unless we already voted for a different one this slot.

  `:voted` is the double-signing guard, and it is the ONLY thing in this
  algorithm that must survive a crash for safety -- everything else is rebuilt
  from the certificate store. Which makes it exactly CometBFT's rule stated for
  a different protocol: gate the things you sign, and nothing else."
  [state header from]
  (let [slot [(:author header) (:round header)]
        hid (header-id header)
        prev (get-in state [:voted slot])
        reply (n/send-to from {:kind :vote :from (:peer-id state)
                               :header-id hid :round (:round header)
                               :author (:author header)})]
    (cond
      ;; A retransmission. Re-answer: a lost vote otherwise stalls the author
      ;; forever, which is the failure Tendermint recorded under message loss.
      (= prev hid) (n/result state [reply])

      prev
      (n/result (update-in state [:rejected :equivocation] (fnil inc 0))
                [(n/report-equivocation
                  (:author header)
                  {:kind :conflicting-headers :round (:round header)
                   :first prev :second hid})])

      :else
      (n/result (assoc-in state [:voted slot] hid)
                [(n/persist-then {:writes {[:voted slot] hid}
                                  :durable? true
                                  :token [:voted slot]
                                  :then [reply]})]))))

(defn- receive-header
  [state header from]
  (cond
    (not= (:author header) from)
    (n/result (update-in state [:rejected :forged-author] (fnil inc 0)))

    (not (and (int? (:round header)) (pos? (:round header))))
    (n/result (update-in state [:rejected :bad-round] (fnil inc 0)))

    (not (have-all-parents? state (:round header) (:parents header)))
    ;; We must not vote for a header whose history we do not hold: signing it
    ;; asserts an availability we cannot provide.
    (n/result state [(n/broadcast :bullshark
                                  {:kind :want :from (:peer-id state)
                                   :round (dec (:round header))
                                   :digests (vec (sort (:parents header)))})])

    (not (quorum-of-parents? state (:round header) (:parents header)))
    (n/result (update-in state [:rejected :thin-parents] (fnil inc 0)))

    :else
    (vote-for state header from)))

(defn- receive-vote
  "Collect a vote for one of our headers; certify at 2f+1 stake.

  Votes are kept per ROUND rather than for a single in-flight header. A node
  that has already advanced can still certify the header it left behind, which
  matters because a node whose own certificate never forms contributes nothing
  to the DAG for that round."
  [state {:keys [header-id round from]}]
  (let [own (get-in state [:own-headers round])]
    (if (or (nil? own)
            (not= header-id (:id own))
            (contains? (:certified state) round))
      (n/result state)
      (let [votes (conj (get-in state [:votes round] #{}) from)
            state (assoc-in state [:votes round] votes)]
        (if (< (reduce + 0 (map #(get (:stake state) % 0) votes))
               (quorum-threshold (:total-stake state)))
          (n/result state)
          (let [c (certificate (:header own) votes)
                state (-> state
                          (update :certified conj round)
                          ;; Remembered so the gossip timer re-announces THIS,
                          ;; not whatever happens to sit one round below our
                          ;; current one. See the note there.
                          (assoc :own-latest (:id c)))
                {state :state fx :effects} (insert-certificate state c)]
            (n/result state
                      (into [(n/broadcast :bullshark {:kind :certificate :cert c
                                                      :from (:peer-id state)})]
                            fx))))))))

;; ============================================================
;; Recovery
;;
;; Narwhal rebuilds from a CERTIFICATE STORE, never by replaying events, and
;; that is the point of the ordering layer being pure: the total order is a
;; function of the DAG, so a restarted node RE-DERIVES it rather than
;; remembering it. There is nothing to replay and nothing to reconcile.
;;
;; We go one step further than Narwhal, which also persists its `last_committed`
;; map and resumes from it. Since ordering is pure, persisting the certificates
;; alone is sufficient -- with one caveat that is honest rather than fatal: GC
;; means the store may hold certificates the live node had already pruned, so
;; re-derivation reproduces the committed prefix exactly only while `gc-depth`
;; exceeds the run. Beyond that a real deployment must persist the watermark
;; too, exactly as Narwhal does.
;; ============================================================

(defn- restore-dag
  "Re-insert stored certificates into a fresh state, causally.

  Writes land in issue order, which is already causal, but a crash can leave a
  certificate whose parents never landed -- so we sweep to a fixpoint rather
  than trusting the order."
  [state certs]
  (loop [st state, remaining certs]
    (let [ready (filterv #(and (not (known? st %))
                               (have-all-parents? st (cert-round %) (cert-parents %))
                               (valid-certificate? st %))
                         remaining)]
      (if (empty? ready)
        st
        (recur (reduce (fn [s c]
                         (-> s
                             (assoc-in [:dag (cert-round c) (cert-author c)] c)
                             (assoc-in [:certificates (:id c)] c)
                             (assoc-in [:slots [(cert-author c) (cert-round c)]] (:id c))))
                       st
                       (sort-by (juxt cert-round :id) ready))
               (vec (remove (fn [c] (some #(= (:id %) (:id c)) ready)) remaining)))))))

(defn replay-order
  "Re-derive the whole committed sequence from a restored DAG.

  Runs `commit-sequence` over every round in ascending order, exactly as a live
  node would have. Because the ordering layer is pure this reproduces what the
  node emitted before it crashed: a re-derivation, not a log replay."
  [state]
  (reduce (fn [[st acc] r]
            (let [[st' s] (commit-sequence st r anchor-for)]
              [st' (into acc s)]))
          [state []]
          (sort (keys (:dag state)))))

;; ============================================================
;; The node
;; ============================================================

(defrecord Bullshark []
  n/Node

  (init [_ config]
    (let [validators (vec (sort (:validators config)))
          stake (or (:stake config) (into {} (map (fn [v] [v 1])) validators))
          base (merge (initial-consensus
                       {:validators validators
                        :stake stake
                        :gc-depth (or (:gc-depth config) 50)
                        :anchor-fn (or (:anchor-fn config) stake-weighted-anchor)})
                      {:peer-id (:peer-id config)
                       :round 1
                       :voted {}
                       :pending {}
                       :own-headers {}
                       :votes {}
                       :certified #{}
                       :commit-index 0
                       :rejected {}
                       :anchor-armed false
                       :anchor-timeout false
                       :anchor-wait-ticks (or (:anchor-wait-ticks config) 4)
                       :gossip-ticks (or (:gossip-ticks config) 5)})
          restored (->> (get-in config [:restored :writes])
                        (mapcat :writes)
                        (reduce (fn [m [k v]] (assoc m k v)) {}))
          certs (into [] (comp (filter (fn [[k _]] (= :cert (first k)))) (map val))
                      restored)
          voted (into {} (comp (filter (fn [[k _]] (= :voted (first k))))
                               (map (fn [[k v]] [(second k) v])))
                      restored)
          ;; Our own proposals, so a restarted node can re-send what it signed
          ;; instead of signing something else. See the `:value-ready` branch.
          proposed (into {} (comp (filter (fn [[k _]] (= :proposed (first k))))
                                  (map (fn [[k h]] [(second k) {:header h :id (header-id h)}])))
                         restored)
          state (assoc base :voted voted :own-headers proposed
                       ;; Our own signature counts toward certifying our own
                       ;; header, on this side of the crash as on the other.
                       :votes (into {} (map (fn [[r _]] [r #{(:peer-id config)}])) proposed))]
      (if (empty? certs)
        (n/result state [(n/set-timer :gossip (:gossip-ticks state))
                         (n/request-value {:round 1})])
        (let [restored-state (restore-dag state certs)
              [state' sequence] (replay-order restored-state)
              highest (reduce max 0 (keys (:dag state')))
              round (loop [r highest]
                      (cond (zero? r) 1
                            (have-quorum-at? state' r) (inc r)
                            :else (recur (dec r))))
              state' (assoc state' :round round :commit-index (count sequence))]
          (n/result state'
                    (into [(n/set-timer :gossip (:gossip-ticks state'))]
                          (concat
                           ;; The protocol has no `here is my committed prefix,
                           ;; resynchronise` effect, so this is Nakamoto's
                           ;; trick: an empty `:dropped` means "truncate to this
                           ;; vertex, whatever you hold", and a vertex nobody
                           ;; committed truncates to nothing.
                           (when (seq sequence)
                             [(n/revert ::genesis [])
                              (n/commit (mapv vertex sequence) 0)])
                           [(n/request-value {:round round})])))))))

  (step [_ state input]
    (case (:type input)

      ;; The application supplied a payload: build, sign and broadcast our
      ;; header for this round. Signing our own header IS a vote for it, so it
      ;; goes through the same durable slot guard.
      :value-ready
      (let [round (:round state)
            slot [(:peer-id state) round]
            announce (fn [h] (n/broadcast :bullshark {:kind :header :header h
                                                      :from (:peer-id state)}))]
        (cond
          ;; Already proposed for this round -- possibly in a previous life, if
          ;; this header came back off disk. Re-announce it; do not build a new
          ;; one, because a new parent set gives a new digest and that is a
          ;; second signature for one slot.
          (get-in state [:own-headers round])
          (n/result state [(announce (:header (get-in state [:own-headers round])))])

          ;; We signed something for this slot and cannot say what. Going silent
          ;; is the only safe option, and it costs one round.
          ;;
          ;; This branch is why the HEADER is persisted next to the guard rather
          ;; than only its digest. `persist-then`'s rule -- gate exactly the
          ;; messages that constitute this node's binding commitment -- says
          ;; what to GATE, and is silent on what to STORE, and storing only the
          ;; guard is not enough: a restarted node then knows it must not sign
          ;; a different header and has no way to re-send the one it did sign.
          ;; The first version of this port stored only the digest, and the
          ;; restarted node cheerfully proposed a fresh header for a round it
          ;; had already signed for -- equivocating with itself, across a crash.
          (get-in state [:voted slot])
          (n/result (update-in state [:rejected :unrecoverable-header] (fnil inc 0)))

          :else
          (let [header {:author (:peer-id state)
                        :round round
                        :payload (:value input)
                        :parents (round-parents state round)}
                hid (header-id header)
                state (-> state
                          (assoc-in [:own-headers round] {:header header :id hid})
                          (assoc-in [:votes round] #{(:peer-id state)})
                          (assoc-in [:voted slot] hid))]
            (n/result state
                      [(n/persist-then
                        {:writes {[:voted slot] hid
                                  [:proposed round] header}
                         :durable? true
                         :token [:header round]
                         :then [(announce header)]})]))))

      :message-received
      (let [{:keys [kind header cert digests round] :as msg} (:msg input)
            from (:from input)]
        (case kind
          :header (receive-header state header from)
          :vote (receive-vote state (assoc msg :from from))
          :certificate (insert-certificate state cert)
          ;; Answered from the STORE, never from the consensus DAG. See the
          ;; header comment on `stored`: the DAG has already thrown away most of
          ;; what a lagging peer is asking for.
          :want
          (n/result state
                    (mapv (fn [c] (n/send-to from {:kind :certificate :cert c
                                                   :from (:peer-id state)}))
                          (sort-by :id (keep #(stored state %) digests))))
          (n/result state)))

      :timer-fired
      (case (:timer-id input)
        ;; The anchor never came. Seal the round without it; a later anchor
        ;; back-fills anything that turns out to have been linked.
        :anchor (advance-round (assoc state :anchor-timeout true :anchor-armed false))

        ;; Retransmission. Without it a single lost header or certificate stalls
        ;; a round forever -- the failure Tendermint recorded as "no gossip
        ;; timer inside the state machine means zero progress under 30% loss".
        :gossip
        ;; Re-announce our latest HEADER and our latest CERTIFICATE.
        ;;
        ;; `:own-latest` rather than "our certificate one round below the
        ;; current one", which is what this did first and which is wrong in
        ;; exactly the case that matters. A node certifies its round-r header
        ;; while still AT round r -- it advances only once 2f+1 certificates
        ;; exist at r, and its own is merely one of them. So the round-below
        ;; expression re-announces the previous round forever and the newest
        ;; certificate, the one peers are waiting on, is broadcast exactly once
        ;; and never again. Under 50% loss all four nodes ended up holding a
        ;; certified round-3 certificate that none of the others ever saw, and
        ;; the network stopped dead with every node reporting healthy state.
        (let [own (get-in state [:own-headers (:round state)])
              mine (stored state (:own-latest state))]
          (n/result state
                    (into []
                          (concat
                           (when own
                             [(n/broadcast :bullshark {:kind :header
                                                       :header (:header own)
                                                       :from (:peer-id state)})])
                           (when mine
                             [(n/broadcast :bullshark {:kind :certificate :cert mine
                                                       :from (:peer-id state)})])
                           ;; Re-ask for the parents of everything still parked.
                           ;; A one-shot request at park time is not enough:
                           ;; lose the reply and the node is stuck forever, and
                           ;; a node that fell far behind needs the whole
                           ;; backward cascade to survive one lost message. This
                           ;; is the catch-up seam Tendermint recorded as
                           ;; missing entirely.
                           (missing-parent-requests state)
                           [(n/set-timer :gossip (:gossip-ticks state))]))))
        (n/result state))

      ;; Nothing is gated behind the certificate write, so there is nothing to
      ;; release; the vote's `:then` is released by the interpreter.
      :persisted (n/result state)

      :vertex-received (insert-certificate state (:vertex input))

      (n/result state))))

(defn create
  "Create a Bullshark node.

  Config: `:stake` {author stake}, `:gc-depth` n, `:anchor-fn`
  `(fn [round validators stake] -> author)`, `:anchor-wait-ticks` n,
  `:gossip-ticks` n."
  []
  (->Bullshark))
