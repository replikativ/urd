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
  certificate signature plus a roaring bitmap of committee indices, we carry one
  attestation per signer -- 2f+1 x 64 bytes on the wire rather than 96 plus a
  bitmap. That is the entire cost of the substitution.

  This paragraph used to claim that the state machine's predicate was
  unchanged, because what it checks is that the SET of signers is decisive,
  never the bytes. That sentence was the bug. A certificate is a THIRD PARTY's
  aggregated claim and it is relayed: the peer handing it to us is almost never
  a signer, so transport authentication says nothing about the signers and the
  names alone are worth nothing. `certified?` verifies each attestation and
  counts stake only over those that verify; `init` refuses to start without a
  verifier, because a permissive default is how the missing check went
  unnoticed through an entire audit round.

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
    for that author, then a stable sort by round.

    Arrival-order independence comes from the DFS, not from the sort's
    stability. The DFS visits parents through `(sort (cert-parents x))`, so its
    output sequence is already a function of the DAG alone and cannot see the
    order certificates were inserted in. Stability then fixes the WITHIN-ROUND
    order to that DFS sequence rather than to an arbitrary permutation of it.
    Both matter; only the first is what makes two nodes agree. narwhal's own
    comment is blunter: ordering the output by round is not really necessary,
    it just makes the commit sequence prettier (`utils.rs:96`).
  - GC drops rounds more than `gc-depth` below the last committed round, and
    each author's certificates below its own last committed round.

  ## Three mechanisms stop the DFS, and all three are needed

  1. `already-queued` dedups within one flatten;
  2. each author's committed watermark stops the walk at or below it;
  3. GC and live insertion keep certificates below that watermark out of the DAG.

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
            [urd.consensus.pending :as pending]
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
  (n/byzantine-threshold total))

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
  "Build a certificate value with its digest attached.

  `votes` is `{signer attestation}`, not a set of names. A certificate is a
  THIRD PARTY's aggregated claim that 2f+1 validators voted, and it is relayed:
  the peer who hands it to us is almost never one of the signers. So the names
  alone are worth nothing, and the attestations are the whole content -- see
  `certified?`.

  `:signers` is derived and kept because the equivocation and quorum checks
  read it; it is never the basis for counting stake."
  [header votes]
  (let [c {:header header :votes votes :signers (set (keys votes))}]
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
               ;; No votes, and none needed: `certified?` short-circuits on
               ;; round 0 because every node derives this same set from the
               ;; committee, so there is nothing to attest to.
               [a (certificate {:author a :round 0 :payload nil :parents #{}}
                               {})]))
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
  order without a single message being lost.

  ## Seeded through `from-key`, not `make`

  This drew from `(rng/make round)` -- the round number straight into the
  generator as its state. xorshift32 is GF(2)-linear and one round of it does
  not decorrelate consecutive seeds, so the draw tracked the seed almost
  exactly. At four validators with uniform stake the anchors for rounds 2..15
  came out `:c :d :a :b` repeating: literally `round mod n`, the rule this
  function exists to replace.

  Worse than it sounds, because ANCHORS ONLY EXIST AT EVEN ROUNDS. Sampling
  that cycle every second round selects from half of it, so for rounds 4..14
  only `:a` and `:c` ever anchored -- two of the four validators could not be
  chosen at all across six consecutive waves. Frequency counts over many
  rounds still look uniform, which is why the existing stake-weighting test
  passed; the bias is in the ORDER, not the totals. If one of the two
  reachable anchors is slow, commits stall while the DAG is perfectly healthy.

  `rng/from-key` applies the murmur3 avalanche finalizer before handing the
  state to xorshift, so every input bit affects every output bit. Raft's
  `randomized-election-timeout` carries the same note, for the same reason,
  found the same way -- the lesson was recorded there and never applied here."
  [round validators stake]
  (let [total (reduce + 0 (map #(get stake % 1) validators))
        [x _] (rng/next-int (rng/from-key round) (max 1 total))]
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
    committed round equals or exceeds that round;
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
                                  (<= (cert-round c) (get last-committed (cert-author c) 0)))
                            [st q]
                            [(conj st c) (conj q d)])
                          [st q]))
                      [stack queued]
                      ;; Strings, sorted as strings. See the namespace note.
                      (sort (cert-parents x)))]
          (recur stack queued (conj ordered x)))))))

(defn store-depth
  "How far back the certificate store retains, in rounds.

  Deeper than `gc-depth` by construction -- the DAG is the working set, the
  store is what a lagging peer is served from. Ten times, floored at 100, which
  at Narwhal's round rate is minutes of history rather than a fixed count: the
  bound exists to stop unbounded growth, not to make catch-up marginal.

  Configurable via `:store-depth`, and that is not only for tests: the right
  retention depends on how far behind a peer may fall before it is cheaper to
  state-sync than to replay, which is a deployment question. It also makes the
  property testable at all -- with the 100-round floor, a run short enough to be
  a unit test never reaches the frontier, so the store keeps everything and a
  test cannot tell a correct horizon from a wrong one."
  [state]
  (or (:store-depth state)
      (max 100 (* 10 (:gc-depth state 50)))))

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
             (:dag state))
        ;; The STORE and the slot map are bounded too, and separately from the
        ;; DAG. Both grew without limit: `:certificates` because catch-up is
        ;; served from it and it therefore deliberately outlives the consensus
        ;; DAG, `:slots` because the one-certificate-per-(author, round) check
        ;; reads it forever. "Deliberately outlives" is not "never released",
        ;; and a node that runs for a week held every certificate it ever saw.
        ;;
        ;; `store-depth` is the retention, and must EXCEED `gc-depth`: the DAG
        ;; is the working set and the store is what a lagging peer is served
        ;; from, so releasing them together would reintroduce the bug where a
        ;; node that fell behind could never return -- catch-up read from the
        ;; consensus DAG, which the GC empties by design.
        keep-from (- lcr (store-depth state))
        certs (into {} (remove (fn [[_ c]] (< (cert-round c) keep-from)))
                    (:certificates state))
        slots (into {} (remove (fn [[[_ r] _]] (< r keep-from))) (:slots state))]
    (assoc state
           :last-committed lc :last-committed-round lcr :dag dag
           :certificates certs :slots slots)))

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
  certificates of `inserted-round` itself -- the ones provably already present.

  The returned sequence carries `::anchors` metadata: the rounds of the anchors
  this call ELECTED as commit points, oldest first. Nothing in the library reads
  it. It exists because electing an anchor and ordering a vertex are different
  events that produce the same kind of value, and from the outside they are
  indistinguishable -- a skipped anchor's certificate is still ordered later, as
  an ordinary member of some subsequent anchor's causal history, at whatever
  position that anchor puts it. A test that tried to recover the election by
  matching author against `anchor-for` therefore read those back-filled
  certificates as anchors committed out of order, and reported a violation
  against a run that was correct. Reconstructing the decision from the output
  was the mistake; this reports it."
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
            (let [elected (reverse (order-anchors state anchor anchor-fn))
                  [st out] (reduce (fn [[st acc] a]
                                     (let [sub (order-sub-dag st a)]
                                       [(reduce record-committed st sub) (into acc sub)]))
                                   [state []]
                                   ;; Oldest anchor first.
                                   elected)]
              [st (with-meta out {::anchors (mapv cert-round elected)})])))
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
      (let [known (keep #(stored state %) parents)]
        ;; REJECT a parent at the wrong round rather than skipping it.
        ;; `core.rs:225-229` `ensure!`s `x.round() + 1 == header.round` and
        ;; errors out; merely leaving it out of the tally admitted a certificate
        ;; whose remaining parents happened to clear 2f+1 but which still
        ;; carried edges the ordering layer can never traverse -- `order-sub-dag`
        ;; and `linked?` only ever look at `(dec round)` -- and let a Byzantine
        ;; author keep honest nodes re-requesting the junk digests forever.
        (and (every? #(= (dec round) (cert-round %)) known)
             (let [authors (into #{} (map cert-author) known)]
               (>= (reduce + 0 (map #(get (:stake state) % 0) authors))
                   (quorum-threshold (:total-stake state))))))))

(defn- have-all-parents? [state round parents]
  (or (zero? round)
      (every? #(some? (stored state %)) parents)))

(defn- certified?
  "Do the VERIFIED signers carry >= 2f+1 stake?

  ## This used to count a list of names supplied by the sender

  The previous docstring said the signature bytes were checked at the edge and
  arrived as `:verified-by`, so the state machine needed only to check that the
  set of signers was decisive. That was false in three ways at once: a
  certificate carried no signature bytes for anything to check, `:verified-by`
  appeared nowhere in this namespace outside that sentence, and `:verified-by`
  authenticates only the peer who RELAYED the message -- which for a
  certificate is precisely not one of the parties whose attestation matters.

  The consequence was a forged certificate for the cost of typing one. A
  Byzantine node that is neither the author nor the anchor broadcasts two
  certificates for the same (author, round) slot, both naming every validator
  as a signer and differing only in payload. Two honest nodes that see
  different ones first each insert theirs, each rejects the other as
  equivocation, and they hold different anchors at that round FOREVER --
  different sub-DAGs, different total orders. Bullshark's central claim broken
  by one faulty node, and our stricter reject-second equivocation rule is what
  makes the divergence permanent rather than transient.

  Narwhal checks this before anything else touches the certificate:
  `Certificate::verify` (`types/src/primary.rs:516-546`) recomputes the signer
  set from the bitmap, requires `weight >= quorum_threshold`, and THEN verifies
  the aggregate signature; `sanitize_certificate` (`primary/src/core.rs:548-572`)
  sits on the only ingress path.

  We verify per-signer rather than in aggregate -- the substitution the
  namespace docstring describes -- and stake is counted only over attestations
  that verify. An unverifiable attestation is not an error to report, merely
  weight that does not count: a certificate padded with junk signers simply
  fails to reach the threshold.
  MEMBERS FIRST, then verify, and that order is a bound rather than a
  preference. `:votes` is attacker-supplied and was consumed whole, so one
  certificate naming a million unknown signers cost a million Ed25519
  verifications before the threshold arithmetic rejected it -- inside `step`,
  on the event loop. Filtering by membership first is strictly equivalent,
  because a signer with no stake contributes zero weight whether or not its
  attestation verifies, and it bounds the work to the number of known
  validators however large the message is."
  [state c]
  (or (zero? (cert-round c))
      (let [verify (:verify-vote state)
            hid (header-id (:header c))
            stake (:stake state)
            members (filter (fn [[signer _]] (pos? (get stake signer 0))) (:votes c))
            verified (filter (fn [[signer att]] (verify signer hid att)) members)]
        (>= (reduce + 0 (map (fn [[signer _]] (get stake signer 0)) verified))
            (quorum-threshold (:total-stake state))))))

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
       (map? (:votes c))
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
                  [(n/commit vs)])))))

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
  the paper's rule rather than the repo's.

  ## Catching up jumps, it does not walk

  A node that fell behind and then ordered a long stretch of DAG could not get
  its own round moving again. `advance-round` stepped one round at a time and
  required a quorum AT the current round, and after catch-up the current round
  is far below the frontier -- worse, the node's own `record-committed` GC has
  by then pruned everything below `last-committed-round`, so the round it is
  sitting on is empty and can never acquire a quorum. Stuck, permanently, in a
  hole it dug itself.

  What that looked like: a partitioned node rejoined, ordered and committed the
  entire history it had missed, agreed with everyone on every position -- and
  sat at round 4 while its peers passed round 100, never proposing another
  header. It contributes nothing to the DAG from then on. `agreement?` is
  perfectly happy, because this is a liveness failure of one node and not a
  safety failure of any.

  `restore` already had the answer and used it on exactly one path: scan down
  from the DAG's highest round for one that holds a quorum. That is what a node
  that has been away needs on the LIVE path too. Skipping rounds is safe --
  safety lives in the certificates and in the ordering function, never in the
  round counter.

  Found because fixing the anchor-selection bias changed the schedule: the
  biased anchors happened to keep the rejoining node's round moving, so the
  test asserting it rejoins had been passing for a reason unrelated to the
  mechanism it was testing."
  [state]
  (let [r0 (:round state)
        highest (reduce max 0 (keys (:dag state)))
        ;; The furthest round we could legitimately be at, given what we hold.
        frontier (loop [r' highest]
                   (cond (<= r' r0) r0
                         (have-quorum-at? state r') (inc r')
                         :else (recur (dec r'))))
        jumped? (> frontier r0)
        state (if jumped?
                (assoc state :round frontier :anchor-armed false :anchor-timeout false)
                state)
        r (:round state)]
    (cond
      (not (have-quorum-at? state r))
      ;; Landing ON the frontier means there is no quorum here yet -- of course
      ;; not, nobody has certified this round. Propose anyway when we JUMPED:
      ;; updating the counter without asking for a payload would leave the node
      ;; silent at a new number, which is the same non-participation with a
      ;; better-looking `:round`.
      (if jumped?
        (let [{state :state fx :effects} (propose-header state)]
          (n/result state (into [(n/cancel-timer :anchor)] fx)))
        (n/result state))

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

(declare receive-header)

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
          state (if (or (< (+ r (:gc-depth state)) (:last-committed-round state))
                        (< r (get (:last-committed state) (cert-author c) 0)))
                  state
                  (assoc-in state [:dag r (cert-author c)] c))
          {state :state fx1 :effects} (deliver-commits state r)
          ;; The commit rides in the write's `:then`, exactly as Tendermint's
          ;; and SCP's do. It used to be emitted ahead of the barrier, and that
          ;; is a durability violation with teeth: the ordering layer is pure,
          ;; so a restarted node RE-DERIVES its committed prefix from the
          ;; certificate store rather than replaying a log -- which only works
          ;; if every certificate the decision rested on is actually in that
          ;; store.
          ;;
          ;; It was not. `deliver-commits` ran on a state that already contained
          ;; `c` while `c`'s persist was still in flight, so a crash in that
          ;; window left a node that had TOLD its consumer about a commit it
          ;; could no longer justify. On restart `replay-order` found one
          ;; supporting certificate instead of two, re-derived nothing, and
          ;; reset `:commit-index` to 0 -- after which the node re-committed the
          ;; whole prefix on top of the copy the consumer still held. The
          ;; consumer's log was literally doubled and `agreement?` failed.
          ;;
          ;; Gating on THIS certificate's write is sufficient for the whole
          ;; decision, not just for `c`: `:landed` is an ordered log truncated
          ;; at the last durable point, so the newest write landing means every
          ;; earlier one has too -- including the rest of the anchor's sub-DAG
          ;; and the other certificates that supplied its support.
          persisted (n/persist-then {:writes {[:cert (:id c)] c}
                                     :durable? true
                                     :token [:cert (:id c)]
                                     :then (vec fx1)})
          {state :state fx2 :effects} (advance-round state)
          ready (->> (vals (:pending state))
                     (filterv #(have-all-parents? state (cert-round %) (cert-parents %)))
                     ;; Sorted so replay does not depend on map iteration order.
                     (sort-by (juxt cert-round :id)))]
      (let [res (reduce (fn [res p]
                          (let [{s :state f :effects} (insert-certificate (:state res) p)]
                            (n/result s (into (:effects res) f))))
                        ;; `fx1` is NOT here: it is inside `persisted`'s
                        ;; `:then`, and emitting it in both places would commit
                        ;; twice.
                        (n/result state (into [persisted] fx2))
                        ready)
            ;; ...and headers that were waiting on THIS certificate. They were
            ;; parked rather than dropped, so the vote we owe their author is
            ;; still owed. This is Narwhal's `core.rs:644` loop-back.
            [pool waiting] (pending/release (:pending-headers (:state res)) (:id c))
            res (assoc-in res [:state :pending-headers] pool)]
        (reduce (fn [acc {:keys [header from]}]
                  (let [{s :state f :effects} (receive-header (:state acc) header from)]
                    (n/result s (into (:effects acc) f))))
                res
                waiting)))))

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
        ;; The attestation is what makes this vote worth anything to a node
        ;; that did not receive it from us. See `certified?`.
        reply #(n/send-to from {:kind :vote :from (:peer-id state)
                                :header-id hid :round (:round header)
                                :author (:author header)
                                :att ((:sign-vote state) (:peer-id state) hid)})]
    (cond
      ;; A retransmission. Re-answer: a lost vote otherwise stalls the author
      ;; forever, which is the failure Tendermint recorded under message loss.
      (= prev hid) (n/result state (when-not (contains? (:pending-votes state) slot)
                                     [(reply)]))

      prev
      (n/result (update-in state [:rejected :equivocation] (fnil inc 0))
                [(n/report-equivocation
                  (:author header)
                  {:kind :conflicting-headers :round (:round header)
                   :first prev :second hid})])

      :else
      (n/result (-> state (assoc-in [:voted slot] hid) (update :pending-votes conj slot))
                [(n/persist-then {:writes {[:voted slot] hid}
                                  :durable? true
                                  :token [:voted slot]
                                  :then [(reply)]})]))))

(defn- receive-header
  [state header from]
  (cond
    (not= (:author header) from)
    (n/result (update-in state [:rejected :forged-author] (fnil inc 0)))

    (not (and (int? (:round header)) (pos? (:round header))))
    (n/result (update-in state [:rejected :bad-round] (fnil inc 0)))

    (not (have-all-parents? state (:round header) (:parents header)))
    ;; We must not vote for a header whose history we do not hold: signing it
    ;; asserts an availability we cannot provide. But we must not FORGET it
    ;; either, and it used to be dropped the moment the `:want` went out --
    ;; a one-shot request with nothing to receive the answer.
    ;;
    ;; The vote was then lost for good. `round-parents` names every certificate
    ;; we hold at the previous round, deliberately a maximal set, and an author
    ;; proposes the instant it reaches 2f+1 -- so a peer one certificate behind
    ;; at that moment is the NORMAL case, not an edge case. Each such peer
    ;; dropped the header and never revisited it, the author fell short of a
    ;; quorum, and its certificate for that round never formed. When the author
    ;; is the anchor, a whole wave is wasted.
    ;;
    ;; Narwhal parks the header itself -- `WaiterMessage::SyncParents` carries
    ;; the header (`synchronizer.rs:115-144`), `header_waiter` waits on the
    ;; store (`header_waiter.rs:239-277`), and `core.rs:644` loops it back
    ;; through `process_header`, which then reaches `send_vote`.
    (let [missing (remove #(some? (stored state %)) (:parents header))
          hid (header-id header)
          state (reduce (fn [st parent]
                          (update st :pending-headers pending/park
                                  hid parent {:header header :from from}
                                  (:round state)))
                        state
                        missing)
          [pool dropped] (pending/reap (:pending-headers state) (:round state)
                                       (:header-ttl state) (:header-limit state))]
      (n/result (assoc state :pending-headers pool)
                (cond-> [(n/broadcast :bullshark
                                      {:kind :want :from (:peer-id state)
                                       :round (dec (:round header))
                                       :digests (vec (sort (:parents header)))})]
                  (pos? dropped)
                  (conj (n/log-effect :debug (str "dropped " dropped " parked headers"))))))

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
  [state {:keys [header-id round from att]}]
  (let [own (get-in state [:own-headers round])]
    (if (or (nil? own)
            (not= header-id (:id own))
            (contains? (:pending-votes state) [(:peer-id state) round])
            (contains? (:certified state) round)
            ;; A vote we cannot verify is a vote we cannot pass on. We are
            ;; about to aggregate these into a certificate that peers will
            ;; accept on our say-so, so anything that does not verify here
            ;; would be a forgery WE minted.
            (not ((:verify-vote state) from header-id att)))
      (n/result state)
      ;; Keyed by signer, holding the attestation: `:votes` was a set of names,
      ;; which was all a certificate could carry and all a peer could check.
      (let [votes (assoc (get-in state [:votes round] {}) from att)
            state (assoc-in state [:votes round] votes)]
        (if (< (reduce + 0 (map #(get (:stake state) % 0) (keys votes)))
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
;; Attestations -- TEST ONLY
;; ============================================================

(defn test-attestations
  "A toy vote-attestation scheme, for tests and simulations only.

  NOT CRYPTOGRAPHY. It is a hash of a per-signer string, so anyone who can read
  this namespace can mint one for any signer. What it does provide is the
  SHAPE: an attestation binds a signer to a header id, verification is a pure
  predicate, and an attestation that was not produced this way fails -- which
  is what a test needs to drive `certified?` down both branches.

  A deployment supplies real signatures here. `init` refuses to start without
  them precisely so that this stub cannot be reached by accident."
  []
  (let [sign (fn [signer hid] (hasch/uuid [::test-vote signer hid]))]
    {:sign-vote sign
     :verify-vote (fn [signer hid att] (and (some? att) (= att (sign signer hid))))}))

;; ============================================================
;; The node
;; ============================================================

(defrecord Bullshark []
  n/Node

  (capabilities [_]
    ;; `:resync` and NOT `:revert`. Bullshark never revokes a decision; on
    ;; restart it re-derives its committed prefix from the durable DAG and
    ;; announces it. Those were the same effect until section 21, which is
    ;; exactly the confusion this declaration exists to prevent.
    {:emits #{:broadcast :send :persist-then :set-timer :cancel-timer
              :request-value :commit :resync :report-equivocation :log}
     :topics #{:bullshark}})

  (init [_ config]
    (let [validators (n/validator-set config)
          stake (or (:stake config) (into {} (map (fn [v] [v 1])) validators))
          ;; REQUIRED, and deliberately not defaulted. A permissive default is
          ;; how the hole this closes came to exist in the first place: the
          ;; check was described in a docstring, nothing implemented it, and
          ;; every test passed. A node that cannot verify a vote cannot safely
          ;; accept a relayed certificate, so it refuses to start instead of
          ;; running with the guard silently absent.
          sign-vote (or (:sign-vote config)
                        (throw (ex-info "bullshark requires :sign-vote -- (fn [signer header-id]) -> attestation"
                                        {:peer-id (:peer-id config)})))
          verify-vote (or (:verify-vote config)
                          (throw (ex-info "bullshark requires :verify-vote -- (fn [signer header-id att]) -> boolean"
                                          {:peer-id (:peer-id config)})))
          base (merge (initial-consensus
                       {:validators validators
                        :stake stake
                        :gc-depth (or (:gc-depth config) 50)
                        :anchor-fn (or (:anchor-fn config) stake-weighted-anchor)})
                      {:peer-id (:peer-id config)
                       :sign-vote sign-vote
                       :verify-vote verify-vote
                       :round 1
                       :voted {}
                       :pending-votes #{}
                       :pending {}
                       ;; Headers waiting on a parent certificate we have
                       ;; asked for. Bounded by round-age and by count: an
                       ;; unbounded pool is a leak an adversary drives by
                       ;; proposing headers naming parents that do not exist.
                       :pending-headers pending/empty-pool
                       :header-ttl (or (:header-ttl config) 10)
                       :header-limit (or (:header-limit config) 512)
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
                       :votes (into {} (map (fn [[r {:keys [id]}]]
                                              [r {(:peer-id config)
                                                  (sign-vote (:peer-id config) id)}]))
                                    proposed))]
      (if (empty? certs)
        (n/result state (cond-> [(n/set-timer :gossip (:gossip-ticks state))
                                 (n/request-value {:round 1})]
                          ;; We are RESTARTING (something is durable) but hold
                          ;; no certificates, so we can re-derive nothing and
                          ;; `:commit-index` is 0. The consumer may still be
                          ;; holding the prefix we announced before we died; if
                          ;; we do not tell it to drop that, everything we
                          ;; re-derive from here is appended to it. `(seq
                          ;; restored)` is what separates this from a first
                          ;; boot, where there is nothing to correct and an
                          ;; announcement would be noise.
                          (seq restored) (conj (n/resync []))))
        (let [restored-state (restore-dag state certs)
              ;; Our own certificates, from the durable log. Two things are
              ;; restored from them, and both were lost across a crash:
              ;;
              ;;   `:own-latest` -- what the gossip timer re-announces. Without
              ;;   it the newest certificate we ever built is silent until we
              ;;   certify again, which is precisely the stall the note on the
              ;;   `:gossip` branch was written for, re-introduced by the one
              ;;   path that does not go through `certify`.
              ;;
              ;;   `:certified` -- the rounds we have already certified, so a
              ;;   restarted node does not rebuild a certificate it already
              ;;   broadcast.
              mine (->> certs
                        (filter #(= (:peer-id config) (cert-author %)))
                        (sort-by cert-round))
              restored-state (assoc restored-state
                                    :own-latest (:id (last mine))
                                    :certified (into #{} (map cert-round) mine))
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
                           ;; `resync`, not a revert. Bullshark never revokes a
                           ;; decision; on restart it re-derives its committed
                           ;; prefix from the durable DAG and announces it. This
                           ;; used to be `(revert ::genesis [])` plus a commit,
                           ;; leaning on an empty `:dropped` meaning "truncate to
                           ;; whatever you hold" -- which is why `:dropped` had to
                           ;; be optional, and why one effect meant two things.
                           ;;
                           ;; UNCONDITIONAL, including when the sequence is
                           ;; empty. `(when (seq sequence) ...)` skipped exactly
                           ;; the dangerous case: we have just set
                           ;; `:commit-index` to 0, so we will re-emit the whole
                           ;; order as it re-derives, and a consumer that was
                           ;; never told to drop the old copy appends the second
                           ;; one to the first. An empty resync is not a no-op,
                           ;; it is the statement "I hold nothing", and that is
                           ;; the true one whenever `:commit-index` is 0.
                           [(n/resync (mapv vertex sequence))]
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
          ;; A validator set change CANNOT be honoured by this algorithm, and
          ;; saying so is the whole point of this branch.
          ;;
          ;; `order-anchors` walks backwards from a newly committed anchor and
          ;; calls `(anchor-fn state r)` for HISTORICAL rounds r -- with the
          ;; CURRENT committee. Committing an anchor at round r retroactively
          ;; commits skipped anchors at r-2, r-4, ..., re-deriving who led those
          ;; rounds from today's set. A committee that changed in between
          ;; therefore rewrites which anchors led the past, and the total order
          ;; with it. Narwhal has the identical property and resolves it by
          ;; destroying the DAG and rebuilding from a new genesis; there is no
          ;; edit that grafts a new committee onto an existing one.
          ;;
          ;; So the options are epochs -- a hard cut, drain, restart, which is a
          ;; different protocol rather than a configuration of this one -- or
          ;; refusing. Refusing LOUDLY is what matters: silently proposing the
          ;; value would have consensus order it, the application see it
          ;; committed, and the set never change. The application would then
          ;; believe a membership it does not have, which is worse than an
          ;; error, because nothing reports it.
          (seq (:validator-updates (:value input)))
          (n/result state
                    [(n/log-effect
                      :error
                      {:event :validator-updates-unsupported
                       :algorithm :bullshark
                       :reason (str "anchor selection re-derives HISTORICAL "
                                    "leaders from the current committee, so a "
                                    "set change rewrites the committed order. "
                                    "Requires epochs (hard cut), not an "
                                    "in-place update.")
                       :updates (:validator-updates (:value input))})])

          (contains? (:pending-votes state) slot)
          (n/result state)

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
                          ;; Our own vote, attested like anyone else's -- it
                          ;; ends up inside a certificate that peers verify,
                          ;; and an unattested self-vote would simply not count
                          ;; toward our own quorum.
                          (assoc-in [:votes round]
                                    {(:peer-id state) ((:sign-vote state) (:peer-id state) hid)})
                          (assoc-in [:voted slot] hid)
                          (update :pending-votes conj slot))]
            (n/result state
                      [(n/persist-then
                        {:writes {[:voted slot] hid
                                  [:proposed round] header}
                         :durable? true
                         :token [:voted slot]
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
          ;; BOUNDED, and only for validators.
          ;;
          ;; `digests` is attacker-supplied and was served whole, one `send-to`
          ;; per hit -- and the runtime emulates unicast as a broadcast, so
          ;; every reply reaches every peer. One `:want` naming fifty thousand
          ;; digests observed from gossip therefore made each of n nodes emit
          ;; fifty thousand certificate messages, each delivered n times: n^2
          ;; certificate-sized deliveries for one request, repeatable at will,
          ;; with a fifty-thousand-element effect vector materialised inside
          ;; `step` on the way.
          ;;
          ;; An honest `:want` asks for one round's missing parents, which is
          ;; at most one per validator -- see `missing-parent-requests`. So the
          ;; committee size is a generous cap and costs a legitimate requester
          ;; nothing.
          ;;
          ;; Narwhal bounds the same request (`MAX_CERTIFICATES_TO_FETCH`) and
          ;; additionally permits one inflight fetch per peer; the requester
          ;; check here is the part its own TODO admits is missing.
          :want
          (if-not (contains? (set (:validators state)) from)
            (n/result state [(n/log-effect :debug
                                           {:event :want-from-non-validator
                                            :from from})])
            (n/result state
                      (mapv (fn [c] (n/send-to from {:kind :certificate :cert c
                                                     :from (:peer-id state)}))
                            (->> (if (sequential? digests) digests [])
                                 (take (count (:validators state)))
                                 (keep #(stored state %))
                                 (sort-by :id)))))
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
                           (when (and own (not (contains? (:pending-votes state)
                                                          [(:peer-id state) (:round state)])))
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

      ;; The interpreter releases the first send after this completion.
      ;; Later retransmissions may now release the same slot immediately.
      :persisted
      (let [token (:token input)]
        (n/result (if (and (vector? token) (= :voted (first token)))
                    (update state :pending-votes disj (second token))
                    state)))

      :vertex-received (insert-certificate state (:vertex input))

      (n/result state))))

(defn create
  "Create a Bullshark node.

  Config: `:stake` {author stake}, `:gc-depth` n, `:anchor-fn`
  `(fn [round validators stake] -> author)`, `:anchor-wait-ticks` n,
  `:gossip-ticks` n."
  []
  (->Bullshark))
