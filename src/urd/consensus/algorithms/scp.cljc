(ns urd.consensus.algorithms.scp
  "Stellar Consensus Protocol -- Federated Byzantine Agreement -- as a pure
  state machine on `urd.consensus.node`.

  The sixth algorithm in the library, and the first with **no global validator
  set**. Raft, Tendermint, round-robin and Snowman all start from \"here are the
  n validators\"; Nakamoto starts from \"anyone with hashpower\". SCP starts from
  neither. Each node names its own *quorum slices*, and whether a set of peers
  is decisive is a question only that node can answer -- from data it may not
  have yet.

  ## Source of truth

  `stellar-core/src/scp/` (checkout of 2017; SCP's core has been frozen since
  2015, so it is authoritative). File/line references below point there. The
  IETF draft `draft-mazieres-dinrg-scp-05` is the same algorithm in prose.

  Two deliberate divergences, both marked at their definitions:

  - `update-round-leaders` ACCUMULATES leaders across nomination rounds. The
    2017 checkout clears the set each round (`NominationProtocol.cpp:203`);
    current stellar-core keeps them, and the growing-leader-set argument is what
    makes nomination converge. We implement the convergent version.
  - The `attempt*` rules scan candidate ballots from ALL known statements rather
    than from the `hint` statement that triggered them. stellar-core's hint is
    an optimisation to bound the scan; taking the union over every possible hint
    is a superset, and a superset cannot cause an unsafe accept because each
    candidate still has to clear federated voting on its own.

  ## The four things this file exists to test

  `Membership`'s tri-state `quorum?` and `node/fixpoint` were designed for SCP
  and, until this file, never exercised by anything. The verdicts are recorded
  at each definition.

  ## Quorum-ness is a greatest fixpoint, not a cardinality

  A set U is a *quorum* iff every member of U has one of its own slices
  contained in U. That is self-referential, so it is computed as a greatest
  fixpoint (`LocalNode.cpp:252-290`): start from all candidates, repeatedly
  discard anyone whose advertised quorum set is not satisfied by the survivors,
  stop when stable, then ask whether the survivors contain a slice of MINE.

  `v-blocking?` (`LocalNode.cpp:194-220`) is the cardinality DUAL and is purely
  LOCAL -- it reads only my own quorum set and never anybody else's. The
  asymmetry is the point: quorum is transitive, v-blocking is not.

  ## Why the answer can be `:unknown`

  Every statement carries the HASH of its sender's quorum set, not the set
  itself. A node routinely holds a statement whose quorum set it has never seen,
  and then it genuinely cannot evaluate the fixpoint.

  stellar-core sidesteps this by refusing to process such an envelope at all --
  `Herder`'s `ItemFetcher` parks it until the quorum set arrives -- and inside
  `isQuorum` an unresolvable quorum set simply excludes its node
  (`LocalNode.cpp:266-274`), which is a safe UNDER-approximation. We do better,
  because the protocol offers a third value and it is worth finding out whether
  it carries its weight: `quorum-tri` computes BOTH bounds. Dropping the
  unknown-quorum-set nodes is the lower bound; treating them as unconditionally
  satisfied is the upper bound. Then

    lower  = true   ->  true    (no arriving data can retract it)
    upper  = false  ->  false   (no arriving data can establish it)
    otherwise       ->  :unknown

  so `:unknown` means precisely *this answer will change once I fetch something*,
  which is exactly the condition under which fetching is worth doing. `false`
  means decided with respect to arriving QUORUM SETS -- an arriving STATEMENT
  enlarges the node set being tested and can still flip it, which is harmless
  because the answer is recomputed on every pass, but it is not the stronger
  claim -- decided regardless of what arrives -- that this used to make.

  Monotonicity is what makes those bounds sound. Learning a quorum set can only
  ADD survivors to the fixpoint, and more survivors can only satisfy more
  slices, so the answer moves in one direction only.

  ## Fetching a missing quorum set needs no new effect

  §4 of the design doc proposed a `[:request-qset]` effect and a
  `:qset-received` event. Neither is necessary and we did not add them: a
  missing quorum set has to come from a peer, so it is a unicast request and a
  unicast reply -- `send-to` and `message-received`, which already exist. See
  the PR; hiding a network round trip behind a bespoke effect would have made
  its failure modes invisible.

  Replies are content-addressed and VERIFIED: `(= hash (qset-hash qset))` before
  the cache is touched, so a Byzantine peer cannot answer a fetch with a quorum
  set of its choosing and thereby manufacture a quorum for us.

  ## Purity

  `.cljc`, no host interop except one character-code helper (the same reader
  conditional `raft` uses), no clock, no RNG. Nomination leader election is a
  portable hash of (slot, previous value, round, node), which is the role
  stellar-core gives SHA-256; see `content-hash` for why the obvious portable
  hash was not good enough, and for what a real deployment should use instead."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [urd.consensus.node :as node]
            [urd.consensus.rng :as rng]
            [urd.wire :as wire]
            [hasch.core :as hasch]))

;; ============================================================
;; Portable hashing
;;
;; SCP makes two decisions by comparing hashes rather than by counting, so the
;; hash has to be both portable and actually good. See `content-hash`.
;; ============================================================

(defn- char-code [s i]
  #?(:clj (int (.charAt ^String s i))
     :cljs (.charCodeAt s i)))

(def ^:private hash-modulus
  "The largest prime below 2^32."
  4294967291)

(defn content-hash
  "A 32-bit hash with real avalanche, portable and exact on both platforms.

  Per character: one djb2 step, `h = (33h + c) mod (2^32 - 5)`, then one
  xorshift32 permutation. Neither half is enough alone, and finding that out was
  worth the trouble:

  - PLAIN djb2 (`raft/string-hash`) has no avalanche at all. Measured: the
    nomination priorities of peers :a :b :c :d came out
    870040764 / 870040797 / 870040830 / 870040863 -- consecutive multiples of
    33, the djb2 multiplier -- so the highest node id won EVERY round of EVERY
    slot. The simulation still reached consensus, which is exactly why it was
    worth catching: a broken leader lottery looks like a working one right up
    until its permanent leader is partitioned away.
  - djb2 THEN xorshift, the composition `raft` uses, is not enough either.
    xorshift32 is GF(2)-linear, so it maps a small, structured seed difference
    to a small, structured output difference; the four priorities stayed within
    3% of each other and their order barely moved between rounds.

  Interleaving them fixes it, because the multiply is nonlinear over GF(2) and
  the shifts are nonlinear over the integers, so neither structure survives the
  other. Measured over 400 nomination rounds the four peers now win 99 / 103 /
  109 / 89 times.

  The arithmetic stays exact: `h` is under 2^32 after the mix, so the largest
  intermediate is 33*2^32 + 65535, about 1.4e11, comfortably inside the 2^53
  where a ClojureScript double is still an integer. A 32-bit FNV-1a would not
  be -- its multiply reaches 7.2e16.

  Emphatically not cryptographic. It is used for two things: content-addressing
  quorum sets, where a collision costs an attacker a preimage search that a
  real deployment should make expensive by using SHA-256 over the XDR encoding;
  and the nomination lottery, which has no safety obligation at all."
  [s]
  (loop [h 5381, i 0]
    (if (>= i (count s))
      h
      (recur (first (rng/next-word
                     (rng/make (mod (+ (* h 33) (char-code s i)) hash-modulus))))
             (inc i)))))

(defn- canonical
  "A stable string for an arbitrary value.

  `pr-str` alone is not enough: map and set iteration order is not specified, so
  two equal maps could print differently and hash differently, and a quorum-set
  hash that depends on iteration order would make the content-addressing lie.
  Sequential collections keep their order because it is meaningful."
  [v]
  (cond
    (map? v) (str "{" (str/join "," (map (fn [[k x]] (str (canonical k) " " (canonical x)))
                                         (sort-by (comp pr-str key) v))) "}")
    (set? v) (str "#{" (str/join "," (sort (map canonical v))) "}")
    (sequential? v) (str "[" (str/join "," (map canonical v)) "]")
    :else (pr-str v)))

;; ============================================================
;; Quorum sets
;;
;; `{:threshold n :validators [id ...] :inner-sets [qset ...]}`, nested at most
;; two deep in practice. A node's SLICES are every way of picking `threshold`
;; members out of `validators ++ inner-sets` (an inner set counting as picked
;; when one of ITS slices is). Enumerating slices is exponential and pointless;
;; every question below is answered by walking the tree.
;; ============================================================

(defn qset-nodes
  "Every node id appearing anywhere in the tree."
  [qset]
  (into (set (:validators qset))
        (mapcat qset-nodes (:inner-sets qset))))

(defn qset-hash
  "The content hash a statement carries in place of the quorum set itself.

  This is what makes the tri-state real: peers advertise a digest, and a node
  that has never seen the preimage cannot evaluate a fixpoint through them.

  CRYPTOGRAPHIC, unlike `content-hash`. `handle-message :qset` accepts a quorum
  set from any peer on the strength of `(= (:hash msg) (qset-hash (:qset msg)))`
  alone, and a forged set is then trusted by `survivors` -- which is the
  manufacture-a-quorum-from-nothing break the whole content-addressing scheme
  exists to prevent. At 32 bits a preimage search costs seconds, so
  `content-hash` was not a hash function here, it was a formality. `hasch/uuid`
  is SHA-512-derived, synchronous on both platforms, and is already what
  Bullshark content-addresses certificates with.

  A STRING, never a raw UUID: the JVM compares a UUID's two 64-bit halves as
  SIGNED longs while ClojureScript compares the printed form, and these values
  are sorted -- see the note in `bullshark`. `content-hash` keeps the nomination
  lottery, which has no safety obligation at all."
  [qset]
  (str (hasch/uuid
        (canonical {:t (:threshold qset)
                    :v (vec (sort-by pr-str (:validators qset)))
                    :i (vec (sort (map qset-hash (:inner-sets qset))))}))))

(def max-qset-nodes
  "`QuorumSetUtils.cpp:64` -- a hard cap so a single advertised set cannot make
  `survivors`' fixpoint arbitrarily expensive."
  1000)

(defn- qset-node-seq
  "Every validator named anywhere in `qset`, WITH repeats."
  [{:keys [validators inner-sets]}]
  (concat validators (mapcat qset-node-seq inner-sets)))

(defn valid-qset?
  "Structural sanity, in the spirit of `QuorumSetUtils.cpp`.

  A threshold of zero would make the empty set a slice, i.e. would make every
  set a quorum -- the same class of silent safety failure as `node`'s missing
  `:validators` guard, and worth refusing for the same reason. Depth is capped
  at 2 as stellar-core does.

  Uniqueness is checked GLOBALLY across the tree, not per list.
  `QuorumSetSanityChecker` carries `mKnownNodes` across the whole recursion
  (`QuorumSetUtils.cpp:68-76`) and rejects any node named twice. Checking only
  within one list accepted, for instance,

      {:threshold 2 :validators [:a] :inner-sets [{:threshold 1 :validators [:a]}]}

  where `quorum-slice?` counts the single node `:a` twice toward a threshold of
  two -- so a peer can advertise a set that a single accomplice satisfies, and
  `survivors` will believe it."
  ([qset] (let [ok (valid-qset? qset 0)
                nodes (when ok (qset-node-seq qset))]
            (boolean (and ok
                          (<= (count nodes) max-qset-nodes)
                          (= (count nodes) (count (set nodes)))))))
  ([{:keys [threshold validators inner-sets] :as qset} depth]
   (boolean
    (and (map? qset)
         (integer? threshold)
         (pos? threshold)
         (<= depth 2)
         (<= threshold (+ (count validators) (count inner-sets)))
         (= (count validators) (count (set validators)))
         (every? #(valid-qset? % (inc depth)) inner-sets)))))

(defn quorum-slice?
  "Does `node-set` contain one of `qset`'s slices? (`LocalNode.cpp:141-170`)

  Recursive: an inner set counts as one member once it is itself satisfied."
  [qset node-set]
  (let [{:keys [threshold validators inner-sets]} qset]
    ;; A threshold of zero is NOT satisfied by the empty set, matching
    ;; `isQuorumSliceInternal`, whose unsigned `thresholdLeft--` underflows
    ;; rather than passing. `v-blocking?` already guarded this; the two must
    ;; agree, because `:qsets`/`:known-qsets` supplied through config bypass
    ;; `valid-qset?` entirely -- which is the path every test uses.
    (and (integer? threshold)
         (pos? threshold)
         (>= (+ (count (filter node-set validators))
                (count (filter #(quorum-slice? % node-set) inner-sets)))
             threshold))))

(defn v-blocking?
  "Does `node-set` intersect EVERY slice of `qset`? (`LocalNode.cpp:194-220`)

  Equivalently: the complement can no longer reach the threshold. This is the
  cardinality dual of `quorum-slice?` -- `n - threshold + 1` members instead of
  `threshold` -- and it is why a node whose whole quorum set has moved on can be
  dragged forward even though nothing resembling a quorum has spoken.

  Purely LOCAL: it reads one quorum set, mine, and consults no other node's
  advertised trust. That is the asymmetry §4 of the design doc calls out, and it
  is the reason `v-blocking?` is always decidable while `quorum?` is not."
  [qset node-set]
  (let [{:keys [threshold validators inner-sets]} qset]
    (if (or (nil? threshold) (zero? threshold))
      false
      (>= (+ (count (filter node-set validators))
             (count (filter #(v-blocking? % node-set) inner-sets)))
          (inc (- (+ (count validators) (count inner-sets)) threshold))))))

(defn survivors
  "The greatest fixpoint of \"everyone here is satisfied by everyone here\".

  `qset-of` maps a node to its advertised quorum set, or nil when we have never
  fetched it. `unknown-survives?` picks which bound we are computing:

    false -- an unresolvable node is discarded (lower bound, stellar-core's)
    true  -- an unresolvable node is assumed satisfied (upper bound)

  Terminates because the set only ever shrinks."
  [candidates qset-of unknown-survives?]
  (loop [s (set candidates)]
    (let [s' (into #{} (filter (fn [n]
                                 (if-let [q (qset-of n)]
                                   (quorum-slice? q s)
                                   unknown-survives?))
                               s))]
      (if (= s' s) s (recur s')))))

(defn quorum-tri
  "`true` / `false` / `:unknown` -- is there a quorum containing me inside
  `candidates`?

  \"Containing me\" is not decoration. A quorum that excludes me proves nothing
  about MY safety, and SCP's whole guarantee is per-node. It is expressed the
  way stellar-core expresses it: the surviving set has to contain one of my own
  slices, and my slices implicitly include me."
  [my-qset candidates qset-of]
  (if (quorum-slice? my-qset (survivors candidates qset-of false))
    true
    (if (quorum-slice? my-qset (survivors candidates qset-of true))
      :unknown
      false)))

(defn node-weight-fraction
  "`[num den]`: this node's share of `qset`, or nil if it is not in the tree.

  `LocalNode.cpp:100-140` returns `UINT64_MAX * n/d` and multiplies fractions
  down the tree. Kept as an exact rational instead, because the products stay
  tiny and a double would round differently in the browser. Used ONLY for
  nomination leader election -- SCP's quorums are not weighted at all, which is
  why `Membership/weight` sits so awkwardly here."
  [node qset]
  (let [{:keys [threshold validators inner-sets]} qset
        d (+ (count validators) (count inner-sets))]
    (if (some #(= % node) validators)
      [threshold d]
      (some (fn [inner]
              (when-let [[n2 d2] (node-weight-fraction node inner)]
                [(* threshold n2) (* d d2)]))
            inner-sets))))

;; ============================================================
;; Membership -- the case `node/Membership` was designed for
;;
;; Verdict, recorded here because the PR is where it belongs but the code is
;; where it will be read:
;;
;;   - `v-blocking?`'s signature is exactly right.
;;   - `quorum?`'s tri-state is right and load-bearing.
;;   - `quorum?` returning a bare `:unknown` is UNDER-informative: it says the
;;     answer is undecidable but not what would decide it, so the algorithm has
;;     to re-walk the statements itself to find the missing hashes
;;     (`missing-qset-hashes` below). That walk is the protocol's job.
;;   - `weight` does not fit. SCP's node weight is relative to a QUORUM SET, not
;;     global, and is not used by any quorum decision.
;;   - `statements` as a bare collection is a hazard: only the LATEST statement
;;     per node may count, under a total order (`isNewerStatement`) that the
;;     protocol cannot know. We reduce to one per sender before calling.
;; ============================================================

(defn statement-qset-hash [stmt] (:qset-hash stmt))

(defrecord FbaMembership []
  node/Membership

  (quorum? [_ state statements pred]
    (let [{:keys [id qset known-qsets]} state
          latest (reduce (fn [m s] (assoc m (:from s) s)) {} statements)
          candidates (into #{} (comp (filter pred) (map :from) (remove nil?))
                           (vals latest))
          ;; An EXTERNALIZE statement resolves to a SINGLETON quorum set --
          ;; `{threshold 1, validators [sender]}` -- never to the sender's
          ;; advertised one. `Slot::getQuorumSetFromStatement`
          ;; (`Slot.cpp:266-270`) substitutes `LocalNode::getSingletonQSet` for
          ;; exactly this case, and that `qfun` is what `federatedAccept`,
          ;; `federatedRatify` and the heard-from-quorum check all pass to
          ;; `isQuorum`.
          ;;
          ;; It matters on any tiered topology, which is Stellar's actual
          ;; shape. A downstream node trusting {a, b} sees EXTERNALIZE from both
          ;; while the tier-1 nodes' own quorum sets name {a, b, c, d}; with c
          ;; and d offline those qsets are unsatisfied, `isQuorum`'s fixpoint
          ;; drops a and b, then drops the downstream node too, and it is
          ;; stranded in `:confirm` permanently. A node that has externalized
          ;; has finished: it cannot change its mind, so its own quorum is no
          ;; longer anyone else's concern. The substitution also removes a
          ;; restart stall, since `:known-qsets` is empty after a restart and
          ;; every EXTERNALIZE would otherwise be unresolvable pending a fetch.
          qset-of (fn [n]
                    (cond
                      (= n id) qset
                      (= :externalize (:kind (get latest n)))
                      {:threshold 1 :validators [n] :inner-sets []}
                      :else
                      (some-> (get latest n) statement-qset-hash known-qsets)))]
      (quorum-tri qset candidates qset-of)))

  (v-blocking? [_ state statements pred]
    (let [latest (reduce (fn [m s] (assoc m (:from s) s)) {} statements)
          nodes (into #{} (comp (filter pred) (map :from) (remove nil?))
                      (vals latest))]
      (v-blocking? (:qset state) nodes)))

  (weight [_ state peer-id]
    ;; Present for protocol conformance only; nothing in SCP's safety argument
    ;; reads it. See the note above.
    (or (node-weight-fraction peer-id (:qset state)) [0 1])))

(def membership (->FbaMembership))

(defn missing-qset-hashes
  "The quorum-set hashes referenced by `statements` that we cannot resolve.

  This exists because `Membership/quorum?` can say `:unknown` but cannot say
  what it is waiting for."
  [state statements]
  (into #{}
        (comp (map statement-qset-hash)
              (remove nil?)
              (remove (:known-qsets state)))
        statements))

;; ============================================================
;; Federated voting (`Slot.cpp:340-376`)
;;
;; Two primitives over the SAME machinery, called with three different
;; predicates. This is what §4 means by "a predicate, not a count".
;; ============================================================

(defn federated-accept
  "`accept(a)`: a v-blocking set already accepts `a`, OR a quorum containing me
  has each voted-or-accepted `a`.

  The first clause is the one that makes federated voting work at all. A node
  that voted AGAINST `a` can still accept it, because a v-blocking set of its
  own slices has accepted -- a plain quorum rule can never switch such a node,
  and the protocol would deadlock.

  Note the v-blocking clause is local and therefore always decidable, so a node
  that cannot resolve anybody's quorum set can still be dragged forward by its
  own slices."
  [state statements voted? accepted?]
  (if (node/v-blocking? membership state statements accepted?)
    true
    (node/quorum? membership state statements #(or (accepted? %) (voted? %)))))

(defn federated-ratify
  "`confirm(a)`: a quorum containing me has each ACCEPTED `a`."
  [state statements accepted?]
  (node/quorum? membership state statements accepted?))

(defn- decided-true?
  "Federated voting is tri-state; `:unknown` must never be read as yes.

  Getting this backwards is the safety bug this file could most easily have
  had, so it is a named function rather than a `(= true ...)` scattered around."
  [r]
  (true? r))

;; ============================================================
;; Ballots
;; ============================================================

(def ^:private max-counter
  "Stands in for stellar-core's `UINT32_MAX`: the counter of the notional
  ballot a CONFIRM or EXTERNALIZE statement vouches for."
  4294967295)

(defn ballot [counter value] {:counter counter :value value})

(defn compatible?
  "Same value. Ballot ordering is by counter first, so two ballots can be
  ordered and still be about different values -- which is the whole reason `p`
  and `p'` both exist."
  [b1 b2]
  (= (:value b1) (:value b2)))

(defn compare-ballots
  "Total order on ballots, nil lowest.

  Values are compared through `canonical` so the order is identical on both
  platforms; a deployment with structured values should supply comparable ids."
  [b1 b2]
  (cond
    (and (nil? b1) (nil? b2)) 0
    (nil? b1) -1
    (nil? b2) 1
    :else (let [c (compare (:counter b1) (:counter b2))]
            (if (zero? c)
              (compare (canonical (:value b1)) (canonical (:value b2)))
              c))))

(defn- less-and-compatible? [b1 b2]
  (and (<= (compare-ballots b1 b2) 0) (compatible? b1 b2)))

(defn- less-and-incompatible? [b1 b2]
  (and (<= (compare-ballots b1 b2) 0) (not (compatible? b1 b2))))

;; ============================================================
;; Statements
;;
;; Four kinds. NOMINATE lives in its own tally (`mLatestNominations`); the three
;; ballot kinds share one (`mLatestEnvelopes`), because a node's ballot state
;; advances monotonically through them.
;; ============================================================

(defn- stmt-value
  "The value a ballot statement is working on."
  [st]
  (case (:kind st)
    :prepare (:value (:ballot st))
    :confirm (:value (:ballot st))
    :externalize (:value (:commit st))
    nil))

(def max-nomination-values
  "A hard cap on the values one nomination statement may carry, in the same
  spirit as `max-qset-nodes` and for the same reason.

  `nomination-rule` runs `federated-accept` ONCE PER DISTINCT VALUE, and each
  of those is two greatest fixpoints over `survivors` plus a `v-blocking?`
  walk. The sanity check required only that a statement carry SOME value, so a
  single message with a million of them bought a million fixpoints, inside
  `step`, on the event loop -- and the whole thing sits inside `settle`'s own
  200-iteration fixpoint.

  Generous against any honest node: a nomination set grows by at most one value
  per nominating peer per round, so this is far above what a real slot
  produces, and a statement above it is refused rather than truncated. Dropping
  values would silently change which of them federated voting could accept,
  which is a correctness change smuggled in as a resource bound."
  256)

(defn statement-sane?
  "`BallotProtocol.cpp:249-311` / `NominationProtocol.cpp:102-113`.

  A Byzantine peer can send anything; a malformed statement must be dropped
  before it reaches the voting rules, not asserted against."
  [st]
  (case (:kind st)
    :nominate (let [n (+ (count (:votes st)) (count (:accepted st)))]
                (and (pos? n) (<= n max-nomination-values)))
    :prepare (let [{:keys [ballot prepared prepared-prime n-c n-h]} st
                   n-c (or n-c 0), n-h (or n-h 0)]
               (and (pos? (:counter ballot 0))
                    (or (nil? prepared) (nil? prepared-prime)
                        (less-and-incompatible? prepared-prime prepared))
                    (or (zero? n-h) (and prepared (<= n-h (:counter prepared))))
                    (or (zero? n-c)
                        (and (not (zero? n-h))
                             (>= (:counter ballot) n-h)
                             (>= n-h n-c)))))
    :confirm (let [{:keys [ballot n-h n-commit]} st]
               (and (pos? (:counter ballot 0))
                    (<= (or n-h 0) (:counter ballot))
                    (<= (or n-commit 0) (or n-h 0))))
    :externalize (and (pos? (:counter (:commit st) 0))
                      (>= (or (:n-h st) 0) (:counter (:commit st))))
    false))

(def ^:private ballot-kind-order {:prepare 0 :confirm 1 :externalize 2})

(defn newer-ballot-statement?
  "The total order of `BallotProtocol.cpp:54-131`: kind first, then (b,p,p',h).

  Keeping only the newest per sender is not an optimisation. A Byzantine node
  that could get an OLD statement counted alongside its newest one would be
  voting twice, which is the federated equivalent of the duplicate-sender bug
  `node/distinct-voters` exists to prevent."
  [old new]
  (if (nil? old)
    true
    (let [ko (ballot-kind-order (:kind old)) kn (ballot-kind-order (:kind new))]
      (cond
        (not= ko kn) (< ko kn)
        (= :externalize (:kind new)) false
        (= :confirm (:kind new))
        (let [c (compare-ballots (:ballot old) (:ballot new))]
          (cond (neg? c) true
                (pos? c) false
                (not= (:n-prepared old) (:n-prepared new))
                (< (or (:n-prepared old) 0) (or (:n-prepared new) 0))
                :else (< (or (:n-h old) 0) (or (:n-h new) 0))))
        :else
        (let [c (compare-ballots (:ballot old) (:ballot new))]
          (if (not= 0 c)
            (neg? c)
            (let [c (compare-ballots (:prepared old) (:prepared new))]
              (if (not= 0 c)
                (neg? c)
                (let [c (compare-ballots (:prepared-prime old) (:prepared-prime new))]
                  (if (not= 0 c)
                    (neg? c)
                    (< (or (:n-h old) 0) (or (:n-h new) 0))))))))))))

(defn newer-nomination?
  "`NominationProtocol.cpp:82-101`: newer iff both sets grew (or stayed) and one
  strictly grew. A nomination statement is monotone by construction, so a
  shrinking one is a lie."
  [old new]
  (if (nil? old)
    true
    (let [ov (set (:votes old)) nv (set (:votes new))
          oa (set (:accepted old)) na (set (:accepted new))]
      (and (every? nv ov) (every? na oa)
           (or (> (count nv) (count ov)) (> (count na) (count oa)))))))

;; ============================================================
;; Ballot predicates
;;
;; Each is a `(fn [stmt] boolean)` handed to federated voting. Reading them
;; against `BallotProtocol.cpp` is the fastest way to check this file.
;; ============================================================

(defn- voted-prepared?
  "Is the sender VOTING to prepare `b`? (`attemptPreparedAccept`'s first lambda)"
  [b st]
  (case (:kind st)
    :prepare (less-and-compatible? b (:ballot st))
    :confirm (compatible? b (:ballot st))
    :externalize (compatible? b (:commit st))
    false))

(defn- accepted-prepared?
  "Has the sender ACCEPTED `b` as prepared? (`hasPreparedBallot`,
  `BallotProtocol.cpp:1479-1516`)"
  [b st]
  (case (:kind st)
    :prepare (or (and (:prepared st) (less-and-compatible? b (:prepared st)))
                 (and (:prepared-prime st)
                      (less-and-compatible? b (:prepared-prime st))))
    :confirm (less-and-compatible? b (ballot (or (:n-prepared st) 0)
                                             (:value (:ballot st))))
    :externalize (compatible? b (:commit st))
    false))

(defn- voted-commit?
  "Is the sender voting to commit `b` over the counter interval [lo hi]?
  (`attemptAcceptCommit`'s first lambda)"
  [b [lo hi] st]
  (case (:kind st)
    :prepare (let [n-c (or (:n-c st) 0)]
               (and (compatible? b (:ballot st))
                    (not (zero? n-c))
                    (<= n-c lo)
                    (<= hi (or (:n-h st) 0))))
    :confirm (and (compatible? b (:ballot st)) (<= (or (:n-commit st) 0) lo))
    :externalize (and (compatible? b (:commit st))
                      (<= (:counter (:commit st)) lo))
    false))

(defn- accepted-commit?
  "Has the sender ACCEPTED commit of `b` over [lo hi]? (`commitPredicate`,
  `BallotProtocol.cpp:970-1002`)

  Note PREPARE never accepts a commit -- `nC` is a VOTE. That asymmetry with
  `voted-commit?` is the crux of the phase change and is easy to get wrong."
  [b [lo hi] st]
  (case (:kind st)
    :prepare false
    :confirm (and (compatible? b (:ballot st))
                  (<= (or (:n-commit st) 0) lo)
                  (<= hi (or (:n-h st) 0)))
    :externalize (and (compatible? b (:commit st))
                      (<= (:counter (:commit st)) lo))
    false))

;; ============================================================
;; State
;; ============================================================

(def default-config
  {:nomination-timeout 4   ; ticks per nomination round, times the round number
   :ballot-timeout 4       ; ticks per ballot counter, times the counter
   :timeout-cap 8          ; stellar-core caps the linear growth; so do we
   :qset-reply-limit 64
   :qset-reply-bytes 1048576
   :gossip-interval 12})   ; re-broadcast, so a lost statement is not fatal

(defn- ballot-statements
  "Every node's latest ballot statement, INCLUDING my own.

  My own is DERIVED from my state rather than fed back through a mailbox the
  way stellar-core does it (`emitCurrentStateStatement` -> `processEnvelope`
  with `self = true`). Deriving it cannot go stale, and it removes the one
  genuinely re-entrant path in the reference implementation."
  [st]
  (let [own (:own-ballot st)]
    (cond-> (:ballot-latest st) own (assoc (:id st) own))))

(defn- nomination-statements [st]
  (let [own (:own-nomination st)]
    (cond-> (:nom-latest st) own (assoc (:id st) own))))

(defn- own-ballot-statement
  "The PREPARE / CONFIRM / EXTERNALIZE statement my current state implies
  (`createStatement`, `BallotProtocol.cpp:508-570`).

  Available with `b = 0` when `b` is unset, and that is not a detail. The
  previous version returned nil there, on the reasoning that stellar-core
  allows itself an internal b = 0 but never emits it. The first half is right
  and the second conflates two things the reference keeps apart: `canEmit`
  (`BallotProtocol.cpp:594`) gates only `emitEnvelope` at `:605`, while
  `processEnvelope(envelope, true)` at `:603` RECORDS the statement
  unconditionally -- and `isStatementSane`'s `self || counter > 0` (`:259-260`)
  exists precisely to admit it.

  Dropping it from the tally as well as from the wire strands the node. A node
  that has accepted a ballot as prepared but not yet adopted a current ballot
  is then invisible to its own federated ratification, so whenever the online
  members of a slice number exactly `threshold - 1` it can never confirm
  anything and nothing re-triggers it. `emitted?` is what keeps it off the
  wire."
  [st]
  (let [b (or (:b st) {:counter 0 :value (:value st)})]
    (let [base {:from (:id st) :slot (:slot st) :qset-hash (:qset-hash st)
                ;; False exactly when stellar-core's `canEmit` is false. The
                ;; statement still counts in our own tally; it just never goes
                ;; on the wire. See `statement-effects`.
                :emitted? (some? (:b st))}]
      (case (:phase st)
        :prepare (merge base {:kind :prepare
                              :ballot b
                              :prepared (:p st)
                              :prepared-prime (:pp st)
                              :n-c (or (some-> (:c st) :counter) 0)
                              :n-h (or (some-> (:h st) :counter) 0)})
        :confirm (merge base {:kind :confirm
                              :ballot b
                              :n-prepared (:counter (:p st))
                              :n-commit (:counter (:c st))
                              :n-h (:counter (:h st))})
        :externalize (merge base {:kind :externalize
                                  :commit (:c st)
                                  :n-h (:counter (:h st))})))))

(defn- own-nomination-statement [st]
  (when (or (seq (:nom-votes st)) (seq (:nom-accepted st)))
    {:kind :nominate :from (:id st) :slot (:slot st) :qset-hash (:qset-hash st)
     :votes (:nom-votes st) :accepted (:nom-accepted st)}))

(defn- refresh-own
  "Recompute the two derived self-statements. Called after every state change so
  the tallies always include an up-to-date me."
  [st]
  (assoc st
         :own-ballot (own-ballot-statement st)
         :own-nomination (own-nomination-statement st)))

;; ============================================================
;; Nomination (`NominationProtocol.cpp`)
;;
;; No safety obligation whatsoever: nomination may produce any values at all and
;; the ballot protocol still cannot break agreement. Its only job is to STOP
;; churning, which it does because votes are monotone and the leader set grows.
;; ============================================================

(defn- hash-node [st priority? n]
  (content-hash (canonical [(:slot st) (:prev-value st) priority?
                            (:nom-round st) n])))

(defn- node-priority
  "`getNodePriority`: zero unless a first hash falls under the node's weight,
  in which case a second hash. Weighting the lottery by trust is what makes a
  widely-trusted node likely to lead."
  [st n]
  ;; Self belongs to the nomination lottery even when our explicit trust
  ;; expression lists only other validators. Preserve explicit weights.
  (let [[num den] (or (node-weight-fraction n (:qset st))
                      (if (= n (:id st)) [1 1] [0 1]))]
    (if (< (* (hash-node st false n) den) (* 4294967296 num))
      (hash-node st true n)
      0)))

(defn- update-round-leaders
  "Leaders for this round, ACCUMULATED across rounds.

  The 2017 checkout clears `mRoundLeaders` first; current stellar-core does not,
  and the accumulation is what the convergence argument needs -- with a fixed
  leader set a partitioned leader stalls nomination forever, whereas a growing
  one eventually contains a node everybody can hear."
  [st]
  (let [nodes (sort-by pr-str (conj (qset-nodes (:qset st)) (:id st)))
        prios (mapv (fn [n] [n (node-priority st n)]) nodes)
        top (reduce max 0 (map second prios))]
    (if (pos? top)
      (update st :nom-leaders into (map first (filter #(= top (second %)) prios)))
      st)))

(defn- new-value-from-nomination
  "The highest-hashing value in a leader's statement that we have not voted for
  (`getNewValueFromNomination`). Hash-ordered rather than value-ordered so that
  no node can make its own value win by naming it cleverly."
  [st nom]
  (let [seen (:nom-votes st)
        cands (remove seen (concat (:votes nom) (:accepted nom)))]
    (when (seq cands)
      (->> cands
           (sort-by (fn [v] [(content-hash (canonical [(:slot st) (:prev-value st)
                                                       (:nom-round st) v]))
                             (canonical v)]))
           last))))

(defn- combine-candidates
  "`combineCandidates` is application-defined; stellar-core merges transaction
  sets. Anything deterministic is safe -- nomination has no safety obligation --
  so the default is the smallest by canonical form."
  [st]
  (let [f (or (:combine-fn st) (fn [cs] (first (sort-by canonical cs))))]
    (f (:nom-candidates st))))

(declare bump-state)

(defn- nominate
  "One nomination round (`NominationProtocol.cpp:431-505`).

  A round that times out before nomination ever started is a no-op, which is how
  a node that has nothing to propose stays quiet."
  [st timed-out?]
  (if (and timed-out? (not (:nom-started? st)))
    st
    (let [st (-> st
                 (assoc :nom-started? true)
                 (update :nom-round inc)
                 update-round-leaders)
          leaders (:nom-leaders st)
          st (if (contains? leaders (:id st))
               (cond-> st (:value st) (update :nom-votes conj (:value st)))
               (reduce (fn [s l]
                         (if-let [nom (get (:nom-latest s) l)]
                           (if-let [nv (new-value-from-nomination s nom)]
                             (update s :nom-votes conj nv)
                             s)
                           s))
                       st
                       (sort-by pr-str leaders)))]
      (refresh-own st))))

(defn- nomination-rule
  "Promote votes to accepted, accepted to candidates, and follow leaders.

  Runs inside the fixpoint: accepting a value can complete a ratification for
  it in the same breath, and a new candidate starts the ballot protocol."
  [st]
  (when (:nom-started? st)
    (let [stmts (vals (nomination-statements st))
          accepted (:nom-accepted st)
          ;; (1) vote -> accept
          to-accept (->> stmts
                         (mapcat :votes)
                         distinct
                         (remove accepted)
                         (filter (fn [v]
                                   (decided-true?
                                    (federated-accept st stmts
                                                      #(contains? (set (:votes %)) v)
                                                      #(contains? (set (:accepted %)) v)))))
                         (sort-by canonical))
          st' (reduce (fn [s v] (-> s (update :nom-accepted conj v)
                                    (update :nom-votes conj v)))
                      st to-accept)
          ;; (2) accept -> candidate
          to-cand (->> (:nom-accepted st')
                       (remove (:nom-candidates st'))
                       (filter (fn [v]
                                 (decided-true?
                                  (federated-ratify st' stmts
                                                    #(contains? (set (:accepted %)) v)))))
                       (sort-by canonical))
          st' (reduce (fn [s v] (update s :nom-candidates conj v)) st' to-cand)
          ;; (3) follow the round leaders, but only while still candidate-less
          st' (if (seq (:nom-candidates st'))
                st'
                (reduce (fn [s l]
                          (if-let [nom (get (nomination-statements s) l)]
                            (if-let [nv (new-value-from-nomination s nom)]
                              (update s :nom-votes conj nv)
                              s)
                            s))
                        st'
                        (sort-by pr-str (:nom-leaders st'))))
          st' (refresh-own st')]
      (when (not= st' st)
        ;; A new candidate hands the composite value to the ballot protocol.
        (if (seq to-cand)
          (let [composite (combine-candidates st')]
            (bump-state (assoc st' :composite composite) composite false))
          st')))))

;; ============================================================
;; Ballot protocol (`BallotProtocol.cpp`)
;;
;; State is `b` (current), `p` (prepared), `p'` (prepared prime), `h` (high),
;; `c` (commit), and a phase in PREPARE -> CONFIRM -> EXTERNALIZE.
;; ============================================================

(defn- bump-to-ballot [st b]
  ;; Clearing `:heard-from-quorum?` is `BallotProtocol.cpp:475`, and without it
  ;; the flag means "have I EVER heard from a quorum" rather than "at this
  ;; counter". That is precisely what `handle-timer`'s own comment says the gate
  ;; prevents: a node that hears from a quorum at counter 1 and is then
  ;; partitioned away would otherwise bump its counter on every ballot timeout
  ;; for the rest of the run, which is the counter-to-infinity race the gate
  ;; exists to stop.
  (assoc st :b b :heard-from-quorum? false))

(defn- update-current-if-needed
  "`updateCurrentIfNeeded`: b must never trail h."
  [st]
  (if (or (nil? (:b st)) (neg? (compare-ballots (:b st) (:h st))))
    (bump-to-ballot st (:h st))
    st))

(defn- update-current-value
  "`updateCurrentValue`: move b to `b'`, refusing a move that would contradict a
  commit we have already accepted."
  [st b']
  (cond
    (not (#{:prepare :confirm} (:phase st))) nil
    (nil? (:b st)) (bump-to-ballot st b')
    (and (:c st) (not (compatible? (:c st) b'))) nil
    (neg? (compare-ballots (:b st) b')) (bump-to-ballot st b')
    ;; A smaller ballot is either a bug or a peer not following the protocol;
    ;; stellar-core logs an error and refuses. So do we.
    :else nil))

(defn bump-state
  "`bumpState(value, n)`: move to counter `n`, keeping h's value if we have one.

  Keeping `h`'s value is the rule that makes counter bumps safe: once we have
  confirmed a ballot prepared we may raise the counter forever but may never
  change the value underneath it."
  [st value n-or-force]
  (let [n (if (integer? n-or-force)
            n-or-force
            (inc (or (some-> (:b st) :counter) 0)))]
    (if (and (not (integer? n-or-force)) (not n-or-force) (:b st))
      st
      (let [v (if (:h st) (:value (:h st)) value)]
        (if (nil? v)
          st
          (or (some-> (update-current-value st (ballot n v)) refresh-own) st))))))

(defn- abandon-ballot
  "`abandonBallot`: give up on the current ballot and move to counter `n`
  (or the next one). Uses the latest composite candidate if there is one."
  [st n]
  (let [v (or (:composite st) (some-> (:b st) :value))]
    (if (nil? v)
      st
      (if (zero? n) (bump-state st v true) (bump-state st v n)))))

(defn- candidate-ballots
  "Every ballot any statement could let us accept as prepared.

  stellar-core derives these from the `hint` statement that triggered the
  transition (`getPrepareCandidates`); we take the union over all statements,
  which is the union over all possible hints."
  [st]
  (into #{}
        (mapcat (fn [s]
                  (case (:kind s)
                    :prepare (keep identity [(:ballot s) (:prepared s) (:prepared-prime s)])
                    :confirm [(ballot (or (:n-prepared s) 0) (:value (:ballot s)))
                              (ballot max-counter (:value (:ballot s)))]
                    :externalize [(ballot max-counter (:value (:commit s)))]
                    nil)))
        (vals (ballot-statements st))))

(defn- set-prepared
  "`setPrepared`: slot `b` into p, demoting the old p into p' when it is
  incompatible. Returns nil if nothing moved."
  [st b]
  (let [p (:p st) pp (:pp st)]
    (cond
      (nil? p) (assoc st :p b)
      (neg? (compare-ballots p b))
      (cond-> (assoc st :p b) (not (compatible? p b)) (assoc :pp p))
      (pos? (compare-ballots p b))
      (when (or (nil? pp) (neg? (compare-ballots pp b)))
        (assoc st :pp b))
      :else nil)))

(defn- rule-prepared-accept
  "PREPARE-accept (`attemptPreparedAccept`): accept a ballot as prepared."
  [st]
  (when (#{:prepare :confirm} (:phase st))
    (let [stmts (vals (ballot-statements st))]
      (some
       (fn [b]
         (when-not (or (and (:pp st) (<= (compare-ballots b (:pp st)) 0))
                       (and (:p st) (less-and-compatible? b (:p st)))
                       (and (= :confirm (:phase st))
                            (not (less-and-compatible? (:p st) b))))
           (when (decided-true?
                  (federated-accept st stmts #(voted-prepared? b %) #(accepted-prepared? b %)))
             (when-let [st' (set-prepared st b)]
               ;; Accepting a higher, incompatible ballot as prepared can
               ;; invalidate a commit we were voting for.
               (let [st' (if (and (:c st') (:h st')
                                  (or (and (:p st') (less-and-incompatible? (:h st') (:p st')))
                                      (and (:pp st') (less-and-incompatible? (:h st') (:pp st')))))
                           (assoc st' :c nil)
                           st')]
                 (refresh-own st'))))))
       ;; Highest first, as stellar-core does: a higher prepared ballot
       ;; subsumes the ones below it.
       (reverse (sort compare-ballots (candidate-ballots st)))))))

(defn- rule-prepared-confirmed
  "PREPARE-confirm (`attemptPreparedConfirmed`): raise h, and possibly set c.

  `c` is only set when nothing we have prepared contradicts `h`; that guard is
  step (3) of the paper and is what stops a node voting to commit a value it has
  already seen outvoted."
  [st]
  (when (and (= :prepare (:phase st)) (:p st))
    (let [stmts (vals (ballot-statements st))
          cands (vec (reverse (sort compare-ballots (candidate-ballots st))))
          ;; Highest ratified-prepared ballot above the current h.
          [new-h idx] (loop [i 0]
                        (if (>= i (count cands))
                          [nil nil]
                          (let [b (nth cands i)]
                            (if (and (:h st) (>= (compare-ballots (:h st) b) 0))
                              [nil nil]
                              (if (decided-true?
                                   (federated-ratify st stmts #(accepted-prepared? b %)))
                                [b i]
                                (recur (inc i)))))))]
      (when new-h
        (let [new-c (when (and (nil? (:c st))
                               (or (nil? (:p st))
                                   (not (less-and-incompatible? new-h (:p st))))
                               (or (nil? (:pp st))
                                   (not (less-and-incompatible? new-h (:pp st)))))
                      ;; Walk DOWN from h while ratification holds; the lowest
                      ;; such ballot is c.
                      (loop [i idx, best nil]
                        (if (>= i (count cands))
                          best
                          (let [b (nth cands i)]
                            (if (neg? (compare-ballots b (:b st)))
                              best
                              (if (decided-true?
                                   (federated-ratify st stmts #(accepted-prepared? b %)))
                                (recur (inc i) b)
                                best))))))
              st' (cond-> st
                    (or (nil? (:h st)) (pos? (compare-ballots new-h (:h st))))
                    (assoc :h new-h)
                    new-c (assoc :c new-c))]
          (when (not= st' st)
            (refresh-own (update-current-if-needed st'))))))))

(defn- commit-boundaries
  "The counters worth testing as interval endpoints
  (`getCommitBoundariesFromStatements`). Only values other nodes have actually
  named can matter, so the search is finite."
  [st value]
  (into (sorted-set)
        (mapcat (fn [s]
                  (case (:kind s)
                    :prepare (when (and (= value (stmt-value s)) (pos? (or (:n-c s) 0)))
                               [(:n-c s) (:n-h s)])
                    :confirm (when (= value (stmt-value s))
                               [(or (:n-commit s) 0) (or (:n-h s) 0)])
                    :externalize (when (= value (stmt-value s))
                                   [(:counter (:commit s)) (or (:n-h s) 0) max-counter])
                    nil)))
        (vals (ballot-statements st))))

(defn- find-extended-interval
  "`findExtendedInterval`: the widest [lo hi] satisfying `pred`, found by first
  fixing the top boundary and then pushing the bottom down."
  [boundaries pred]
  (loop [bs (reverse (seq boundaries)), cand nil]
    (if (empty? bs)
      cand
      (let [b (first bs)
            cur (cond (nil? cand) [b b]
                      (> b (second cand)) nil
                      :else [b (second cand)])]
        (cond
          (nil? cur) (recur (rest bs) cand)
          (pred cur) (recur (rest bs) cur)
          (some? cand) cand
          :else (recur (rest bs) cand))))))

(defn- rule-accept-commit
  "COMMIT-accept (`attemptAcceptCommit`): move PREPARE -> CONFIRM.

  This is the phase change, and the point at which the node has committed
  itself: from here it may raise counters but never change value."
  [st]
  (when (#{:prepare :confirm} (:phase st))
    (let [stmts (vals (ballot-statements st))
          values (->> stmts
                      (keep (fn [s]
                              (case (:kind s)
                                :prepare (when (pos? (or (:n-c s) 0)) (stmt-value s))
                                (stmt-value s))))
                      distinct
                      (sort-by canonical))]
      (some
       (fn [value]
         (when-not (and (= :confirm (:phase st)) (not= value (:value (:h st))))
           (let [bs (commit-boundaries st value)
                 b (ballot 0 value)
                 cand (when (seq bs)
                        (find-extended-interval
                         bs
                         (fn [iv]
                           (decided-true?
                            (federated-accept st stmts
                                              #(voted-commit? b iv %)
                                              #(accepted-commit? b iv %))))))]
             (when (and cand (pos? (first cand))
                        (or (not= :confirm (:phase st))
                            (> (second cand) (:counter (:h st)))))
               (let [c (ballot (first cand) value)
                     h (ballot (second cand) value)
                     st' (assoc st :c c :h h)
                     st' (if (= :prepare (:phase st'))
                           (-> st'
                               (assoc :phase :confirm :pp nil)
                               (as-> s (if (and (:b s) (not (less-and-compatible? h (:b s))))
                                         (bump-to-ballot s h)
                                         s)))
                           st')]
                 (when (not= st' st)
                   (refresh-own (update-current-if-needed st'))))))))
       values))))

(defn- rule-confirm-commit
  "COMMIT-confirm (`attemptConfirmCommit`): EXTERNALIZE. Irrevocable."
  [st]
  (when (and (= :confirm (:phase st)) (:h st) (:c st))
    (let [stmts (vals (ballot-statements st))
          value (:value (:c st))
          b (ballot 0 value)
          bs (commit-boundaries st value)
          cand (when (seq bs)
                 (find-extended-interval
                  bs
                  (fn [iv]
                    (decided-true?
                     (federated-ratify st stmts #(accepted-commit? b iv %))))))]
      (when (and cand (pos? (first cand)))
        (-> st
            (assoc :c (ballot (first cand) value)
                   :h (ballot (second cand) value))
            update-current-if-needed
            (assoc :phase :externalize
                   :nom-started? false
                   :externalized value)
            refresh-own)))))

(defn- rule-bump
  "`attemptBump`: adopt the smallest counter that a v-blocking set has already
  passed.

  This is the liveness rule, and it is v-blocking rather than quorum-based
  precisely because it must work when a quorum cannot be assembled -- which is
  the situation it exists to escape. Ordered LAST so it only fires once the
  safety rules are quiescent.

  ONE DIVERGENCE from `BallotProtocol.cpp:1334-1339`, and it is deliberate.
  stellar-core iterates the counters in ascending order and does
  `if (n < targetCounter) break;` -- so a single peer sitting at a counter BELOW
  ours aborts the whole scan on its first iteration and the node never bumps.
  Counters below ours are simply not candidates to move up to, so we skip them
  and carry on. The paper's rule (`draft-mazieres-dinrg-scp-05` §5.4) is `the
  lowest counter greater than mine at which the blocking set is no longer
  ahead`, which is what skipping computes and what breaking does not."
  [st]
  (when (#{:prepare :confirm} (:phase st))
    (let [stmts (vals (ballot-statements st))
          counters (into (sorted-set)
                         (map (fn [s]
                                (case (:kind s)
                                  :prepare (:counter (:ballot s))
                                  :confirm (:counter (:ballot s))
                                  :externalize max-counter)))
                         stmts)
          target (or (some-> (:b st) :counter) 0)
          counters (conj counters target)]
      (loop [cs (seq counters)]
        (when cs
          (let [n (first cs)]
            (if (< n target)
              (recur (rest cs))
              (let [vb (v-blocking? (:qset st)
                                    (into #{}
                                          (comp (filter (fn [s]
                                                          (case (:kind s)
                                                            :prepare (< n (:counter (:ballot s)))
                                                            :confirm (< n (:counter (:ballot s)))
                                                            :externalize (not= n max-counter)
                                                            false)))
                                                (map :from))
                                          stmts))]
                (cond
                  (= n target) (when vb (recur (rest cs)))
                  vb (recur (rest cs))
                  :else (let [st' (abandon-ballot st n)]
                          (when (not= st' st) st')))))))))))

;; ============================================================
;; The fixpoint
;;
;; `node/fixpoint` is genuinely load-bearing here and this is the only algorithm
;; in the library for which that is true. One arriving EXTERNALIZE statement can
;; walk a node all the way from "nothing prepared" to "externalized" -- accept
;; prepared, confirm prepared, accept commit, confirm commit -- and each step is
;; only unlocked by the previous one having landed. One-transition-per-event
;; cannot express it.
;;
;; The ORDER is normative (`advanceSlot`, `BallotProtocol.cpp:1835-1850`). We
;; apply the FIRST rule that fires and then restart from the top, which is
;; strictly closer to the paper than stellar-core's `a() || b() || c()` chain.
;; ============================================================

(def ^:private rules
  [nomination-rule
   rule-prepared-accept
   rule-prepared-confirmed
   rule-accept-commit
   rule-confirm-commit
   rule-bump])

(defn- rule-step
  "One pass: the first rule that changes anything wins.

  Returns `{:state :effects}` because that is `node/fixpoint`'s contract. The
  effects are always empty -- see the PR: SCP wants a fixpoint over STATE and
  derives its messages from the final state, because the reference
  implementation's own `sendLatestEnvelope` consolidates whatever the recursion
  produced into one envelope anyway. `fixpoint`'s effect accumulation would emit
  every intermediate statement."
  [st]
  {:state (or (some (fn [r]
                      (let [st' (r st)]
                        (when (and st' (not= st' st))
                          ;; Counting passes is safe inside a fixpoint precisely
                          ;; because it only moves when something else already
                          ;; did. It is how a test can show the fixpoint is
                          ;; load-bearing rather than assert that it is.
                          (update st' :rule-passes inc))))
                    rules)
              st)
   :effects []})

(defn check-invariants
  "`BallotProtocol::checkInvariants` (`BallotProtocol.cpp:624-656`), throwing.

  stellar-core runs this on every state change under `dbgAssert`. It is a
  SELF-CHECK on the ballot state rather than a protocol rule -- nothing here is
  reachable from a well-behaved transition, which is exactly why it is worth
  running: it catches the transition that is not well-behaved, at the point it
  happens rather than three rounds later when the externalized value is wrong.

  `dbgAssert` compiles out of stellar's release builds. This does not, because
  the cost is six comparisons on a state machine that already runs a fixpoint of
  eleven rules, and because a check compiled out of the build that matters is a
  check you do not have."
  [st]
  (let [{:keys [b p pp h c phase]} st
        bad (fn [why data] (throw (ex-info (str "SCP invariant violated: " why)
                                           (merge {:phase phase} data))))]
    (when (and b (zero? (:counter b)))
      (bad "current ballot has counter 0" {:b b}))
    (when (and p pp (not (less-and-incompatible? pp p)))
      (bad "p' must be less than and incompatible with p" {:p p :pp pp}))
    (when c
      (when-not b (bad "c is set with no current ballot" {:c c}))
      (when-not (and h (less-and-compatible? c h))
        (bad "c must be <= h and compatible" {:c c :h h}))
      (when-not (and b (less-and-compatible? h b))
        (bad "h must be <= b and compatible" {:h h :b b})))
    (case phase
      :prepare nil
      :confirm (when-not c (bad "CONFIRM without c" {}))
      :externalize (do (when-not c (bad "EXTERNALIZE without c" {}))
                       (when-not h (bad "EXTERNALIZE without h" {})))
      (bad "unknown phase" {}))
    st))

(defn- settle [st]
  ;; Checked after the fixpoint, which is where stellar checks it -- every rule
  ;; that fired has had its say and the state is at rest.
  (check-invariants (:state (node/fixpoint rule-step st 200))))

;; ============================================================
;; Effects, derived from state
;; ============================================================

(defn- timer-generations
  "What each timer should currently be set for. Emitting a `set-timer` only when
  a generation CHANGES keeps timer arming idempotent inside a fixpoint."
  [st]
  {:nomination (when (:nom-started? st) (:nom-round st))
   :ballot (some-> (:b st) :counter)
   :gossip (:gossip-seq st)})

(defn- timeout-for [st base n]
  (* base (min (max 1 n) (:timeout-cap st))))

(defn- timer-effects [st]
  (let [want (timer-generations st)
        have (:armed st)]
    [(assoc st :armed want)
     (into []
           (keep (fn [[k g]]
                   (when (and g (not= g (get have k)))
                     (case k
                       :nomination (node/set-timer :nomination
                                                   (timeout-for st (:nomination-timeout st) g))
                       :ballot (node/set-timer :ballot
                                               (timeout-for st (:ballot-timeout st) g))
                       :gossip (node/set-timer :gossip (:gossip-interval st))))))
           (sort-by (comp str key) want))]))

(defn- statement-effects
  "Broadcast my statements when they change, behind the durability barrier.

  §3's rule -- gate exactly the messages that constitute this node's binding
  commitment -- makes the whole of SCP's ballot state a binding commitment: a
  node that forgot it had accepted a commit could externalize a contradictory
  value after a restart. So `b/p/p'/h/c/phase` is written and the broadcast
  rides in `:then`. Nomination is not binding (nomination has no safety
  obligation) but travels in the same write, which costs nothing.

  `gated` are effects that must not escape before the same write lands --
  currently the `:commit`. `finish` used to concatenate the commit BEFORE this,
  so the application was told a value had externalized while the state
  justifying it was still in flight; crash in that window and the node came
  back in `:prepare` having already exposed a decision. stellar-core has the
  opposite order: `setConfirmCommit` emits the statement first
  (`BallotProtocol.cpp:1469`) and only then calls `valueExternalized`
  (`:1473`), and `HerderImpl::persistSCPState` (`HerderImpl.cpp:865`) runs
  before the broadcast at `:867`.

  A gossip tick replays only a current statement whose own persistence token
  completed (or whose envelope was read from disk). A local commit always
  travels with the write that records its supporting state."
  [st gated]
  (let [nom (:own-nomination st)
        bal (:own-ballot st)
        nom-new? (and nom (not= nom (:sent-nomination st)))
        ;; `:emitted? false` is stellar-core's `canEmit` being false: the
        ;; statement counts in our own tally but must not go on the wire.
        bal-new? (and bal (:emitted? bal) (not= bal (:sent-ballot st)))
        msgs (cond-> []
               nom-new? (conj (node/broadcast :scp nom))
               bal-new? (conj (node/broadcast :scp bal)))
        ;; Each statement has its own barrier. A pending ballot must not
        ;; block replay of a durable nomination, or escape with it.
        replay (cond-> []
                 (and (:gossip? st) nom (= nom (:durable-nomination st)))
                 (conj (node/broadcast :scp nom))
                 (and (:gossip? st) bal (= bal (:durable-ballot st)))
                 (conj (node/broadcast :scp bal)))
        st (dissoc st :gossip?)]
    (if (and (empty? msgs) (empty? gated))
      [st replay]
      (let [token [:scp (:write-seq st)]
            st (cond-> (update st :write-seq inc)
                 nom-new? (assoc :sent-nomination nom :nomination-token token)
                 bal-new? (assoc :sent-ballot bal :ballot-token token))
            saved (select-keys st [:slot :phase :b :p :pp :h :c :nom-votes :nom-accepted
                                   :nom-candidates :composite :prev-value :value
                                   :sent-nomination :sent-ballot])]
        [st (conj replay (node/persist-then {:writes {:scp saved}
                                             :durable? true :epoch (:slot st) :token token
                                             :then (into msgs gated)}))]))))

(defn- fetch-effects
  "Ask for quorum sets we cannot resolve.

  Unicast to the node that referenced the hash, because that node certainly has
  it. Deduplicated through `:requested`, and re-issued on the gossip timer so a
  lost request is not permanent."
  [st]
  (let [stmts (concat (vals (:ballot-latest st)) (vals (:nom-latest st)))
        wanted (into {}
                     (comp (remove #(contains? (:known-qsets st) (:qset-hash %)))
                           (map (juxt :qset-hash :from)))
                     stmts)
        new (remove #(contains? (:requested st) (key %)) wanted)]
    [(update st :requested into (map key) new)
     (mapv (fn [[h from]] (node/send-to from {:kind :get-qset :hash h}))
           (sort-by (comp str key) new))]))

(defn- commit-effects
  "Externalizing commits, once."
  [st]
  (if (and (:externalized st) (not (:committed? st)))
    [(assoc st :committed? true)
     [(node/commit [(:externalized st)])]]
    [st []]))

(defn- finish
  "Turn settled state into effects. Every effect here is a FUNCTION of the state
  and of what was last sent, so running the fixpoint longer cannot duplicate
  one."
  [st logs]
  (let [[st commits] (commit-effects st)
        ;; The commit rides in the write's `:then` rather than ahead of it.
        [st fx2] (statement-effects st commits)
        [st fx3] (fetch-effects st)
        [st fx4] (timer-effects st)]
    (node/result st (concat logs fx2 fx3 fx4))))

;; ============================================================
;; Input handling
;; ============================================================

(defn- record-statement
  "Ingest a peer's statement, newest-wins.

  `from` is who actually SENT this -- the verified peer id from the network
  edge -- and it must equal the `:from` the statement claims. It did not used
  to be passed at all: the statement was filed under the body's own claim about
  its author and never compared with the sender.

  That is a quorum forged from one connection. A single peer sends n statements,
  naming each validator of our quorum slice in turn, and `quorum?` counts n
  distinct authors agreeing. Federated voting's entire safety argument is that
  a slice cannot be satisfied without genuinely distinct nodes; this let one
  node satisfy any slice by itself.

  Independent of transport authentication -- it breaks with a perfect wire too,
  because the check that was missing is not whether the sender is who they say,
  but whether the AUTHOR is the sender. Bullshark does this correctly at both
  of its ingest points; SCP was the one that was missed.

  A statement for another slot is dropped. Catch-up is out of scope and is the
  same gap Tendermint reported; see the PR."
  [st from stmt]
  (cond
    (not= from (:from stmt)) st
    (not= (:slot stmt) (:slot st)) st
    (not (statement-sane? stmt)) st
    (= :nominate (:kind stmt))
    (if (newer-nomination? (get-in st [:nom-latest (:from stmt)]) stmt)
      (assoc-in st [:nom-latest (:from stmt)] stmt)
      st)
    :else
    (if (newer-ballot-statement? (get-in st [:ballot-latest (:from stmt)]) stmt)
      (assoc-in st [:ballot-latest (:from stmt)] stmt)
      st)))

(defn- handle-message [st from msg]
  (case (:kind msg)
    ;; Trust is directional. Serve our own advertised preimage to an
    ;; authenticated requester, once per peer and within a shared budget.
    :get-qset
    (let [size (:qset-response-size st)
          served (:qset-served st)]
      (if (and (= (:hash msg) (:qset-hash st))
               (not (contains? served from))
               (< (count served) (:qset-reply-limit st))
               (<= (* (inc (count served)) size) (:qset-reply-bytes st)))
        (-> st
            (update :qset-served conj from)
            (update :replies (fnil conj [])
                    (node/send-to from {:kind :qset :hash (:qset-hash st) :qset (:qset st)})))
        st))

    ;; Only a qset we ASKED for.
    ;;
    ;; `:requested` was already tracked and already `disj`'d here -- the
    ;; membership test was simply never made, so any peer could push unlimited
    ;; quorum sets into `:known-qsets`, each up to `max-qset-nodes` entries, and
    ;; nothing ever removed them. One message per entry, permanent, on every
    ;; node that received it; and `:get-qset` then re-served them, so the cache
    ;; an attacker filled was also the payload of the amplifier above.
    ;;
    ;; The content-addressing check below is about a DIFFERENT attack -- a
    ;; forged preimage for a hash we wanted -- and does nothing about volume,
    ;; because an attacker computing hashes of its own quorum sets satisfies it
    ;; every time.
    :qset (if (and (contains? (:requested st) (:hash msg))
                   (valid-qset? (:qset msg))
                   (= (:hash msg) (qset-hash (:qset msg))))
            ;; Content-addressed and CHECKED. Skipping this check would let a
            ;; Byzantine peer answer a fetch with a quorum set of its choosing
            ;; and so manufacture a quorum for us out of nothing.
            (-> st
                (assoc-in [:known-qsets (:hash msg)] (:qset msg))
                (update :requested disj (:hash msg)))
            st)
    (record-statement st from msg)))

(defn- handle-timer [st timer-id]
  (case timer-id
    :nomination (if (:externalized st) st (nominate st true))
    ;; stellar-core will not abandon a ballot until it has heard from a quorum
    ;; at this counter -- otherwise a node alone on a partition would race its
    ;; counter to infinity.
    :ballot (if (and (:b st) (:heard-from-quorum? st))
              (abandon-ballot st 0)
              ;; Suppressed -- but the timer must be RE-ARMED, or it is gone for
              ;; good. `timer-effects` emits a `set-timer` only when the ballot
              ;; generation (the counter) changes, and the interpreter has
              ;; already removed the timer that just fired; returning `st`
              ;; unchanged therefore killed the ballot timer permanently at this
              ;; counter, even once a quorum was later heard from. stellar-core
              ;; re-arms in exactly this branch
              ;; (`ballotProtocolTimerExpired` -> `startBallotProtocolTimer`,
              ;; `BallotProtocol.cpp:502-504`). Forgetting what we armed makes
              ;; the generation look changed, which re-arms it.
              (update st :armed dissoc :ballot))
    :gossip (update st :gossip-seq inc)
    st))

(defn- update-heard-from-quorum
  "`advanceSlot`'s pre-check: have I heard from a quorum at my current counter?"
  [st]
  (if (or (:heard-from-quorum? st) (nil? (:b st)))
    st
    (let [stmts (vals (ballot-statements st))
          r (node/quorum? membership st stmts
                          (fn [s] (if (= :prepare (:kind s))
                                    (<= (:counter (:b st)) (:counter (:ballot s)))
                                    true)))]
      (cond-> st (decided-true? r) (assoc :heard-from-quorum? true)))))

(defn- transition [st input]
  (let [st (assoc st :replies [])
        st (case (:type input)
             ;; A message whose sender we did not VERIFY is dropped, as
             ;; Tendermint and Bullshark already drop theirs. `verified-by` is
             ;; the set of peers whose signature was checked at the edge; under
             ;; `:auth :none` it is empty, so an unauthenticated deployment
             ;; visibly refuses to make progress rather than quietly trusting a
             ;; self-declared name.
             :message-received (if (contains? (:verified-by input) (:from input))
                                 (handle-message st (:from input) (:msg input))
                                 st)
             :timer-fired (let [st (handle-timer st (:timer-id input))]
                            (cond-> st (= :gossip (:timer-id input))
                                    (assoc :gossip? true :requested #{} :qset-served #{})))
             :value-ready (-> st (assoc :value (:value input)) (nominate false))
             :persisted (let [token (:token input)]
                          (cond-> st
                            (and (= (:epoch input) (:slot st)) token (= token (:nomination-token st)))
                            (assoc :durable-nomination (:sent-nomination st) :nomination-token nil)
                            (and (= (:epoch input) (:slot st)) token (= token (:ballot-token st)))
                            (assoc :durable-ballot (:sent-ballot st) :ballot-token nil)))
             st)
        replies (:replies st)
        st (-> st refresh-own settle update-heard-from-quorum)]
    (finish (dissoc st :replies) replies)))

;; ============================================================
;; The node
;; ============================================================

(defn- initial-state [config]
  (let [cfg (merge default-config config)
        qset (:qset cfg)]
    (when-not (valid-qset? qset)
      (throw (ex-info "scp needs a valid :qset in config -- trust is per-node and subjective, a flat :validators list cannot express it"
                      {:peer-id (:peer-id cfg) :qset qset})))
    (let [h (qset-hash qset)
          restored (get-in cfg [:restored :durable :scp])]
      (refresh-own
       (merge
        {:id (:peer-id cfg)
         :qset qset
         :qset-hash h
         :qset-served #{}
         :qset-response-size (alength (wire/signing-bytes {:kind :qset :hash h :qset qset}))
         :qset-reply-limit (:qset-reply-limit cfg)
         :qset-reply-bytes (:qset-reply-bytes cfg)
         ;; Our own quorum set is always resolvable; peers' are not, and
         ;; `:qsets` lets a test pre-seed the cache to isolate fetching.
         :known-qsets (merge {h qset}
                             (into {} (map (fn [q] [(qset-hash q) q])) (vals (:qsets cfg)))
                             (into {} (map (fn [q] [(qset-hash q) q])) (:known-qsets cfg)))
         :requested #{}
         :slot (:slot cfg 0)
         :value (:value cfg)
         :prev-value (:prev-value cfg :genesis)
         :combine-fn (:combine-fn cfg)
         :nom-started? false
         :nom-round 0
         :nom-votes #{} :nom-accepted #{} :nom-candidates #{}
         :nom-latest {} :nom-leaders #{}
         :composite nil
         :phase :prepare
         :b nil :p nil :pp nil :h nil :c nil
         :ballot-latest {}
         :heard-from-quorum? false
         :externalized nil
         :committed? false
         :armed {}
         :rule-passes 0
         :gossip-seq 0
         :write-seq 0
         :sent-nomination (:sent-nomination restored)
         :sent-ballot (:sent-ballot restored)
         :durable-nomination (:sent-nomination restored)
         :durable-ballot (:sent-ballot restored)
         :nomination-timeout (:nomination-timeout cfg)
         :ballot-timeout (:ballot-timeout cfg)
         :timeout-cap (:timeout-cap cfg)
         :gossip-interval (:gossip-interval cfg)}
        ;; A restart resumes from durable state only. Anything not written --
        ;; other nodes' statements, in particular -- is genuinely lost, and the
        ;; node re-learns it from the gossip timer.
        (select-keys (or restored {})
                     [:slot :phase :b :p :pp :h :c :nom-votes :nom-accepted
                      :nom-candidates :composite :prev-value :value]))))))

(defrecord Scp []
  node/Node

  (capabilities [_]
    ;; Federated Byzantine agreement. Final, but conditionally: the guarantee
    ;; holds between INTERTWINED nodes, and a befouled node may externalize
    ;; whatever it likes. That is an assumption a consumer reasons with rather
    ;; than code it must have, so it does not appear here -- only revocability
    ;; does, and SCP never revokes.
    ;; `:resync` is emitted only on restart, to re-announce a value this node
    ;; had already externalized. SCP never REVOKES, so `:revert` is absent.
    {:emits #{:broadcast :send :persist-then :set-timer :cancel-timer
              :commit :resync :log}
     :topics #{:scp}})

  (init [_ config]
    (let [st (initial-state config)
          ;; `:externalized` and `:committed?` are NOT in the persisted key set,
          ;; and neither can be: they record what the APPLICATION was told,
          ;; which no amount of our own state establishes. But `phase` and `:c`
          ;; ARE persisted, and in `:externalize` they say exactly which value
          ;; was decided -- so the decision is recoverable even though the
          ;; delivery is not.
          ;;
          ;; Without this a node that crashed after the write landed but before
          ;; the `:commit` reached the application came back in `:externalize`,
          ;; re-broadcast its EXTERNALIZE to peers, and never told its own
          ;; application anything at all -- the decision visible to the network
          ;; and absent from the machine that had to act on it.
          restored-value (when (= :externalize (:phase st)) (:value (:c st)))
          st (cond-> st
               restored-value (assoc :externalized restored-value :committed? true)
               ;; A node with nothing to propose stays silent until the
               ;; application hands it a value; one configured with a value
               ;; starts nomination round 1 immediately.
               (and (nil? restored-value) (:value st)) (nominate false))
          st (assoc st :gossip-seq 1)]
      (finish (settle st)
              (cond-> [(node/log-effect :info (str "scp " (:id st) " slot " (:slot st)
                                                   " qset " (:qset-hash st)))]
                ;; `resync`, not `commit`: this is a restarting node stating
                ;; what its committed prefix is, not extending it. Emitting a
                ;; `commit` would hand the application a second copy of a value
                ;; it may already hold.
                restored-value (conj (node/resync [restored-value]))))))

  (step [_ state input] (transition state input)))

(defn make [] (->Scp))

;; ============================================================
;; Inspection helpers for tests and runtimes
;; ============================================================

(defn externalized
  "The value this node externalized, or nil."
  [st]
  (:externalized st))

(defn phase [st] (:phase st))

(defn ballot-state
  "`[b p p' h c]` -- the five ballot variables, for assertions and traces."
  [st]
  [(:b st) (:p st) (:pp st) (:h st) (:c st)])

(defn candidates [st] (:nom-candidates st))

(defn rule-passes
  "How many rule applications this node has run in total.

  The gap across one `step` is how many transitions that single event unlocked.
  A one-transition-per-event machine can only ever move it by one."
  [st]
  (:rule-passes st))

(defn intertwined?
  "Small-network oracle for quorum intersection. With `faulty` supplied, every
  pair of quorums must share a node outside that set. Returns false when no
  quorum exists. Enumeration is exponential and limited to sixteen nodes."
  ([qsets] (intertwined? qsets #{}))
  ([qsets faulty]
   (let [nodes (vec (keys qsets))
         universe (set nodes)]
     (when (> (count nodes) 16)
       (throw (ex-info "quorum intersection oracle supports up to 16 nodes" {:nodes (count nodes)})))
     (boolean
      (and (seq (survivors universe qsets false))
           (every?
            (fn [mask]
              (let [q (into #{} (keep-indexed (fn [i n] (when (bit-test mask i) n))) nodes)]
                (or (not-every? #(quorum-slice? (qsets %) q) q)
                    ;; A second quorum sharing no honest member of q must
                    ;; survive entirely inside this complement.
                    (empty? (survivors (set/difference universe (set/difference q faulty))
                                       qsets false)))))
            (range 1 (bit-shift-left 1 (count nodes)))))))))
