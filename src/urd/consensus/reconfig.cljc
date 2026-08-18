(ns urd.consensus.reconfig
  "Validator set changes: the part that is the same for every algorithm.

  Written after reading four reference implementations (CometBFT/tendermint-go,
  etcd-raft, Narwhal, stellar-core). They gave four different answers, and this
  namespace is deliberately only the intersection.

  ## What generalises, and what does not

  A set change decomposes into a TRIGGER, a TRANSITION, and an ACTIVATION.

  The trigger generalises completely: a decided value may carry updates, so the
  decision about who is a validator is made by the same consensus that orders
  everything else. Every reference that supports the feature does it this way,
  including Narwhal -- whose epoch predicate is a pure function of the committed
  sequence even though nothing else about its mechanism generalises.

  The transition is this namespace: `(config, updates) -> config'`, pure and
  total. Also common to all of them.

  The ACTIVATION does not generalise, and pretending otherwise would be the
  error. It stays with each algorithm:

    Tendermint  +2 heights. The offset decomposes -- one is forced, because a
                header is built from PRE-execution state, so the result of
                deciding H cannot appear in H's own header; the second buys
                pre-commitment, letting a light client verify adjacent headers
                by hash chain alone. N=1 suffices without light clients.
    Raft        at APPLY, with at most one update un-applied at a time. etcd
                measures that against `applied`, not `committed`, because its
                active config is its applied config and applied trails commit
                by an unbounded amount. Where decide == apply -- which is urd's
                case, `step` being pure and its state BEING the applied state
                -- the two-phase joint transition collapses to two consecutive
                decisions at a fixed offset.
    Bullshark   NOT THIS MECHANISM. `order-anchors` re-derives who led
                HISTORICAL rounds using the CURRENT committee, so a change
                silently rewrites which anchors led the past. Narwhal resolves
                this by destroying the DAG and rebuilding from a new genesis.
                Epochs, or certificates carrying a committee digest -- a
                different protocol, not a configuration of this one.
    SCP         NOT APPLICABLE. There is no agreed set: a quorum set is local
                configuration, nodes are designed to disagree, and in
                stellar-core the only mutator is dead code with zero callers.

  ## Why a sparse diff rather than a whole set

  Both chain references use a diff -- CometBFT's `ValidatorUpdate{pub_key,
  power}` with power 0 meaning remove, etcd's `ConfChangeSingle`. A whole-set
  replacement is easier to validate and loses something worth keeping: with a
  diff, two proposals that touch different validators are visibly independent,
  and the application says what it MEANT rather than what it computed.

  The cost is that a diff can be invalid in ways a replacement cannot -- naming
  a validator twice, removing one that is not there, emptying the set -- so
  every one of those is checked below and named.

  ## Order independence is a SAFETY property, not tidiness

  CometBFT issue #3181: proposer selection depended on the ORDER of updates in
  the ABCI response, so two honest nodes given identical input computed
  different proposer priorities. The fix (`cce4d21cc`, consensus-breaking) was
  to treat updates as a SET.

  That is the single most important thing to get right here, because the
  failure is silent and the input is identical on both nodes -- no message is
  lost, nothing is malformed, and the two simply disagree about who proposes
  next. `apply-updates` therefore canonicalises before doing anything, and
  `same-result-whatever-the-order` in the tests drives it.

  ## Rejection must be deterministic, and it is the CALLER's to act on

  Every function here returns data. An invalid update yields `{:error ...}`
  rather than throwing, because what to do about it is an algorithm-level
  decision with two defensible answers -- halt (CometBFT panics, and since the
  input is identical everywhere all nodes halt identically, which is a stall
  rather than a fork) or skip. What is NOT defensible is for two nodes to
  classify the same update differently, so validity here depends on nothing but
  the config and the updates.

  etcd learned the harder version of this: validating at PROPOSE time, against
  whatever config happened to be active, caused real data corruption in
  CockroachDB because the basis was not stable. Hence `DisableConfChangeValidation`
  and the caveat that the checks are best-effort. Validation here is a function
  of the config the update is applied TO, which is the stable basis."
  (:require [urd.consensus.proposer :as proposer]))

(def max-total-power
  "Ceiling on the total voting power of a validator set.

  CometBFT uses `MaxInt64 / 8` (`types/validator_set.go:27`) and the reason is
  NOT a BFT one -- it is arithmetic headroom, so that the proposer-priority
  accumulator cannot overflow while priorities are incremented and re-centred.
  Their own comment says as much: \"prevent clipping in
  incrementProposerPriority\" and \"let (diff+diffMax-1) not overflow\".

  Reproduced here for the same reason and no other. urd's priorities live in
  the same accumulator (`urd.consensus.proposer`), so they need the same room.
  Kept well below the platform maximum because ClojureScript numbers are
  doubles: exact integer arithmetic holds only to 2^53, and a cap chosen from
  the JVM's `Long/MAX_VALUE` would be silently wrong under cljs -- the same
  class of trap that made `rng.cljc` mask to 32 bits and made the anti-replay
  window in `auth.cljc` a set rather than a bitmap."
  ;; Written as a literal, not as (long (/ (Math/pow 2 40) 8)):  does
  ;; not exist in ClojureScript, and Math/pow returns a double on both
  ;; platforms. 2^37 is exact under a double, so both readers get the same
  ;; value -- which is the whole reason for writing it out.
  137438953472)

(defn- canonical
  "Updates as a SET: last mention of an id wins, then sorted by id.

  Both halves matter. Deduplication is not merely defensive -- see the
  namespace docstring on CometBFT #3181, where order dependence made two honest
  nodes disagree about the proposer. Sorting makes the result independent of
  the order the application happened to emit, which is the property that stops
  the disagreement.

  `str` on the id because validator ids are keywords or uuids depending on the
  deployment, and neither sorts against the other."
  [updates]
  (->> updates
       (reduce (fn [m u] (assoc m (:id u) u)) {})
       vals
       (sort-by (comp str :id))
       vec))

(defn validate
  "Check `updates` against `config`. Returns nil when they are applicable, or a
  map describing the first problem.

  A function of the config the updates are applied TO and nothing else, so two
  nodes cannot classify the same update differently. See the namespace
  docstring on etcd's CockroachDB corruption for what happens when the basis is
  not stable.

  `config` is `{:validators [id ...] :powers {id power}}`."
  [config updates]
  (let [{:keys [validators powers]} config
        vset (set validators)
        us (canonical updates)]
    (or
     (when-let [bad (first (remove #(and (int? (:power %)) (not (neg? (:power %)))) us))]
       {:error :negative-or-non-integer-power :update bad})

     ;; Removing something that is not there is a sign the application and the
     ;; consensus state disagree about the set, which is worth surfacing rather
     ;; than treating as a no-op. CometBFT: "failed to find validator %X to
     ;; remove".
     (when-let [bad (first (filter #(and (zero? (:power %))
                                         (not (contains? vset (:id %))))
                                   us))]
       {:error :remove-unknown-validator :update bad})

     ;; The duplicate case cannot be observed after `canonical` collapses it,
     ;; so it is checked on the RAW input. A caller that sends the same id
     ;; twice with different powers has a bug, and silently picking one is how
     ;; the two nodes end up disagreeing.
     (let [ids (map :id updates)
           dups (->> ids frequencies (keep (fn [[k n]] (when (> n 1) k))) vec)]
       (when (seq dups) {:error :duplicate-update :ids dups}))

     (let [after (reduce (fn [m {:keys [id power]}]
                           (if (zero? power) (dissoc m id) (assoc m id power)))
                         (select-keys powers validators)
                         us)]
       (or
        (when (empty? after) {:error :would-empty-the-validator-set})
        (when (> (reduce + 0 (vals after)) max-total-power)
          {:error :total-power-exceeded
           :total (reduce + 0 (vals after)) :max max-total-power}))))))

(defn apply-updates
  "Apply `updates` to `config`, returning a new config or `{:error ...}`.

  `config` is `{:validators [id ...] :powers {id power} :priorities {id p}}`.
  Priorities are optional; when absent they are not computed.

  Pure and total: the same config and the same updates give the same result on
  every node, in any order the application emitted them.

  A validator that JOINS is given `-(P + P>>3)` where P is the resulting total
  power, following CometBFT `validator_set.go:543-550`. That is not cosmetic --
  without it a fresh validator proposes immediately, and worse, a validator
  could unbond and rebond to clear a negative priority. See
  `proposer/new-validator-priority`, which also documents where the reference's
  arithmetic quietly disagrees with its own comment.

  A validator that LEAVES loses its priority outright. Keeping it would let a
  validator bank priority while absent."
  [config updates]
  (or (validate config updates)
      (let [{:keys [validators powers priorities]} config
            us (canonical updates)
            vset (set validators)
            powers' (reduce (fn [m {:keys [id power]}]
                              (if (zero? power) (dissoc m id) (assoc m id power)))
                            (select-keys powers validators)
                            us)
            validators' (vec (sort-by str (keys powers')))
            joining (remove vset validators')
            total' (reduce + 0 (vals powers'))]
        (cond-> {:validators validators' :powers powers'}
          priorities
          (assoc :priorities
                 (let [kept (select-keys priorities validators')
                       new-p (proposer/new-validator-priority total')]
                   (reduce (fn [m id] (assoc m id new-p)) kept joining)))))))

(defn changed?
  "Did `updates` actually change anything about `config`?

  An update that sets a validator to the power it already has is legal and is a
  no-op, and an algorithm should not pay the cost of a transition for one."
  [config updates]
  (let [after (apply-updates config updates)]
    (and (not (:error after))
         (or (not= (set (:validators config)) (set (:validators after)))
             (not= (select-keys (:powers config) (:validators config))
                   (:powers after))))))

(defn single-voter-change?
  "Does applying `updates` to `config` change the membership by at most ONE?

  Raft's original mechanism (thesis S4.1) and etcd's `Changer.Simple`
  (`confchange.go:140-143`, \"more than one voter changed without entering
  joint config\"). A configuration differing by one voter always has majorities
  intersecting its predecessor's, which is the entire safety argument for
  changing membership without joint consensus.

  Counts MEMBERSHIP changes, not power changes: re-weighting an existing
  validator does not alter who is in the set, so the intersection argument is
  untouched by it. etcd has no notion of power at all, so this is a place where
  the reference cannot answer the question for us -- CometBFT, which does have
  power, imposes no such restriction because it never uses this mechanism.

  A no-op counts as zero, so `changed?` and this agree about doing nothing."
  [config updates]
  (let [after (apply-updates config updates)]
    (and (not (:error after))
         (let [before (set (:validators config))
               now (set (:validators after))]
           (<= (+ (count (remove now before)) (count (remove before now))) 1)))))
