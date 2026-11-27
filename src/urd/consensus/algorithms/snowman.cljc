(ns urd.consensus.algorithms.snowman
  "Snowman: leaderless consensus by repeated sampling, on urd's core protocol.

  This exists to stress the OPPOSITE corner of the protocol from Raft. Where
  Raft is leader-based, log-structured, quorum-decided and absolutely final,
  Snowman is leaderless, chain-structured, SAMPLE-decided and only
  probabilistically final. If one protocol expresses both cleanly, the
  generality claim has evidence; if not, we learn where it breaks.

  ## How it decides

  There is no quorum. A node repeatedly samples k peers, asks each for its
  current preference, and feeds the tally into a Snowball instance. Confidence
  accumulates only on CONSECUTIVE successful polls, so a network that keeps
  flip-flopping never finalizes -- and one that has tipped past the metastable
  point converges fast. Safety is probabilistic, parameterised by k, alpha, beta
  and the Byzantine fraction; it is not enforced by the code, and this
  implementation does not pretend otherwise.

  ## Where the instances live, and why it matters

  **One instance per PARENT, arbitrating among its children.** This is
  `snowman_block.go:22-44`, where the instance is a field of the block and
  `AddChild` adds each new child as one of its choices; `topological.go:517`
  votes into `parentBlock.sb`.

  What that instance IS, is the next section. This one is about the PLACEMENT,
  which is the part that was a safety bug.

  It is worth stating why, because the obvious alternative -- one instance per
  candidate block, keyed by and voting for itself -- looks equivalent and is
  not. Snowflake's entire safety argument is that confidence counts CONSECUTIVE
  successes, enforced by `nnary_snowflake.go:66-68`: a poll whose winner differs
  from the current preference zeroes confidence before incrementing. That flip
  is only visible to an instance that can see both siblings. Give each block its
  own instance and the flip never happens, no instance ever holds more than one
  choice, and confidence in a losing sibling is never cleared -- so two honest
  nodes seeing the alternating tallies X, Y, X, Y, X and Y, X, Y, X, Y both
  reach beta and accept CONFLICTING blocks. Alternating tallies are the expected
  outcome of a split preference, not a contrived one. The consecutive-poll
  invariant this namespace advertises has to be enforced at the layer that
  accepts blocks, or it is not enforced at all.

  Two consequences follow from getting the PLACEMENT right:

  - **Vote bubbling is transitive.** A chit for a deep block is a vote for every
    block on the path from the last accepted block down to it, each counted in
    its own parent's instance (`topological.go:362-427` does this with a Kahn
    sort; the path walk below is the same relation computed per chit).
  - **Preference is the TIP.** After recording a poll we walk down the preferred
    branch to a leaf (`topological.go:296-311`), rather than leaving preference
    at the child of the last accepted block -- which would cap the chain at one
    block per round.

  ## Which instance, of the three avalanchego has

  `:variant` selects it and defaults to `:tree`, which is what a running node
  uses: `chains/manager.go:933` and `:1358` build `Topological{Factory:
  SnowflakeFactory}`, and `snowman_block.go:39` hands that factory to
  `snowball.NewTree`.

      :tree            NewTree(SnowflakeFactory)   -- production
      :flat-snowflake  NewFlat(SnowflakeFactory)
      :flat-snowball   NewFlat(SnowballFactory)    -- the published algorithm

  The flat variants are kept because the papers are stated in Snowball's terms
  and a library covering this family should be able to express them. Neither is
  what any chain runs; `NewFlat` has no non-test caller anywhere in avalanchego.

  The Tree is not an optimization of the flat form, which is how the design doc
  had it filed. `Flat.RecordPoll` feeds one n-ary instance the PLURALITY choice
  and its count; the Tree feeds each of its nodes every vote that reached it, so
  votes for two siblings combine at every node above the bit where their ids
  diverge. Three children where two share a leading bit the third lacks: a
  split between the two still eliminates the third, on evidence the flat form
  discards as a sub-alpha plurality. See `snowtree`.

  Block ids stay whatever the application calls them. The Tree needs
  fixed-width bits, so `choice-key` derives them with `hasch/uuid` rather than
  constraining the vertex contract.

  ## What it revealed about the core protocol

  1. `Membership` does NOT apply. Snowman never asks \"is this set a quorum of
     the validators?\" -- it asks \"did alpha of my k SAMPLED peers agree?\". The
     `Membership` protocol is therefore optional, not universal, and a runtime
     must not require it. Documented in the design as a correction.

  2. `:sample` returning a BAG is load-bearing, and would have been easy to get
     wrong. Weight is drawn without replacement, so one peer can appear several
     times and its multiplicity IS its vote weight. The multiplicity belongs to
     the REQUEST, not to the peer: several polls are in flight at once and a
     peer's weight differs between them, so storing it in one global map lets
     one poll's tally exceed k.

  3. Probabilistic finality still maps onto `:commit` without `:revert`.
     Preference flips freely BEFORE finalization, but a finalized decision is
     never revoked -- so Snowman needs the revocable API less than Raft does,
     which is a pleasing inversion of the usual intuition."
  (:require [clojure.string :as str]
            [urd.consensus.node :as n]
            [urd.consensus.algorithms.snowflake :as sf]
            [urd.consensus.algorithms.snowtree :as st]
            [hasch.core :as hasch]
            [urd.wire :as wire]
            [urd.crypto :as crypto]))

(defn block-id
  "SHA-256 of the canonical CBOR block fields excluding :id. This is the
  default identity check for blocks fetched from other validators."
  [block]
  (crypto/bytes->hex (hasch/sha256 (wire/signing-bytes (dissoc block :id)))))

;; ============================================================
;; The polling instance
;;
;; `:variant` selects which of avalanchego's three shapes a parent's instance
;; is. `:tree` is the default because it is what a running node uses:
;; `chains/manager.go:933` builds `Topological{Factory: SnowflakeFactory}` and
;; `snowman_block.go:39` calls `snowball.NewTree` with it.
;;
;;   :tree            NewTree(SnowflakeFactory)  -- production
;;   :flat-snowflake  NewFlat(SnowflakeFactory)
;;   :flat-snowball   NewFlat(SnowballFactory)   -- the published algorithm
;;
;; The two flat variants are kept because a library covering this family should
;; be able to express them and because the papers are stated in Snowball's
;; terms. Neither is what any chain runs. See `snowflake`'s docstring.
;; ============================================================

(defn choice-key
  "The bit key the Tree indexes a choice by.

  Block ids here are whatever the application calls them -- a keyword in the
  tests, a hash in a deployment -- and the Tree needs fixed-width bits. So the
  key is derived rather than required: `hasch/uuid` is content-addressed,
  synchronous on both platforms, and already how Bullshark identifies
  certificates. 32 hex characters, 128 bits.

  A caller therefore keeps its own ids and never sees a digest, and no
  constraint leaks into the vertex contract to buy this."
  [choice]
  (str/replace (str (hasch/uuid choice)) "-" ""))

(def variants
  "The three shapes, and the only accepted values of `:variant`."
  #{:tree :flat-snowflake :flat-snowball})

(defn- variant [params] (:variant params :tree))

(defn- instance-key [params choice]
  (if (= :avalanche (:tree-key-mode params))
    (st/avalanche-key choice)
    (choice-key choice)))

(defn- instance-new [params choice]
  (case (variant params)
    :tree (st/tree params choice (instance-key params choice))
    :flat-snowflake (sf/snowflake params choice)
    :flat-snowball (sf/snowball params choice)))

(defn- instance-add
  "Offer a further choice to an existing instance -- `sb.Add(childID)` in
  `AddChild` (`snowman_block.go:43`).

  A no-op for the flat variants, whose n-ary instance accepts any choice
  implicitly. NOT a no-op for the Tree, which has to split a node to make room
  for it, and forgetting this call would leave every sibling after the first
  invisible to the poll."
  [inst params choice]
  (case (variant params)
    :tree (st/tree-add inst choice (instance-key params choice))
    inst))

(defn- instance-record-poll
  "Feed one poll's per-child votes in.

  The flat variants reduce the bag to its plurality first, which is
  `Flat.RecordPoll` (`flat.go:29-33`) exactly. The Tree takes the whole bag,
  which is the entire difference between them."
  [inst params child-votes]
  (case (variant params)
    :tree (st/tree-record-poll inst child-votes)
    (let [[choice votes] (apply max-key val child-votes)]
      (case (variant params)
        :flat-snowflake (sf/snowflake-record-poll inst votes choice)
        :flat-snowball (sf/snowball-record-poll inst votes choice)))))

(defn- instance-unsuccessful [inst params]
  (case (variant params)
    :tree (st/tree-record-unsuccessful-poll inst)
    :flat-snowflake (sf/snowflake-record-unsuccessful-poll inst)
    :flat-snowball (update inst :snowflake sf/snowflake-record-unsuccessful-poll)))

(defn- instance-preference [inst params]
  (case (variant params)
    :tree (st/tree-preference inst)
    :flat-snowflake (:preference inst)
    :flat-snowball (sf/snowball-preference inst)))

(defn- instance-finalized? [inst params]
  (case (variant params)
    :tree (st/tree-finalized? inst)
    :flat-snowflake (:finalized? inst)
    :flat-snowball (sf/finalized? inst)))

;; ============================================================
;; Block tree
;; ============================================================

(defn- add-one
  "Insert a block into the tree. Blocks are {:id :parent :height}.

  Adding a child creates its PARENT's snowball instance if there is none, which
  is `snowman_block.go:32-44`: the instance is initialised preferring the first
  child added, and later children join it as alternatives. Initialising it from
  the first poll winner instead would silently prefer whatever happened to win a
  poll that did not clear alpha-preference."
  [state {:keys [id parent] :as blk}]
  (cond
    (get-in state [:blocks id]) state
    (contains? (:rejected state) id) state           ; a rejected subtree stays rejected

    ;; The parent's slot is already decided: this block is a sibling of one we
    ;; accepted, arriving late. Accepting is absorbing, so it can never win --
    ;; admitting it would only leak a Snowball instance under a parent nothing
    ;; will ever poll again.
    (or (contains? (:rejected state) parent)
        (and (contains? (:accepted state) parent)
             (not= parent (:last-accepted state))))
    (-> state (update :orphans dissoc id) (update :rejected conj id))

    (nil? (get-in state [:blocks parent]))
    ;; Unknown parent. Hold it rather than drop it: blocks reach us over a
    ;; reordering network, so a child arriving before its parent is ordinary,
    ;; and dropping it would strand the whole branch permanently.
    (assoc-in state [:orphans id] blk)

    (not= (:height blk) (inc (get-in state [:blocks parent :height])))
    (update state :orphans dissoc id)

    :else
    (-> state
        (update :orphans dissoc id)
        (assoc-in [:blocks id] blk)
        (update-in [:children parent] (fnil conj #{}) id)
        (update-in [:snowballs parent]
                   (fn [inst]
                     (if inst
                       ;; A SIBLING. `AddChild` calls `sb.Add(childID)` here,
                       ;; and the Tree needs it -- see `instance-add`.
                       (instance-add inst (:params state) id)
                       (instance-new (:params state) id)))))))

(defn- add-block
  "Insert `blk`, then keep re-offering the held orphans until none lands."
  [state blk]
  (loop [st (add-one state blk)]
    (let [st' (reduce add-one st (vals (:orphans st)))]
      (if (= (:blocks st') (:blocks st))
        st'
        (recur st')))))

(defn- resolve-path
  "Walk from `id` up to `stop`, reporting WHY the walk failed.

  Returns `{:path [...]}` root-first, or `{:missing id}` when the walk reached
  a block we do not hold, or nil when `stop` is simply not an ancestor.

  The distinction is the whole point and `path-below` did not draw it: both
  cases returned nil, so a chit naming a block we had never seen was discarded
  exactly like a chit for a rejected branch. The first means ASK SOMEONE; the
  second means ignore. Conflating them stranded a node permanently -- it was
  polled every round, received chits naming blocks its peers demonstrably held,
  and had no way to request one. avalanchego `SendGet`s the block from the peer
  that chitted it (`engine.go:709-722`) and schedules the vote against it
  (`:396-415`)."
  [state id stop]
  (loop [cur id, acc (), visited #{}]
    (cond
      (= cur stop) {:path (vec acc)}
      (nil? cur) nil
      (contains? visited cur) nil
      (contains? (:rejected state) cur) nil
      :else (if-let [block (or (get-in state [:blocks cur]) (get-in state [:orphans cur]))]
              (recur (:parent block) (conj acc cur) (conj visited cur))
              {:missing cur}))))

(defn- path-below
  "The ids from `stop` (exclusive) down to `id` (inclusive), root-first, or nil."
  [state id stop]
  (:path (resolve-path state id stop)))

(defn- reject-subtree
  "Drop `id` and everything under it: a rejected block can never be accepted, so
  keeping its accumulated confidence around would let a later chit for a
  descendant resurrect it (`rejectTransitively`, `topological.go:670-700`)."
  [state id]
  (loop [st state, frontier [id]]
    (if-let [cur (first frontier)]
      (let [kids (get-in st [:children cur] #{})]
        (recur (-> st
                   (update :blocks dissoc cur)
                   (update :children dissoc cur)
                   (update :snowballs dissoc cur)
                   (update :rejected conj cur))
               (into (vec (rest frontier)) kids)))
      st)))

;; ============================================================
;; Polling
;; ============================================================

(defn- start-poll
  "Emit a sample request; the reply drives the query round."
  [state]
  (let [rid (:next-request state)]
    (n/result (-> state
                  (assoc :next-request (inc rid))
                  (update :polls-run inc)
                  (assoc-in [:outstanding rid] {:issued (inc (:polls-run state))}))
              [(n/set-timer [:poll-expire rid] (:poll-timeout state))
               (assoc-in (n/sample rid (get-in state [:params :k]) :validators) [1 :powers] (:powers state))])))

(defn- bubble
  "Turn chits into per-parent vote counts: {parent {child votes}}.

  Transitive, per the namespace docstring: one chit contributes to every
  instance on the path from the last accepted block down to the block it names.
  `weights` is the sample bag for THIS request, so a peer drawn twice votes
  twice -- and only in the poll that drew it twice."
  [state chits weights]
  (reduce (fn [acc [peer pref]]
            (if-let [path (path-below state pref (:last-accepted state))]
              (let [w (get weights peer 1)]
                (reduce (fn [acc id]
                          (update-in acc [(get-in state [:blocks id :parent]) id]
                                     (fnil + 0) w))
                        acc path))
              acc))
          {}
          chits))

(defn- record-votes
  "Feed each parent's tally into that parent's instance.

  An instance that received NO votes in this poll gets an unsuccessful poll,
  which clears its confidence. avalanchego gets the same effect lazily, by
  marking untouched children `shouldFalter` (`topological.go:558-580`) and
  calling `RecordUnsuccessfulPoll` before the next positive vote lands
  (`:493-500`). Eager is simpler and errs toward NOT finalizing."
  [state by-parent]
  (let [params (:params state)]
    (reduce (fn [st [parent inst]]
              (assoc-in st [:snowballs parent]
                        (if-let [child-votes (get by-parent parent)]
                          (instance-record-poll inst params child-votes)
                          (instance-unsuccessful inst params))))
            state
            (:snowballs state))))

(defn- accept-finalized
  "Accept as far down the chain as the finalized instances allow.

  Returns [state commits]. Sequential: a block is accepted only when its parent
  is the last accepted block, so the committed prefix is always a chain. Each
  acceptance rejects the losing siblings and their subtrees
  (`acceptPreferredChild`, `topological.go:645-665`)."
  [state]
  (loop [st state, accepted []]
    (let [la (:last-accepted st)
          sb (get-in st [:snowballs la])]
      (if-not (and sb (instance-finalized? sb (:params st)))
        [st accepted]
        (let [choice (instance-preference sb (:params st))
              idx (:commit-index st)
              siblings (disj (get-in st [:children la] #{}) choice)
              st (reduce reject-subtree st siblings)
              st (-> st
                     (update :snowballs dissoc la)
                     (update :children dissoc la)
                     (assoc :last-accepted choice)
                     (update :accepted conj choice)
                     (assoc :commit-index (inc idx)))]
          (recur st (conj accepted (get-in st [:blocks choice]))))))))

(defn- preferred-tip
  "Walk down the preferred branch to a leaf (`topological.go:296-311`).

  Leaving preference at the child of the last accepted block -- which is where
  the tally puts it -- would mean every completed poll pulled preference back
  from the tip, capping the chain at one block per round."
  [state]
  (loop [cur (:last-accepted state)]
    (let [inst (get-in state [:snowballs cur])]
      (if inst
        (recur (instance-preference inst (:params state)))
        cur))))

(defn- tally
  "Apply a set of chits and settle the consequences."
  [state chits weights]
  (let [state (record-votes state (bubble state chits weights))
        [state accepted] (accept-finalized state)]
    [(assoc state :preference (preferred-tip state))
     (when (seq accepted)
       [(n/persist-then {:writes {:snowman-root (:root state) :snowman-accepted accepted}
                         :durable? true :epoch 0
                         :then [(n/commit (mapv :id accepted))]})])]))

(defn- bound-dependencies
  "Drop the oldest unresolved replies over the configured age or size bounds."
  [state effects]
  (let [cutoff (- (:polls-run state) (:deferred-ttl state))
        waiting (for [[rid poll] (:outstanding state)
                      peer (sort-by str (keys (:waiting poll)))]
                  [rid peer])
        expired (take-while (fn [[rid _]] (< (get-in state [:outstanding rid :issued]) cutoff))
                            waiting)
        drop-n (max (count expired) (- (count waiting) (:deferred-limit state)))]
    [(reduce (fn [st [rid peer]] (update-in st [:outstanding rid :waiting] dissoc peer))
             state (take drop-n waiting))
     (cond-> (vec effects)
       (pos? drop-n) (conj (n/log-effect :debug {:event :dropped-poll-dependencies
                                                 :count drop-n})))]))

(defn- drain-polls
  "Deliver the longest finished prefix in issuance order (poll/set.go)."
  [state effects]
  (let [[state effects] (bound-dependencies state effects)]
    (loop [st state, fx effects]
      (let [[rid poll] (first (:outstanding st))]
        (if (and (:closed? poll) (empty? (:waiting poll)))
          (let [[st commits] (tally st (:votes poll) (:weights poll))]
            (recur (-> st (update :outstanding dissoc rid) (assoc :last-polled rid))
                   (into (conj fx (n/cancel-timer [:poll-expire rid])) commits)))
          (n/result st fx))))))

(defn- resolve-chit
  "Record a peer's vote once its entire branch connects, or request its missing ancestor."
  [state rid peer]
  (let [pref (get-in state [:outstanding rid :chits peer])
        {:keys [path missing]} (resolve-path state pref (:last-accepted state))
        state (update-in state [:outstanding rid :waiting] dissoc peer)]
    (cond
      path [(assoc-in state [:outstanding rid :votes peer] pref) []]
      missing [(assoc-in state [:outstanding rid :waiting peer] missing)
               [(n/send-to peer {:kind :get-block :id missing})]]
      :else [state []])))

(defn- receive-block
  [state block remote?]
  (if (or (not (map? block)) (nil? (:id block)) (nil? (:parent block))
          (= (:id block) (:parent block))
          (and (= :avalanche (get-in state [:params :tree-key-mode]))
               (nil? (st/avalanche-key (:id block))))
          (not (and (integer? (:height block)) (pos? (:height block))))
          (get-in state [:blocks (:id block)])
          ;; Local vertex inputs come from the application VM. Wire blocks
          ;; must verify against their advertised identity before staging.
          (if-let [verify (:verify-block state)]
            (not (verify block))
            (and remote? (not= (:id block) (block-id block)))))
    (n/result state)
    (let [st (add-block state block)
          waiting (for [[rid poll] (:outstanding st)
                        [peer dep] (:waiting poll)
                        :when (= dep (:id block))]
                    [rid peer])
          [st fx] (reduce (fn [[st fx] [rid peer]]
                            (let [[st asks] (resolve-chit st rid peer)]
                              [st (into fx asks)]))
                          [st []] waiting)]
      (drain-polls (assoc st :preference (preferred-tip st)) (distinct fx)))))

;; ============================================================
;; The node
;; ============================================================

(def default-poll-timeout
  "Ticks a poll waits for its chits before being abandoned.

  A poll that loses one chit must not hang forever: `:outstanding` would grow
  without bound and the node would simply stop polling into its instances.

  On expiry the poll is COMPLETED from the chits that did arrive, not discarded.
  The previous behaviour recorded nothing, and its docstring justified that as
  matching avalanchego -- \"avalanchego likewise drops a poll it cannot complete
  rather than tallying a partial result. Tallying the partial would under-count,
  fail alpha, and clear confidence, so a lossy network could never finalize
  anything.\" Both sentences are contradicted by the source.

  avalanchego never leaves a poll incomplete. Every outstanding query ends in
  `Chits` or `QueryFailed` (`voter.go:47,49`), and both reach `polls.Vote` or
  `polls.Drop`. `Drop` removes the peer from `polled`
  (`early_term_traversal.go:154-156`) -- it does not invalidate the poll -- and
  `Finished` case 1 is `remaining == 0`, i.e. everyone either voted OR was
  dropped (`:167-176`). The partial does not mechanically fail alpha either,
  precisely because the dropped peer leaves `polled`: alpha is measured against
  votes RECEIVED, so a poll clears it with up to `k - alphaPreference`
  non-responses -- five of twenty at production parameters.

  Discarding instead is a permanent halt, not a slowdown. With `k` near `n` --
  avalanchego's own default is K=20 on subnets of about that size -- a single
  unresponsive validator lands in every sample, so every poll expires and
  records nothing, forever. Measured: five validators, k=4, one crashed, and
  the four healthy nodes finalize NOTHING in 600 ticks.

  It is also a safety-argument gap. A round in which the network genuinely
  disagreed (sub-alpha) was erased rather than registering as a failed poll, so
  `beta` counted \"polls where everyone happened to answer\" rather than
  consecutive successful polls."
  12)

(defrecord Snowman []
  n/Node

  (capabilities [_]
    ;; Accepted blocks must survive a crash before their IDs reach the consumer.
    ;;
    ;; No `:revert`, despite finality being PROBABILISTIC. Those are different
    ;; axes: acceptance here is absorbing, so a consumer needs no code for
    ;; revocation even though it needs an assumption about parameters.
    {:emits #{:send :sample :set-timer :cancel-timer :commit :persist-then :resync :log}})

  (init [_ config]
    (let [genesis (or (:genesis config) :genesis)
          params (merge sf/default-params (:params config))]
      (when-not (sf/valid-params? params)
        (throw (ex-info "invalid snowball parameters" {:params params})))
      ;; A misspelt variant must not fall through to a default. The `case`
      ;; forms above would throw anyway, but far from here and with nothing
      ;; naming the cause -- and a silent default would be worse still, since
      ;; the three shapes differ in how much of a poll's evidence they use.
      (when-not (#{:derived :avalanche} (:tree-key-mode params :derived))
        (throw (ex-info "Unknown Snowtree key mode" {:mode (:tree-key-mode params)})))
      (when-not (contains? variants (variant params))
        (throw (ex-info "unknown snowman variant"
                        {:variant (:variant params) :known variants})))
      (let [validators (n/validator-set config)
            powers (or (:powers config) (zipmap validators (repeat 1)))
            _ (when-not (and (= (set validators) (set (keys powers)))
                             (every? #(and (integer? %) (< 0 % 4294967296)) (vals powers))
                             (<= (:k params) (reduce + (vals powers)) 4294967295))
                (throw (ex-info "Snowman needs enough positive validator weight for a full sample"
                                {:k (:k params) :powers powers})))
            restored (:restored config)
            root (or (get-in restored [:durable :snowman-root]) (:accepted-frontier config)
                     {:id genesis :parent nil :height 0})
            _ (when-not (and (some? (:id root)) (integer? (:height root)) (<= 0 (:height root)))
                (throw (ex-info "Invalid Snowman accepted frontier" {:frontier root})))
            history (into [] (mapcat #(get-in % [:writes :snowman-accepted])) (:writes restored))
            blocks (loop [blocks {(:id root) root}, parent root, remaining (seq history)]
                     (if-let [block (first remaining)]
                       (if (and (= (:parent block) (:id parent))
                                (= (:height block) (inc (:height parent)))
                                (some? (:id block)) (not (contains? blocks (:id block))))
                         (recur (assoc blocks (:id block) block) block (next remaining))
                         (throw (ex-info "Broken Snowman accepted history" {:block block})))
                       blocks))
            frontier (or (peek history) root)
            cursor (:delivered-through config)
            _ (when (or (and (some? cursor)
                             (not (and (integer? cursor) (<= (:height root) cursor (:height frontier)))))
                        (and (nil? cursor) (pos? (:height root))))
                (throw (ex-info "Snowman consumer cursor falls outside its durable history"
                                {:cursor cursor :root (:height root) :frontier (:height frontier)})))
            recovery (cond
                       (and cursor (< cursor (:height frontier)))
                       [(n/commit (mapv :id (subvec history (- cursor (:height root)))))]

                       (and (nil? cursor) (seq history)) [(n/resync (mapv :id history))])]
        (n/result {:peer-id (:peer-id config)
                   :peers validators :powers powers :root root :verify-block (:verify-block config)
                   :params params
                   :poll-interval (:poll-interval config 2)
                   :poll-timeout (:poll-timeout config default-poll-timeout)
                   :blocks blocks
                   :children {}
                   :snowballs {}
                   :orphans {}
                   :accepted (set (keys blocks))
                   :rejected #{}
                   :last-accepted (:id frontier)
                   :preference (:id frontier)
                   :commit-index (:height frontier)
                   :next-request 0
                   :outstanding (sorted-map)
                   :last-polled -1
                 ;; Votes waiting on a block we have asked for. Bounded both
                 ;; ways: an unbounded pool is a leak an adversary can drive by
                 ;; chitting block ids that do not exist. Aged in POLLS rather
                 ;; than ticks, because polls are what this algorithm counts.
                   :polls-run 0
                   :deferred-ttl (or (:deferred-ttl config) 20)
                   :deferred-limit (or (:deferred-limit config) 256)}
                ;; Poll periodically. Snowman has no leader to drive rounds, so
                ;; the timer IS the engine.
                  (conj (vec recovery) (n/set-timer :poll 2))))))

  (step [_ state input]
    (case (:type input)

      ;; A new block to consider. Adding it may extend the preferred branch,
      ;; which `preferred-tip` picks up: the new block's parent gets an instance
      ;; preferring it, so if the parent was the tip, the tip moves down.
      :vertex-received
      (receive-block state (:vertex input) false)

      :timer-fired
      (let [tid (:timer-id input)]
        (cond
          (= :poll tid)
          (let [{state' :state fx :effects} (start-poll state)]
            (n/result state' (conj (vec fx) (n/set-timer :poll (:poll-interval state)))))

          ;; A poll ran out of time. Complete it from what arrived, treating
          ;; the silent peers as dropped rather than the poll as void. See
          ;; `default-poll-timeout`.
          (and (vector? tid) (= :poll-expire (first tid)))
          (let [rid (second tid)]
            (if (contains? (:outstanding state) rid)
              (drain-polls (update-in state [:outstanding rid] assoc
                                      :closed? true :waiting {}) [])
              ;; Already completed on the last chit; the expiry is a straggler.
              (n/result state)))

          :else (n/result state)))

      ;; The sampler answered: query each sampled peer. The reply is a BAG --
      ;; multiplicity is vote weight -- and it is recorded PER REQUEST, because
      ;; several polls are in flight at once and a peer's weight differs between
      ;; them.
      :sampled
      (let [{rid :request-id peers :peers} input
            reserved (get-in state [:outstanding rid])]
        (if (or (<= rid (:last-polled state)) (:weights reserved) (:closed? reserved))
          (n/result state)
          (let [self (:peer-id state)
                local (if (contains? peers self) {self (:preference state)} {})
                remotes (dissoc peers self)
                st (cond-> (assoc-in state [:outstanding rid]
                                     {:weights peers :chits local :votes local :waiting {}
                                      :issued (:issued reserved (inc (:polls-run state)))
                                      :closed? (empty? remotes)})
                     (nil? reserved) (update :polls-run inc))
                queries (mapv (fn [p] (n/send-to p {:kind :query :request-id rid
                                                    :from (:peer-id state)}))
                              (sort-by str (keys remotes)))]
            (drain-polls st
                         (cond-> queries (nil? reserved)
                                 (conj (n/set-timer [:poll-expire rid] (:poll-timeout state))))))))

      :message-received
      (let [{:keys [kind request-id preference]} (:msg input)
            ;; The TRANSPORT-authenticated sender, never the one the body
            ;; claims. Attributing a chit to `(:from (:msg input))` would let one
            ;; sampled Byzantine peer forge a full sample's worth of chits under
            ;; other names and hand us any tally it liked.
            sender (:from input)]
        (case kind
          ;; Someone is polling us: answer with our current preference.
          :query
          (n/result state
                    [(n/send-to sender
                                {:kind :chit
                                 :request-id request-id
                                 :preference (:preference state)})])

          ;; A peer is missing a block we named in a chit. Serve it.
          :get-block
          (if-let [blk (get-in state [:blocks (:id (:msg input))])]
            (n/result state [(n/send-to sender {:kind :block :block blk})])
            (n/result state))

          :block (receive-block state (:block (:msg input)) true)

          :chit
          (let [out (when (integer? request-id) (get-in state [:outstanding request-id]))]
            (if (or (:closed? out) (not (contains? (:weights out) sender))
                    (contains? (:chits out) sender))
              (n/result state)
              (let [chits (assoc (:chits out) sender preference)
                    st (update-in state [:outstanding request-id] assoc :chits chits
                                  :closed? (= (count chits) (count (:weights out))))
                    [st asks] (resolve-chit st request-id sender)]
                (drain-polls st asks))))
          (n/result state)))

      (n/result state))))

(defn create
  "Create a Snowman node. A :verify-block predicate validates application IDs
  and content. Configure :params {:tree-key-mode :avalanche} to traverse
  32-byte hexadecimal IDs in AvalancheGo byte/bit order. Without a verifier, fetched blocks use block-id and locally supplied
  vertices come from the application VM. :powers sets positive voting weights
  for all validators (unit weight by default).

  Supply the application's durable :delivered-through cursor for suffix replay.
  An application migrating older decisions can supply its trusted
  :accepted-frontier block and matching cursor."
  []
  (->Snowman))
