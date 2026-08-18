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
            [urd.consensus.pending :as pending]
            [urd.consensus.algorithms.snowflake :as sf]
            [urd.consensus.algorithms.snowtree :as st]
            [hasch.core :as hasch]))

;; Depth guard on every block-tree walk. The block tree is built from untrusted
;; messages, so a cycle is a thing a peer can send us, not a thing that cannot
;; happen.
(def ^:private max-depth 1000)

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

(defn- instance-new [params choice]
  (case (variant params)
    :tree (st/tree params choice (choice-key choice))
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
    :tree (st/tree-add inst choice (choice-key choice))
    inst))

(defn- instance-record-poll
  "Feed one poll's per-child votes in.

  The flat variants reduce the bag to its plurality first, which is
  `Flat.RecordPoll` (`flat.go:29-33`) exactly. The Tree takes the whole bag,
  which is the entire difference between them."
  [inst params child-votes]
  (case (variant params)
    :tree (st/tree-record-poll inst child-votes)
    (let [[choice votes] (apply max-key val (sort-by key child-votes))]
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
    (and (contains? (:accepted state) parent)
         (not= parent (:last-accepted state)))
    (update state :rejected conj id)

    (nil? (get-in state [:blocks parent]))
    ;; Unknown parent. Hold it rather than drop it: blocks reach us over a
    ;; reordering network, so a child arriving before its parent is ordinary,
    ;; and dropping it would strand the whole branch permanently.
    (assoc-in state [:orphans id] blk)

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
  (loop [st (add-one state blk), guard 0]
    (let [st' (reduce add-one st (vals (:orphans st)))]
      (if (or (= (:blocks st') (:blocks st)) (>= guard max-depth))
        st'
        (recur st' (inc guard))))))

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
  (loop [cur id, acc ()]
    (cond
      (= cur stop) {:path (vec acc)}
      (nil? cur) nil
      (> (count acc) max-depth) nil
      (nil? (get-in state [:blocks cur])) {:missing cur}
      :else (recur (get-in state [:blocks cur :parent]) (conj acc cur)))))

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
    (n/result (assoc state :next-request (inc rid))
              [(n/sample rid (get-in state [:params :k]) :peers)])))

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

(defn- split-chits
  "Partition chits into those we can tally and those blocked on a block we do
  not hold. Returns `{:usable {peer pref} :blocked [{:peer :pref :missing}]}`.

  A chit on a genuinely unreachable branch -- rejected, or not descended from
  our last accepted block -- is in NEITHER: it is correctly discarded, exactly
  as `topological.go:378` discards a vote that bubbles to nothing."
  [state chits]
  (reduce (fn [acc [peer pref]]
            (let [r (resolve-path state pref (:last-accepted state))]
              (cond
                (:path r) (assoc-in acc [:usable peer] pref)
                (:missing r) (update acc :blocked conj
                                     {:peer peer :pref pref :missing (:missing r)})
                :else acc)))
          {:usable {} :blocked []}
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
  (loop [st state, commits [], guard 0]
    (let [la (:last-accepted st)
          sb (get-in st [:snowballs la])]
      (if-not (and sb (instance-finalized? sb (:params st)) (< guard max-depth))
        [st commits]
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
          (recur st (conj commits (n/commit [choice])) (inc guard)))))))

(defn- preferred-tip
  "Walk down the preferred branch to a leaf (`topological.go:296-311`).

  Leaving preference at the child of the last accepted block -- which is where
  the tally puts it -- would mean every completed poll pulled preference back
  from the tip, capping the chain at one block per round."
  [state]
  (loop [cur (:last-accepted state), guard 0]
    (let [inst (get-in state [:snowballs cur])]
      (if (and inst (< guard max-depth))
        (recur (instance-preference inst (:params state)) (inc guard))
        cur))))

(defn- tally
  "Apply a set of chits and settle the consequences."
  [state chits weights]
  (let [state (record-votes state (bubble state chits weights))
        [state commits] (accept-finalized state)]
    [(assoc state :preference (preferred-tip state)) commits]))

(defn- finish-poll
  "Record a completed poll's chits and settle the consequences.

  A chit naming a block we do not hold is DEFERRED and the block requested from
  the peer that named it -- the one peer we know has it. It used to be dropped
  along with any hope of ever obtaining the block, which stranded the node at
  that height permanently while it went on being sampled, contributing nothing
  to anyone's tally. avalanchego issues `SendGet` to that peer
  (`engine.go:709-722`) and schedules the vote as blocked on the block
  (`:396-415`), applying it when the block lands."
  [state rid chits weights]
  (let [{:keys [usable blocked]} (split-chits state chits)
        [state commits] (tally state usable weights)
        ;; Park each blocked vote against the block it waits on. Keyed by
        ;; (request, peer) so a re-delivered chit cannot re-stamp it.
        state (reduce (fn [st {:keys [peer pref missing]}]
                        (update st :deferred pending/park
                                [rid peer] missing
                                {:peer peer :pref pref :weight (get weights peer 1)}
                                (:polls-run st 0)))
                      state
                      blocked)
        [deferred dropped] (pending/reap (:deferred state) (:polls-run state 0)
                                         (:deferred-ttl state)
                                         (:deferred-limit state))
        state (assoc state :deferred deferred)
        asks (mapv (fn [{:keys [peer missing]}]
                     (n/send-to peer {:kind :get-block :id missing}))
                   ;; One ask per (peer, block), not one per chit.
                   (distinct (map #(select-keys % [:peer :missing]) blocked)))]
    (n/result (update state :polls-run (fnil inc 0))
              (cond-> (vec (concat commits asks))
                (pos? dropped)
                (conj (n/log-effect :debug
                                    (str "dropped " dropped " deferred votes")))))))

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
    ;; The only algorithm here that emits `:sample`, and the only one that
    ;; emits no `:persist-then` at all -- Snowman has no durable state and
    ;; nothing it signs, so there is no binding commitment to gate.
    ;;
    ;; No `:revert`, despite finality being PROBABILISTIC. Those are different
    ;; axes: acceptance here is absorbing, so a consumer needs no code for
    ;; revocation even though it needs an assumption about parameters.
    {:emits #{:send :sample :set-timer :cancel-timer :commit :log}})

  (init [_ config]
    (let [genesis (or (:genesis config) :genesis)
          params (merge sf/default-params (:params config))]
      (when-not (sf/valid-params? params)
        (throw (ex-info "invalid snowball parameters" {:params params})))
      ;; A misspelt variant must not fall through to a default. The `case`
      ;; forms above would throw anyway, but far from here and with nothing
      ;; naming the cause -- and a silent default would be worse still, since
      ;; the three shapes differ in how much of a poll's evidence they use.
      (when-not (contains? variants (variant params))
        (throw (ex-info "unknown snowman variant"
                        {:variant (:variant params) :known variants})))
      (n/result {:peer-id (:peer-id config)
                 :peers (n/validator-set config)
                 :params params
                 :poll-interval (:poll-interval config 2)
                 :poll-timeout (:poll-timeout config default-poll-timeout)
                 :blocks {genesis {:id genesis :parent nil :height 0}}
                 :children {}
                 :snowballs {}
                 :orphans {}
                 :accepted #{genesis}
                 :rejected #{}
                 :last-accepted genesis
                 :preference genesis
                 :commit-index 0
                 :next-request 0
                 :outstanding {}
                 ;; Votes waiting on a block we have asked for. Bounded both
                 ;; ways: an unbounded pool is a leak an adversary can drive by
                 ;; chitting block ids that do not exist. Aged in POLLS rather
                 ;; than ticks, because polls are what this algorithm counts.
                 :deferred pending/empty-pool
                 :polls-run 0
                 :deferred-ttl (or (:deferred-ttl config) 20)
                 :deferred-limit (or (:deferred-limit config) 256)}
                ;; Poll periodically. Snowman has no leader to drive rounds, so
                ;; the timer IS the engine.
                [(n/set-timer :poll 2)])))

  (step [_ state input]
    (case (:type input)

      ;; A new block to consider. Adding it may extend the preferred branch,
      ;; which `preferred-tip` picks up: the new block's parent gets an instance
      ;; preferring it, so if the parent was the tip, the tip moves down.
      :vertex-received
      (let [state (add-block state (:vertex input))]
        (n/result (assoc state :preference (preferred-tip state))))

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
            (if-let [out (get-in state [:outstanding rid])]
              (finish-poll (update state :outstanding dissoc rid)
                           rid (:chits out) (:weights out))
              ;; Already completed on the last chit; the expiry is a straggler.
              (n/result state)))

          :else (n/result state)))

      ;; The sampler answered: query each sampled peer. The reply is a BAG --
      ;; multiplicity is vote weight -- and it is recorded PER REQUEST, because
      ;; several polls are in flight at once and a peer's weight differs between
      ;; them.
      :sampled
      (let [{:keys [request-id peers]} input
            state (assoc-in state [:outstanding request-id]
                            {:expect (set (keys peers)) :weights peers :chits {}})]
        (n/result state
                  (conj (mapv (fn [p] (n/send-to p {:kind :query
                                                    :request-id request-id
                                                    :from (:peer-id state)}))
                              (sort (keys peers)))
                        (n/set-timer [:poll-expire request-id] (:poll-timeout state)))))

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

          ;; A block we asked for. Add it, then apply every vote that was
          ;; waiting on it -- the deferred half of `finish-poll`.
          :block
          (let [blk (:block (:msg input))
                id (:id blk)]
            (if (or (nil? id) (get-in state [:blocks id]))
              (n/result state)
              (let [state (add-block state blk)
                    [pool waiting] (pending/release (:deferred state) id)
                    state (assoc state :deferred pool)
                    chits (into {} (map (juxt :peer :pref)) waiting)
                    weights (into {} (map (juxt :peer :weight)) waiting)
                    [state commits] (tally state chits weights)]
                (n/result (assoc state :preference (preferred-tip state)) commits))))

          ;; A chit came back. Once every sampled peer has answered, tally.
          :chit
          (let [out (get-in state [:outstanding request-id])]
            (if-not (and out (contains? (:expect out) sender))
              ;; Stale poll, unknown poll, or a peer we did not sample.
              (n/result state)
              ;; FIRST response binds. `early_term_traversal.go:144-151` reads
              ;; the peer's count and then removes it from `polled`, so a
              ;; second `Vote` from the same peer contributes 0. Overwriting let
              ;; a sampled Byzantine peer change its vote until the poll closed.
              (let [chits (if (contains? (:chits out) sender)
                            (:chits out)
                            (assoc (:chits out) sender preference))
                    state (assoc-in state [:outstanding request-id :chits] chits)]
                (if (< (count chits) (count (:expect out)))
                  (n/result state)
                  (finish-poll (update state :outstanding dissoc request-id)
                               request-id chits (:weights out))))))
          (n/result state)))

      (n/result state))))

(defn create
  "Create a Snowman node."
  []
  (->Snowman))
