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

  ## What it revealed about the core protocol

  1. `Membership` does NOT apply. Snowman never asks \"is this set a quorum of
     the validators?\" -- it asks \"did alpha of my k SAMPLED peers agree?\". The
     `Membership` protocol is therefore optional, not universal, and a runtime
     must not require it. Documented in the design as a correction.

  2. `:sample` returning a BAG is load-bearing, and would have been easy to get
     wrong. Weight is drawn without replacement, so one peer can appear several
     times and its multiplicity IS its vote weight.

  3. Probabilistic finality still maps onto `:commit` without `:revert`.
     Preference flips freely BEFORE finalization, but a finalized decision is
     never revoked -- so Snowman needs the revocable API less than Raft does,
     which is a pleasing inversion of the usual intuition."
  (:require [urd.consensus.node :as n]
            [urd.consensus.algorithms.snowflake :as sf]))

;; ============================================================
;; Block tree
;; ============================================================

(defn- add-block
  "Insert a block into the tree. Blocks are {:id :parent :height}."
  [state {:keys [id parent] :as blk}]
  (if (get-in state [:blocks id])
    state
    (-> state
        (assoc-in [:blocks id] blk)
        (update-in [:children parent] (fnil conj #{}) id))))

(defn- ancestor-at
  "Walk from `id` toward the root until reaching a child of `of`, or nil."
  [state id of]
  (loop [cur id, guard 0]
    (let [blk (get-in state [:blocks cur])]
      (cond
        (nil? blk) nil
        (> guard 1000) nil
        (= (:parent blk) of) cur
        :else (recur (:parent blk) (inc guard))))))

;; ============================================================
;; Polling
;; ============================================================

(defn- start-poll
  "Emit a sample request; the reply drives the query round."
  [state]
  (let [rid (:next-request state)]
    (n/result (assoc state :next-request (inc rid))
              [(n/sample rid (get-in state [:params :k]) :peers)])))

(defn- tally
  "Turn collected chits into [votes choice].

  A chit is a peer's current preference. We count votes for the ancestor of
  each reported preference that is a child of our last-accepted block -- this is
  avalanchego's 'vote bubbling': a vote for a deep descendant counts as a vote
  for the branch it sits on."
  [state chits]
  (let [last-acc (:last-accepted state)
        bubbled (keep (fn [[peer pref]]
                        (when-let [a (ancestor-at state pref last-acc)]
                          [peer a]))
                      chits)
        counts (reduce (fn [m [peer blk]]
                         (update m blk (fnil + 0) (get-in state [:weights peer] 1)))
                       {}
                       bubbled)]
    (when (seq counts)
      (let [[choice votes] (apply max-key val (sort-by key counts))]
        [votes choice]))))

(defn- apply-poll
  "Feed a poll result into the snowball instance for the contested block."
  [state votes choice]
  (let [params (:params state)
        sb (or (get-in state [:snowballs choice]) (sf/snowball params choice))
        sb' (sf/snowball-record-poll sb votes choice)
        state (assoc-in state [:snowballs choice] sb')
        state (assoc state :preference (sf/snowball-preference sb'))]
    (if (and (sf/finalized? sb')
             (= (get-in state [:blocks choice :parent]) (:last-accepted state))
             (not (contains? (:accepted state) choice)))
      ;; Accept. Sequential along the chain: a block is accepted only when its
      ;; parent is the last accepted block, so the committed prefix is a chain.
      (let [idx (:commit-index state)]
        (n/result (-> state
                      (assoc :last-accepted choice)
                      (update :accepted conj choice)
                      (assoc :commit-index (inc idx)))
                  [(n/commit [choice] idx)]))
      (n/result state))))

;; ============================================================
;; The node
;; ============================================================

(defrecord Snowman []
  n/Node

  (init [_ config]
    (let [genesis (or (:genesis config) :genesis)
          params (merge sf/default-params (:params config))]
      (when-not (sf/valid-params? params)
        (throw (ex-info "invalid snowball parameters" {:params params})))
      (n/result {:peer-id (:peer-id config)
                 :peers (vec (sort (:validators config)))
                 :weights (or (:weights config) {})
                 :params params
                 :blocks {genesis {:id genesis :parent nil :height 0}}
                 :children {}
                 :snowballs {}
                 :accepted #{genesis}
                 :last-accepted genesis
                 :preference genesis
                 :commit-index 0
                 :next-request 0
                 :outstanding {}}
                ;; Poll periodically. Snowman has no leader to drive rounds, so
                ;; the timer IS the engine.
                [(n/set-timer :poll 2)])))

  (step [_ state input]
    (case (:type input)

      ;; A new block to consider.
      :vertex-received
      (let [blk (:vertex input)
            state (add-block state blk)]
        ;; Adopt it as our preference if it extends what we already prefer and
        ;; nothing else is contesting that slot yet.
        (n/result (if (= (:parent blk) (:preference state))
                    (assoc state :preference (:id blk))
                    state)))

      ;; Time to poll.
      :timer-fired
      (if (= :poll (:timer-id input))
        (let [{state' :state fx :effects} (start-poll state)]
          (n/result state' (conj (vec fx) (n/set-timer :poll 2))))
        (n/result state))

      ;; The sampler answered: query each sampled peer. The reply is a BAG --
      ;; multiplicity is vote weight -- so we record the weights for the tally.
      :sampled
      (let [{:keys [request-id peers]} input
            state (-> state
                      (assoc-in [:outstanding request-id] {:expect (set (keys peers))
                                                           :chits {}})
                      (update :weights merge peers))]
        (n/result state
                  (mapv (fn [p] (n/send-to p {:kind :query
                                              :request-id request-id
                                              :from (:peer-id state)}))
                        (sort (keys peers)))))

      :message-received
      (let [{:keys [kind request-id from preference]} (:msg input)]
        (case kind
          ;; Someone is polling us: answer with our current preference.
          :query
          (n/result state
                    [(n/send-to (:from input)
                                {:kind :chit
                                 :request-id request-id
                                 :from (:peer-id state)
                                 :preference (:preference state)})])

          ;; A chit came back. Once every sampled peer has answered, tally.
          :chit
          (let [out (get-in state [:outstanding request-id])]
            (if-not out
              (n/result state) ; stale or unknown poll; ignore
              (let [chits (assoc (:chits out) from preference)
                    state (assoc-in state [:outstanding request-id :chits] chits)]
                (if (< (count chits) (count (:expect out)))
                  (n/result state)
                  (let [state (update state :outstanding dissoc request-id)]
                    (if-let [[votes choice] (tally state chits)]
                      (apply-poll state votes choice)
                      ;; No usable votes: an unsuccessful poll clears confidence,
                      ;; which is what stops a flapping network from finalizing.
                      (n/result
                       (update state :snowballs
                               (fn [sbs]
                                 (into {} (map (fn [[k v]]
                                                 [k (update v :snowflake
                                                            sf/snowflake-record-unsuccessful-poll)]))
                                       sbs))))))))))
          (n/result state)))

      (n/result state))))

(defn create
  "Create a Snowman node."
  []
  (->Snowman))
