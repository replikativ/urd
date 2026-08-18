(ns urd.consensus.conformance-test
  "Every algorithm, over the REAL runtime.

  Until this existed, one algorithm had run on `urd.consensus.runtime`
  (round-robin, over kabel) and one had been spot-checked (Raft). The other
  five had never had a message leave a state machine: they were PORTABLE to the
  runtime and unexercised on it, and that distinction had already cost this
  project a day.

  What this adds over `sim-test` is not a different algorithm but a different
  INTERPRETER. The simulator is one thread, logical time, and a map for a
  network; the runtime is core.async, a wall clock, a real store, real timers,
  and a `ConsensusNetwork`. Everything below was found by running exactly these
  five configurations, and none of it was reachable in the simulator:

  - the runtime subscribed to round-robin's topic vocabulary, hardcoded, so
    every other algorithm's broadcasts went to a topic nothing was listening
    on -- silently, with no error;
  - `on-finalize` ran inside a go block, so two commits in quick succession
    raced and the application saw the committed prefix OUT OF ORDER;
  - round-robin replaced a proposal it had already broadcast when the
    application answered a second `request-value` for the same height, which
    breaks the one-proposal-per-height assumption its safety rests on.

  The property asserted is the same one `sim/agreement?` asserts: no two nodes
  disagree about a position in the committed sequence. It is checked over the
  runtime's own `on-finalize` seam, which is what an application actually
  sees."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.node :as n]
            [urd.consensus.auth :as auth]
            [urd.consensus.runtime :as rt]
            [urd.consensus.store :as store]
            [urd.consensus.networks.simulation :as sn]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.tendermint :as tm]
            [urd.consensus.algorithms.scp :as scp]
            [urd.consensus.algorithms.bullshark :as bs]
            [urd.consensus.algorithms.snowman :as sm]
            [urd.consensus.algorithms.nakamoto :as nk]
            [clojure.core.async :refer [<!! timeout]]))

(def peers [:a :b :c :d])

(defn auth-for-peers
  "Real Ed25519 identities for a peer set.

  NOT `:auth :none`. Unauthenticated mode yields an empty `verified-by` by
  design, and Tendermint and Bullshark check it -- so they correctly refuse
  every message and make no progress. Running conformance authenticated is
  therefore both more realistic and the only way these two can run at all,
  which is the clearest possible statement that the check is live."
  [ids]
  (let [kps (into {} (map (fn [id] [id (<!! (auth/generate-keypair))])) ids)
        pubs (into {} (map (fn [[id kp]] [id (:public kp)])) kps)]
    (into {} (map (fn [[id kp]]
                    [id {:chain :urd-conformance :peer-id id
                         :private-key (:private kp) :public-keys pubs}]))
          kps)))
(def validator-set (into {} (map (fn [p] [p (str "pk-" (name p))])) peers))
(def qset {:threshold 3 :validators peers :inner-sets []})

(defn run-network
  "Start one runtime per peer over a shared in-process network, run for
  `ms`, and return `{peer -> committed-vector}`.

  `per-node` may be a map or `(fn [peer-id])`. `:kick?` sends `:start-round`,
  which round-robin needs because it does not self-start."
  [{:keys [node-fn per-node ms kick?] :or {ms 4000}}]
  (let [router (sn/create-router)
        auths (auth-for-peers peers)
        committed (atom (into {} (map (fn [p] [p []])) peers))
        runtimes (doall
                  (for [id peers]
                    (<!! (rt/start-runtime!
                          (merge {:peer-id id
                                  :node (node-fn id)
                                  :auth (get auths id)
                                  :validators peers
                                  :network (sn/create-simulation-network id router)
                                  :store (store/memory-store)
                                  :tick-ms 20
                                  :on-finalize (fn [vs]
                                                 (swap! committed update id into vs))}
                                 (if (fn? per-node) (per-node id) per-node))))))]
    (when-let [bad (first (filter #(instance? Throwable %) runtimes))]
      (throw bad))
    (when kick?
      (doseq [r runtimes] (rt/send-event! r {:type :start-round})))
    (<!! (timeout ms))
    (let [result {:committed @committed
                  :errors (vec (keep #(some-> (rt/last-error %) ex-message) runtimes))}]
      (doseq [r runtimes] (<!! (rt/stop-runtime! r)))
      result)))

(defn first-divergence
  "The first position where two nodes disagree, or nil."
  [committed]
  (let [vs (vals committed)
        n (apply min (map count vs))]
    (first (for [i (range n)
                 :when (> (count (set (map #(nth % i) vs))) 1)]
             i))))

(defn check!
  "Every node made progress, nobody errored, and no position disagrees."
  [label {:keys [committed errors]}]
  (is (empty? errors) (str label ": event loops must not halt -- " (pr-str errors)))
  (is (every? pos? (map count (vals committed)))
      (str label ": every node must commit something -- "
           (pr-str (into (sorted-map) (for [[k v] committed] [k (count v)])))))
  (is (nil? (first-divergence committed))
      (str label ": committed sequences must agree at every position")))

;; ============================================================
;; One test per algorithm
;; ============================================================

(deftest ^:integration round-robin-on-the-runtime
  (check! "round-robin"
          (run-network {:node-fn (fn [_] (rr/create validator-set))
                        :kick? true
                        :per-node (merge (rr/test-attestations)
                                         {:validator-set validator-set
                                          ;; A FRESH value on every request,
                                          ;; deliberately. The application is
                                          ;; allowed to do this --
                                          ;; `request-value` promises nothing
                                          ;; about being asked once -- and it
                                          ;; used to diverge the cluster. See
                                          ;; `handle-value-ready`.
                                          :on-propose (fn [_] {:snapshot-id (random-uuid)
                                                               :data "x"})})})))

(deftest ^:integration raft-on-the-runtime
  (check! "raft"
          (run-network {:node-fn (fn [_] (raft/make))
                        :per-node {:on-propose (fn [_] {:id (random-uuid)})}})))

(deftest ^:integration tendermint-on-the-runtime
  (check! "tendermint"
          (run-network {:node-fn (fn [_] (tm/make))
                        :per-node {:on-propose (fn [_] {:id (random-uuid)})}})))

(deftest ^:integration bullshark-on-the-runtime
  (check! "bullshark"
          (run-network {:node-fn (fn [_] (bs/create))
                        :per-node (merge (bs/test-attestations)
                                         {:on-propose (fn [_] {:id (random-uuid)})})})))

(deftest ^:integration scp-on-the-runtime
  (testing "SCP decides ONE slot and stops, which is the algorithm rather than a
            stall: nothing advances a slot without the application supplying a
            value for the next one."
    (check! "scp"
            (run-network {:node-fn (fn [_] (scp/make))
                          :per-node (fn [id]
                                      {:qset qset
                                       :qsets (into {} (map (fn [p] [p qset])) peers)
                                       :value {:id [:v id]}})}))))

;; ============================================================
;; Regressions for what running them found
;; ============================================================

(deftest ^:integration a-node-broadcasting-to-an-undeclared-topic-is-refused
  (testing "the runtime subscribes to exactly what a node DECLARES, so a
            broadcast outside that set is a message that provably cannot be
            received. It used to be accepted, sent, and dropped -- Tendermint
            started cleanly and sat at height 0 forever, because the runtime's
            subscription list was round-robin's vocabulary."
    (let [router (sn/create-router)
          liar (reify n/Node
                 (capabilities [_] {:emits #{:broadcast} :topics #{:declared}})
                 (init [_ _] (n/result
                              {} [(n/broadcast :undeclared {:x 1})]))
                 (step [_ st _] (n/result st [])))
          errs (atom [])
          r (<!! (rt/start-runtime! {:peer-id :a :node liar :validators [:a]
                                     :network (sn/create-simulation-network :a router)
                                     :store (store/memory-store)
                                     :on-error (fn [e] (swap! errs conj e))}))]
      ;; The offending broadcast is in `init`, so it is interpreted at startup.
      (<!! (timeout 200))
      (is (or (instance? Throwable r)
              (some? (rt/last-error r))
              (seq @errs))
          "an undeclared topic must be refused, not silently dropped")
      (when-not (instance? Throwable r) (<!! (rt/stop-runtime! r))))))

(deftest ^:integration commits-reach-the-application-in-order
  (testing "`on-finalize` used to run inside a go block, so two commits in
            quick succession raced and the application saw the committed prefix
            out of ORDER -- identical set, wrong sequence, no error anywhere.
            A consumer that applies them as transactions, which is exactly what
            the datahike ledger does, would have written the database wrong and
            had no way to notice.

            Tendermint is used because it commits fast enough to expose it: the
            original divergence showed up at position 486."
    (let [{:keys [committed]}
          (run-network {:node-fn (fn [_] (tm/make))
                        :ms 5000
                        :per-node {:on-propose (fn [_] {:id (random-uuid)})}})]
      (is (every? #(> (count %) 100) (vals committed))
          "enough commits to have raced")
      (is (nil? (first-divergence committed))
          "and every node's sequence is in the same order"))))

;; ============================================================
;; The two that need an external vertex source
;; ============================================================

(def nakamoto-genesis
  {:version 1 :prev nk/zero-hash :merkle-root nk/zero-hash
   :time 1600000000 :bits 0x207fffff :nonce 0})

(def nakamoto-params
  {:pow-limit-bits 0x207fffff
   :blocks-per-retarget 100000          ; retargeting off; not what is under test
   :target-timespan 1209600})

(deftest ^:integration snowman-on-the-runtime
  (testing "Snowman consumes blocks rather than producing them, so it needs a
            block source the other five do not. This is also the only algorithm
            whose `:sample` effect the runtime has to interpret -- drawing peers
            from `:validators` with its own generator -- which no other
            conformance case exercises."
    (let [router (sn/create-router)
          auths (auth-for-peers peers)
          committed (atom (into {} (map (fn [p] [p []])) peers))
          runtimes (into {}
                         (for [id peers]
                           [id (<!! (rt/start-runtime!
                                     {:peer-id id :node (sm/create) :validators peers
                                      :auth (get auths id)
                                      :network (sn/create-simulation-network id router)
                                      :store (store/memory-store) :tick-ms 20
                                      :params {:k 3 :alpha-preference 2
                                               :alpha-confidence 2 :beta 3}
                                      :on-finalize (fn [vs]
                                                     (swap! committed update id into vs))}))]))
          height (atom 0)]
      ;; A block producer: extend whatever :a currently prefers, hand it to all.
      (dotimes [_ 20]
        (<!! (timeout 120))
        (let [parent (:preference (rt/get-state (get runtimes (first peers))))
              blk {:id (keyword (str "blk" (swap! height inc)))
                   :parent parent :height @height}]
          (doseq [[_ r] runtimes] (rt/send-event! r (n/vertex-received blk)))))
      (<!! (timeout 3000))
      (check! "snowman" {:committed @committed
                         :errors (vec (keep #(some-> (rt/last-error %) ex-message)
                                            (vals runtimes)))})
      (doseq [[_ r] runtimes] (<!! (rt/stop-runtime! r))))))

(deftest ^:integration nakamoto-on-the-runtime
  (testing "one miner, no fork -- the baseline before the reorg case below"
    (let [router (sn/create-router)
          auths (auth-for-peers peers)
          committed (atom (into {} (map (fn [p] [p []])) peers))
          runtimes (into {}
                         (for [id peers]
                           [id (<!! (rt/start-runtime!
                                     {:peer-id id :node (nk/create) :validators peers
                                      :auth (get auths id)
                                      :network (sn/create-simulation-network id router)
                                      :store (store/memory-store) :tick-ms 20
                                      :params nakamoto-params :genesis nakamoto-genesis
                                      :now 2000000000
                                      :on-finalize (fn [vs]
                                                     (swap! committed update id into vs))}))]))]
      (dotimes [i 10]
        (<!! (timeout 200))
        (let [r (get runtimes (first peers))
              tpl (nk/template (rt/get-state r) {:merkle-root (format "%064x" (+ 100 i))})]
          (when-let [h (nk/mine tpl 2000000)]
            (rt/send-event! r (n/vertex-received h)))))
      (<!! (timeout 3000))
      (check! "nakamoto" {:committed @committed
                          :errors (vec (keep #(some-> (rt/last-error %) ex-message)
                                             (vals runtimes)))})
      (doseq [[_ r] runtimes] (<!! (rt/stop-runtime! r))))))

(deftest ^:integration a-reorg-reverts-over-the-runtime
  (testing "`:revert` interpreted by the RUNTIME rather than the simulator.

            This is the only algorithm that revokes a decision, and until now
            the runtime's revert path -- including the check that a revert's
            `:dropped` matches the committed tail it retains -- had only ever
            been exercised by hand-built unit tests. A real reorg is a
            different thing: the drop set is produced by the algorithm walking
            an actual fork, not by a test author writing down what it should be.

            The fork is made by dropping messages TO one node while it keeps
            mining, so it builds a branch nobody else adopts while the other
            node overtakes it on work."
    (let [peers2 [:a :b]
          router (sn/create-router)
          auths (auth-for-peers peers2)
          reverts (atom [])
          runtimes (into {}
                         (for [id peers2]
                           [id (<!! (rt/start-runtime!
                                     {:peer-id id :node (nk/create) :validators peers2
                                      :auth (get auths id)
                                      :network (sn/create-simulation-network id router)
                                      :store (store/memory-store) :tick-ms 20
                                      :params nakamoto-params :genesis nakamoto-genesis
                                      :now 2000000000
                                      :on-finalize (fn [_])
                                      :on-revert (fn [_to dropped]
                                                   (swap! reverts conj [id (count dropped)]))}))]))
          mine! (fn [id tag]
                  (let [r (get runtimes id)
                        tpl (nk/template (rt/get-state r)
                                         {:merkle-root (format "%064x" (hash tag))})]
                    (when-let [h (nk/mine tpl 2000000)]
                      (rt/send-event! r (n/vertex-received h)))))
          ;; Saved and restored rather than `unregister-peer!`, which drops the
          ;; peer's handlers -- re-registering would give back a node that is
          ;; connected and deaf.
          saved (get-in @router [:peers :b])]
      (swap! router update :peers dissoc :b)
      (dotimes [i 2] (mine! :a (str "a" i)) (<!! (timeout 120)))
      (dotimes [i 4] (mine! :b (str "b" i)) (<!! (timeout 120)))
      (<!! (timeout 800))
      (swap! router assoc-in [:peers :b] saved)
      (dotimes [i 2] (mine! :b (str "c" i)) (<!! (timeout 250)))
      (<!! (timeout 2500))

      (is (seq @reverts) "a reorg must actually have happened, or this proves nothing")
      (is (empty? (keep #(some-> (rt/last-error %) ex-message) (vals runtimes)))
          "and the runtime's :dropped check must have accepted every revert --
           a mismatch halts the event loop, which is how we would know")
      (is (= (:tip (rt/get-state (get runtimes :a)))
             (:tip (rt/get-state (get runtimes :b))))
          "both nodes end on the same tip")
      (doseq [[_ r] runtimes] (<!! (rt/stop-runtime! r))))))
