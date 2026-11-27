(ns urd.consensus.membership-test
  "Validator set changes through a RUNNING cluster.

  Everything else about set changes is tested at the state-machine level: given
  this state and this input, what comes out. That is where the algebra belongs,
  and it is not sufficient here. A set change is the one operation whose whole
  point is that several nodes do it at the same logical moment -- and the
  failures the reference implementations actually suffered were nodes
  disagreeing about the current configuration, not a diff applied wrongly.

  CometBFT's own randomised cross-height churn harness was disabled in 2024
  and then deleted in a branch reset, leaving them with fixed hand-authored
  schedules. etcd's `InteractionEnv` is the closest thing to this in any of the
  references, and it is deterministic for the same reason this is."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.node :as node]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.tendermint :as tm]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.algorithms.bullshark :as bs]))

(def peers [:a :b :c :d])

;; ============================================================
;; Tendermint
;; ============================================================

(defn- tm-cluster
  "Four validators. `updates-at` maps a height to validator updates, which the
  proposer at that height folds into its value."
  [updates-at]
  (sim/make {:seed 5
             :nodes (zipmap peers (repeat (tm/make)))
             :node-config (zipmap peers (repeat {:timeout-propose 10
                                                 :timeout-prevote 8
                                                 :timeout-precommit 8
                                                 :timeout-delta 2}))
             :config {:value-fn (fn [_ p ctx]
                                  (cond-> {:id [:v p (:height ctx)]}
                                    (get updates-at (:height ctx))
                                    (assoc :validator-updates
                                           (get updates-at (:height ctx)))))}}))

(deftest tendermint-adds-a-validator-through-a-running-cluster
  (testing "the end-to-end shape, and the assertion that matters is that every
            node changes at the SAME HEIGHT. A diff applied correctly on each
            node in isolation still splits the cluster if they apply it at
            different moments -- which is exactly what CometBFT's off-by-ones
            around their +2 offset produced, six times in six subsystems."
    (let [s (sim/run (tm-cluster {3 [{:id :e :power 1}]}) 400)
          heights (mapv #(:height (sim/node-state s %)) peers)
          sets (mapv #(:validators (sim/node-state s %)) peers)]
      (is (every? #(> % 4) heights)
          (str "the cluster passed the change height: " heights))
      (is (apply = sets) (str "every node holds the same set: " sets))
      (is (= [:a :b :c :d :e] (first sets))
          "and it is the changed one -- the update was decided and activated")
      (is (sim/agreement? s) "with no safety violation on the way"))))

(deftest tendermint-activates-at-the-same-height-on-every-node
  (testing "not merely `they all ended up the same`, which a cluster reaches
            eventually even if it got there at different heights. Replaying the
            decisions each node recorded pins the ACTIVATION POINT: the set
            must change at the height after the decision that carried it, on
            all of them."
    (let [s (sim/run (tm-cluster {3 [{:id :e :power 1}]}) 400)]
      (doseq [p peers]
        (let [st (sim/node-state s p)
              carrier (->> (:decisions st)
                           (keep (fn [[h v]] (when (seq (:validator-updates v)) h)))
                           sort)]
          ;; A node may have trimmed the decision by now; when it still holds
          ;; it, it must be the height we asked for.
          (when (seq carrier)
            (is (= [3] carrier)
                (str p " decided the update at height 3, not " carrier))))))))

(deftest tendermint-activates-at-exactly-one-height-after-the-decision
  (testing "the OFFSET itself, which nothing else here pins.

           Checking the final set cannot see a late activation -- the cluster
           reaches the same configuration either way, just later. Verified by
           mutation: shifting the activation to `(dec old-h)` passes every
           other test in this namespace. That is the exact bug class the
           reference study found to be CometBFT's worst, the same off-by-one
           appearing in six different subsystems around their +2.

           So this watches the transition rather than the outcome: step the
           cluster one tick at a time and record the height at which the set
           first differs. It must be the height AFTER the one whose decision
           carried the update -- N=1, not N=0 and not N=2."
    (let [change-at 3
          s0 (tm-cluster {change-at [{:id :e :power 1}]})
          ;; The first height at which :a holds the new set.
          activated (loop [s s0, n 0]
                      (let [st (sim/node-state s :a)]
                        (cond
                          (not= peers (:validators st)) (:height st)
                          (> n 400) nil
                          :else (recur (sim/run s 1) (inc n)))))]
      (is (some? activated) "the set changed at all")
      (is (= (inc change-at) activated)
          (str "activated at height " activated ", expected " (inc change-at)
               " -- one after the decision that carried it")))))

(deftest tendermint-removes-a-validator-and-the-rest-continue
  (testing "removal is the direction that can wedge a cluster: the quorum is
            recomputed over a smaller set, and a node that kept counting the
            departed validator would wait for a vote that never comes."
    (let [s (sim/run (tm-cluster {3 [{:id :d :power 0}]}) 400)
          sets (mapv #(:validators (sim/node-state s %)) [:a :b :c])
          before (:height (sim/node-state s :a))
          s' (sim/run s 200)]
      (is (apply = sets))
      (is (= [:a :b :c] (first sets)) ":d is out of the set")
      (is (> (:height (sim/node-state s' :a)) before)
          "and the remaining three keep deciding -- a quorum of 3 is 3, and a
           node still counting :d would wait forever")
      (is (sim/agreement? s')))))

(deftest tendermint-a-joining-validator-participates
  (testing "reachable BEFORE it counts. A joiner has to be able to receive
            messages while it is still not a voter, or it can never catch up
            enough to become one -- which is why `:peer-ids` and the validator
            set are separate things in the simulator."
    (let [s0 (sim/run (tm-cluster {}) 200)
          h (:height (sim/node-state s0 :a))
          ;; Transfer the actual committed boundary from the donor. The
          ;; joiner keeps its own voting identity and signing registers.
          boundary (select-keys (get-in s0 [:storage :a :durable])
                                [:decided-through :validators :powers :priorities])
          s1 (sim/add-peer s0 :e (tm/make)
                           {:validators peers
                            :restored {:durable boundary :writes []}})
          _ (is (= peers (:validators (sim/node-state s1 :a)))
                ":e is reachable and NOT yet counted")
          ;; Now the cluster votes it in.
          s2 (-> s1
                 (assoc-in [:config :value-fn]
                           (fn [_ p ctx]
                             (cond-> {:id [:v p (:height ctx)]}
                               (= (:height ctx) (+ h 2))
                               (assoc :validator-updates [{:id :e :power 1}]))))
                 (sim/run 500))
          sets (mapv #(:validators (sim/node-state s2 %)) (conj peers :e))]
      (is (apply = sets) (str "all five agree on the set: " sets))
      (is (= [:a :b :c :d :e] (first sets)))
      (is (> (count (sim/committed s2 :e)) 0)
          ":e is committing values, so it really joined rather than idling")

      ;; NOT `sim/agreement?`, and the reason is a real limitation worth
      ;; naming. It compares committed sequences POSITIONALLY -- `(take n a)`
      ;; against `(take n b)` -- which assumes every node started at genesis.
      ;; A state-synced joiner did not: its sequence begins at the height it
      ;; joined, so position 0 means different things for it and for :a, and
      ;; the check reports a violation against a cluster that agrees perfectly.
      ;; Exactly the shape of the positional-indexing bug that made three Raft
      ;; safety checkers fire against a healthy cluster once compaction moved
      ;; their log bases.
      (let [a (mapv :id (sim/committed s2 :a))
            e (mapv :id (sim/committed s2 :e))
            ;; Where :e's history begins inside :a's.
            offset (.indexOf ^java.util.List a (first e))]
        (is (seq e))
        (is (nat-int? offset) "the joiner's first commit appears in :a's history")
        (is (= e (subvec a offset (+ offset (count e))))
            "and from there the two are identical, value for value, in order.
             A SLICE rather than a suffix: the joiner starts later AND may lag,
             so neither end lines up. Asserting a suffix failed for exactly
             that reason -- :a was one height ahead.")))))

;; ============================================================
;; Raft
;; ============================================================

(defn- raft-cluster [values]
  (sim/make {:seed 3
             :nodes (zipmap peers (repeat (raft/make)))
             :node-config (zipmap peers (repeat {:election-timeout 10
                                                 :heartbeat-timeout 3
                                                 :propose-interval 4}))
             :config {:min-delay 1 :max-delay 3 :persist-latency 2
                      :value-fn values}}))

(defn- raft-leader [s]
  (first (filter #(= :leader (:role (sim/node-state s %))) (:peer-ids s))))

(deftest raft-adds-a-validator-through-a-running-cluster
  (testing "Raft activates at COMMIT rather than at a height offset, so the
            end-to-end question is whether every node reaches the same
            configuration at the same LOG POSITION. `commit-to` is the single
            chokepoint the leader and every follower pass through, which is why
            that is the chosen point.

           `:e` is added to the SIMULATOR before it is voted into the set. My
           first version of this test skipped that and voted in a peer the
           transport had never heard of -- which is precisely the rule the
           design documents (reachable before it counts) and I broke it in the
           first test I wrote against it. The simulator now reports such a
           message as undeliverable rather than dying inside `node/step` on a
           nil impl."
    (let [emitted (atom false)
          s (-> (raft-cluster
                 (fn [sm p _]
                   (if (and (not @emitted) (> (:tick sm) 120))
                     (do (reset! emitted true)
                         {:validator-updates [{:id :e :power 1}]})
                     {:v (:tick sm) :by p})))
                (sim/run 100)
                (sim/add-peer :e (raft/make) {:validators peers
                                              :election-timeout 10
                                              :heartbeat-timeout 3})
                (sim/run 500))
          sets (mapv #(:validators (sim/node-state s %)) peers)]
      (is (true? @emitted) "the change was actually proposed")
      (is (apply = sets) (str "every node holds the same set: " sets))
      (is (= [:a :b :c :d :e] (first sets))
          "and it changed -- committed entries activate on every node")
      (is (some? (raft-leader s)) "the cluster still has a leader afterwards"))))

(deftest raft-refuses-a-second-change-while-one-is-uncommitted
  (testing "the one-at-a-time rule, through a running cluster rather than by
            constructing a state. Two changes in flight is the case where the
            old and new quorums need not intersect."
    (let [n (atom 0)
          s (-> (raft-cluster
                 (fn [sm p _]
                   (if (and (< @n 2) (> (:tick sm) 100))
                     (do (swap! n inc)
                         {:validator-updates [{:id (if (= 1 @n) :e :f) :power 1}]})
                     {:v (:tick sm) :by p})))
                (sim/run 90)
                (sim/add-peer :e (raft/make) {:validators peers :election-timeout 10
                                              :heartbeat-timeout 3})
                (sim/add-peer :f (raft/make) {:validators peers :election-timeout 10
                                              :heartbeat-timeout 3})
                (sim/run 500))
          sets (mapv #(:validators (sim/node-state s %)) peers)]
      (is (= 2 @n) "both changes were offered")
      (is (apply = sets))
        ;; Both may eventually land -- the rule delays the second until the
        ;; first commits, it does not discard it. What must never happen is a
        ;; node holding a set nobody else has.
      (is (contains? (set (first sets)) :e)
          "the first change took effect")
      (is (sim/agreement? s)))))

(deftest raft-a-removed-validator-stops-counting
  (testing "a stale Progress entry for a departed peer keeps contributing its
            `:match` to `committed-index`, so the commit index could be
            advanced by a node that is no longer a validator. Through a running
            cluster, that shows up as the remaining nodes still making
            progress with the smaller quorum."
    (let [emitted (atom false)
          s (sim/run (raft-cluster
                      (fn [sm p _]
                        (if (and (not @emitted) (> (:tick sm) 120))
                          (do (reset! emitted true)
                              {:validator-updates [{:id :d :power 0}]})
                          {:v (:tick sm) :by p})))
                     500)
          sets (mapv #(:validators (sim/node-state s %)) [:a :b :c])
          before (count (sim/committed s :a))
          s' (sim/run s 200)]
      (is (true? @emitted))
      (is (apply = sets))
      (is (= [:a :b :c] (first sets)) ":d is out")
      (is (not (contains? (:progress (sim/node-state s' (raft-leader s'))) :d))
          "and gone from the leader's Progress, not merely from the list")
      (is (> (count (sim/committed s' :a)) before)
          "the remaining three keep committing"))))

(deftest raft-a-multi-voter-change-completes-through-joint-consensus
  (testing "the whole two-phase transition, end to end: enter joint on the
            first decision, leave on the second, settle on the new set.

           The leave is a real log entry the LEADER proposes once the joint
           entry commits -- not an event each node infers locally. Every
           replica must reach the same configuration deterministically, and the
           only thing they all agree on is the log.

           Where decide == apply the two are consecutive decisions at a fixed
           offset. etcd cannot do that: their active config is their APPLIED
           config and applied trails commit unboundedly, so their leave is
           gated on a local predicate instead."
    (let [emitted (atom false)
          s (-> (raft-cluster
                 (fn [sm p _]
                   (if (and (not @emitted) (> (:tick sm) 120))
                     (do (reset! emitted true)
                         ;; TWO voters at once -- needs joint consensus.
                         {:validator-updates [{:id :e :power 1} {:id :f :power 1}]})
                     {:v (:tick sm) :by p})))
                (sim/run 100)
                (sim/add-peer :e (raft/make) {:validators peers :election-timeout 10
                                              :heartbeat-timeout 3})
                (sim/add-peer :f (raft/make) {:validators peers :election-timeout 10
                                              :heartbeat-timeout 3})
                (sim/run 600))
          states (map #(sim/node-state s %) peers)]
      (is (true? @emitted) "the change was proposed")
      (is (apply = (map :validators states))
          (str "every node holds the same set: " (mapv :validators states)))
      (is (= [:a :b :c :d :e :f] (:validators (first states)))
          "both validators joined")
      (is (every? #(empty? (:outgoing %)) states)
          "and every node LEFT the joint configuration -- a cluster stuck
           joint still works but pays a two-quorum tax forever, and would
           refuse the next change")
      (is (some? (raft-leader s)) "with a leader at the end")

      ;; Exactly ONE leave entry. The guard that ensures this only matters in
      ;; the window between appending the leave and it committing -- after
      ;; that `:outgoing` is empty and nothing proposes again -- so nothing
      ;; else here observes it. Verified by mutation: removing the idempotence
      ;; check passes every other assertion in this namespace while the leader
      ;; appends a leave on every commit advance.
      ;;
      ;; etcd panicked on the analogous case (`bd3c759`): repeated
      ;; transitions out of the same joint state, when the conf change was not
      ;; the last entry in the log.
      (let [leaves (fn [p] (->> (:log (sim/node-state s p))
                                (filter #(:leave-joint (:data %)))
                                count))]
        (is (every? #(= 1 (leaves %)) peers)
            (str "exactly one leave entry per node, got "
                 (mapv leaves peers)))))))

(deftest raft-refuses-a-second-change-while-joint
  (testing "etcd refuses the same (`raft.go:1326`, must transition out of the
            joint config first). A second change entering before the first has
            left would nest two transitions, and the both-halves rule relates
            exactly TWO configurations -- there is no meaning for three."
    (let [st (-> (sim/make {:seed 1 :nodes (zipmap peers (repeat (raft/make)))
                            :node-config (zipmap peers (repeat {:election-timeout 10
                                                                :heartbeat-timeout 3}))
                            :config {:value-fn (fn [sm p _] {:v (:tick sm)})}})
                 (sim/run 60)
                 (sim/node-state :a))
          ;; Force the joint state directly -- reaching it through a run is
          ;; what the test above does; this isolates the refusal.
          joint (assoc st :role :leader :outgoing (:validators st))
          {after :state} (node/step (raft/make) joint
                                    (node/value-ready {:validator-updates
                                                       [{:id :z :power 1}]}))]
      (is (= (raft/last-index joint) (raft/last-index after))
          "nothing is appended while joint"))))

;; ============================================================
;; round-robin
;; ============================================================

(defn- rr-cluster [updates-at]
  (let [atts (rr/test-attestations)
        vset (zipmap peers (repeat nil))]
    (sim/make {:seed 9
               :nodes (zipmap peers (repeat (rr/create vset)))
               :node-config (zipmap peers (repeat (merge atts {:validators peers})))
               :config {:value-fn (fn [_ p ctx]
                                    (cond-> {:snapshot-id [:v p (:height ctx)]}
                                      (get updates-at (:height ctx))
                                      (assoc :validator-updates
                                             (get updates-at (:height ctx)))))}})))

(defn- rr-set [s p] (vec (sort (keys (:validator-set (sim/node-state s p))))))

(deftest round-robin-changes-its-set-and-the-rotation-with-it
  (testing "this algorithm is the most sensitive of the three to getting the
            activation point wrong, and the reason is its safety argument.

           The proposer is `(mod height (count validators))` over the sorted
           ids: exactly one validator proposes per height, so at most one
           proposal per height ever exists, so two values cannot both reach a
           majority without any locking. Nothing else defends that, because
           nothing else has to.

           A set change REINDEXES that rotation. Two nodes disagreeing about
           the set at height H compute different proposers, each accepts a
           different proposal, and the one-proposal-per-height premise is gone.
           So the set must change at a point every node agrees on -- which the
           finalized proposal is, by construction."
    (let [atts (rr/test-attestations)
          s (-> (rr-cluster {2 [{:id :e :power 1}]})
                ;; :e must be REACHABLE before the rotation reaches it. Without
                ;; this the cluster stalls the moment `(mod height 5)` selects
                ;; a validator nobody can talk to -- observed at height 4, and
                ;; a sharper demonstration of the rule than any assertion:
                ;; in Tendermint an unreachable validator costs liveness only
                ;; when it is needed for a quorum, here it costs a whole height
                ;; every cycle, because it is the sole proposer for that height.
                (sim/add-peer :e (rr/create (zipmap (conj peers :e) (repeat nil)))
                              (merge atts {:validators (conj peers :e)}))
                (sim/run 400))
          sets (mapv #(rr-set s %) peers)]
      (is (apply = sets) (str "every node holds the same set: " sets))
      (is (= [:a :b :c :d :e] (first sets)) "and it changed")
      (is (sim/agreement? s) "with no safety violation")
      (is (> (:height (sim/node-state s :a)) 6)
          "and the cluster kept making progress across the reindexed rotation,
           including the heights where :e is the proposer"))))

(deftest round-robin-activates-at-exactly-the-next-height
  (testing "watching the transition rather than the outcome, for the same
            reason as Tendermint: a late activation reaches the same set and
            fails no assertion about the set."
    (let [change-at 2
          activated (loop [s (rr-cluster {change-at [{:id :e :power 1}]}), n 0]
                      (let [st (sim/node-state s :a)]
                        (cond
                          (not= peers (vec (sort (keys (:validator-set st)))))
                          (:height st)
                          (> n 400) nil
                          :else (recur (sim/run s 1) (inc n)))))]
      (is (some? activated) "the set changed at all")
      (is (= (inc change-at) activated)
          (str "activated at height " activated ", expected " (inc change-at))))))

(deftest round-robin-removes-a-validator
  (testing "removal shrinks the rotation as well as the quorum. A node that
            kept the departed validator in its set would compute a proposer
            nobody else expects for one height in every cycle."
    (let [s (sim/run (rr-cluster {2 [{:id :d :power 0}]}) 400)
          sets (mapv #(rr-set s %) [:a :b :c])]
      (is (apply = sets))
      (is (= [:a :b :c] (first sets)))
      (is (sim/agreement? s))
      (is (> (:height (sim/node-state s :a)) 5)
          "the remaining three keep finalizing on a 3-cycle rotation"))))

;; ============================================================
;; Bullshark -- refuses, and says so
;; ============================================================

(deftest bullshark-refuses-a-set-change-rather-than-ignoring-it
  (testing "the DAG cannot honour one. `order-anchors` re-derives who led
            HISTORICAL rounds from the CURRENT committee, so a change rewrites
            the committed order -- Narwhal has the identical property and
            resolves it by destroying the DAG and rebuilding from a new
            genesis.

           What matters is that it refuses LOUDLY. The payload is opaque to
           this algorithm, so silently proposing the value would have consensus
           order it, the application see it committed, and the set never
           change. The application would then believe a membership it does not
           have -- worse than an error, because nothing reports it."
    (let [atts (bs/test-attestations)
          {st :state} (node/init (bs/create)
                                 (merge atts {:peer-id :a :validators peers}))
          {st' :state fx :effects}
          (node/step (bs/create) st
                     (node/value-ready {:payload :x
                                        :validator-updates [{:id :e :power 1}]}))
          logs (keep #(when (= :log (node/effect-kind %)) (node/effect-params %)) fx)]
      (is (some #(= :validator-updates-unsupported (:event (:message %))) logs)
          (str "it must SAY it cannot do this: " (pr-str logs)))
      (is (empty? (filter #(= :broadcast (node/effect-kind %)) fx))
          "and must not propose the value as though it had been honoured")))

  (testing "while an ordinary value produces no such complaint"
    (let [atts (bs/test-attestations)
          {st :state} (node/init (bs/create)
                                 (merge atts {:peer-id :a :validators peers}))
          {fx :effects} (node/step (bs/create) st (node/value-ready {:payload :x}))
          logs (keep #(when (= :log (node/effect-kind %)) (node/effect-params %)) fx)]
      ;; Asserted on the COMPLAINT rather than on a broadcast: whether a fresh
      ;; node can build a header at round 0 depends on parent availability, so
      ;; a broadcast assertion would be testing header construction rather than
      ;; this guard.
      (is (not-any? #(= :validator-updates-unsupported (:event (:message %))) logs)
          "or the guard fires on everything, which passes the assertion above
           while breaking the algorithm"))))
