(ns urd.consensus.algorithms.scp-test
  "Federated Byzantine Agreement, tested the way FBA has to be tested.

  Every other algorithm in this library has a system-wide safety property:
  `sim/agreement?` over all live nodes. SCP does not, and asserting it would be
  asserting something false. SCP's theorem is conditioned on QUORUM
  INTERSECTION between the nodes in question, so the oracle is
  `scp/intertwined?` over a SUBSET, and a node outside that subset is allowed to
  externalize whatever it likes. `befouled-node-*` below is that case made
  explicit; it is the test that would be missing if SCP had been shoehorned into
  the existing harness."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.algorithms.scp :as scp]
            [urd.consensus.node :as node]
            [urd.consensus.sim :as sim]))

;; ============================================================
;; Topologies
;; ============================================================

(def flat-qset
  "Four peers, three needed. Every node has the SAME quorum set, so every node
  can resolve every hash from the start. The degenerate, classical-BFT-shaped
  configuration."
  {:threshold 3 :validators [:a :b :c :d]})

(def flat-peers [:a :b :c :d])

(def flat-qset-config (into {} (map (fn [n] [n flat-qset])) flat-peers))

(def tiered
  "Four peers with FOUR different opinions about whom to trust -- two of which
  happen to coincide, as they do in the real network. This is the shape that
  makes quorum-set fetching necessary, because a statement's hash is now
  genuinely one a node may never have seen."
  {:a {:threshold 3 :validators [:a :b :c :d]}
   :b {:threshold 3 :validators [:b :a :c :d]}
   :c {:threshold 2 :validators [:c :a :b]}
   :d {:threshold 2 :validators [:d :b :c]}})

(def left-cluster {:threshold 2 :validators [:a :b :c]})
(def right-cluster {:threshold 2 :validators [:d :e :f]})

(def split
  "Two intertwined clusters with no node in common, plus `:x`, whose single
  slice can be satisfied by EITHER cluster. `:x` is befouled: nothing in the
  protocol protects it, and nothing in the protocol needs to."
  (merge (zipmap [:a :b :c] (repeat left-cluster))
         (zipmap [:d :e :f] (repeat right-cluster))
         {:x {:threshold 1 :validators [] :inner-sets [left-cluster right-cluster]}}))

(defn- make-sim
  [qsets {:keys [seed drop-rate values seed-qsets? config]
          :or {seed 1 drop-rate 0.0 seed-qsets? true}}]
  (let [peers (vec (sort (keys qsets)))]
    (sim/make {:seed seed
               :nodes (zipmap peers (repeat (scp/make)))
               :node-config (into {} (map (fn [n]
                                            [n (cond-> {:qset (get qsets n)
                                                        :value (get values n n)}
                                                 seed-qsets? (assoc :qsets qsets))]))
                                  peers)
               :config (merge {:drop-rate drop-rate} config)})))

(defn- externalized-by [sim] (into {} (map (juxt identity #(scp/externalized (sim/node-state sim %))))
                                   (:peer-ids sim)))

(defn- all-externalized? [peers]
  (fn [s] (every? #(scp/externalized (sim/node-state s %)) peers)))

(defn- run-to-consensus
  ([qsets] (run-to-consensus qsets {}))
  ([qsets opts]
   (let [s (make-sim qsets opts)]
     (sim/run s (:ticks opts 300) (all-externalized? (:peer-ids s))))))

;; ============================================================
;; Quorum slices: the tree, not a number
;; ============================================================

(deftest quorum-slice-is-a-threshold-tree
  (testing "flat: three of four"
    (is (scp/quorum-slice? flat-qset #{:a :b :c}))
    (is (not (scp/quorum-slice? flat-qset #{:a :b})))
    (is (scp/quorum-slice? flat-qset #{:a :b :c :d})))
  (testing "nested: an inner set counts as one member once satisfied"
    (let [q {:threshold 2
             :validators [:a]
             :inner-sets [{:threshold 2 :validators [:b :c :d]}
                          {:threshold 2 :validators [:e :f :g]}]}]
      (is (scp/quorum-slice? q #{:a :b :c}) "one validator plus one satisfied inner set")
      (is (scp/quorum-slice? q #{:b :c :e :f}) "two satisfied inner sets")
      (is (not (scp/quorum-slice? q #{:a :b})) "an unsatisfied inner set counts for nothing")
      (is (not (scp/quorum-slice? q #{:b :c :d})) "one inner set is one member, however many nodes"))))

(deftest v-blocking-is-the-cardinality-dual-and-purely-local
  (testing "n - threshold + 1"
    (is (scp/v-blocking? flat-qset #{:a :b}))
    (is (not (scp/v-blocking? flat-qset #{:a}))))
  (testing "nested"
    (let [q {:threshold 2
             :validators [:a]
             :inner-sets [{:threshold 2 :validators [:b :c :d]}
                          {:threshold 2 :validators [:e :f :g]}]}]
      ;; blocking needs 2 of the 3 members; an inner set is blocked when 2 of
      ;; its own 3 are present.
      (is (scp/v-blocking? q #{:a :b :c}))
      (is (scp/v-blocking? q #{:b :c :e :f}))
      (is (not (scp/v-blocking? q #{:b :c})) "one blocked inner set is one member")))
  (testing "it consults NO other node's configuration -- unlike quorum?, it is
           always decidable, which is what lets a node with an empty quorum-set
           cache still be dragged forward"
    (let [state {:id :a :qset flat-qset :known-qsets {}}
          stmts [{:from :b :qset-hash 1} {:from :c :qset-hash 2}]]
      (is (true? (node/v-blocking? scp/membership state stmts (constantly true)))))))

(deftest quorum-is-a-greatest-fixpoint-not-a-count
  (testing "a set of the right SIZE is not a quorum unless it is closed"
    ;; :a and :b trust each other; :c and :d trust each other. {a b c} has
    ;; three members -- the same count as a quorum of `flat-qset` -- and is not
    ;; a quorum of anything, because c's own slice is not inside it.
    (let [qsets {:a {:threshold 2 :validators [:a :b]}
                 :b {:threshold 2 :validators [:a :b]}
                 :c {:threshold 2 :validators [:c :d]}
                 :d {:threshold 2 :validators [:c :d]}}]
      (is (= #{:a :b} (scp/survivors #{:a :b :c} qsets false))
          ":c is discarded because :d is absent")
      (is (true? (scp/quorum-tri (:a qsets) #{:a :b :c} qsets)))
      (is (false? (scp/quorum-tri (:c qsets) #{:a :b :c} qsets))
          "the same set is a quorum for :a and not for :c -- trust is subjective")))
  (testing "the discard cascades"
    (let [qsets {:a {:threshold 2 :validators [:a :b]}
                 :b {:threshold 2 :validators [:b :c]}
                 :c {:threshold 2 :validators [:c :d]}}]
      (is (= #{} (scp/survivors #{:a :b :c} qsets false))
          ":d missing kills :c, which kills :b, which kills :a"))))

;; ============================================================
;; The tri-state
;; ============================================================

(deftest quorum-is-tri-state-and-unknown-means-fetchable
  (let [hash-a (scp/qset-hash flat-qset)
        state {:id :a :qset flat-qset :known-qsets {hash-a flat-qset}}
        stmts [{:from :a :qset-hash hash-a :votes #{:v}}
               {:from :b :qset-hash 111 :votes #{:v}}
               {:from :c :qset-hash 222 :votes #{:v}}]
        voted? #(contains? (:votes %) :v)]
    (testing ":unknown, not false -- the answer is genuinely pending data"
      (is (= :unknown (node/quorum? scp/membership state stmts voted?))))
    (testing "and it says exactly which data"
      (is (= #{111 222} (scp/missing-qset-hashes state stmts))))
    (testing "supplying it decides the question"
      (is (true? (node/quorum? scp/membership
                               (update state :known-qsets merge {111 flat-qset 222 flat-qset})
                               stmts voted?)))))
  (testing "false stays false: a decided negative is not reported as :unknown"
    ;; Only :a and :b have voted. Even if every unresolved quorum set turned out
    ;; to be maximally helpful, two of four cannot clear a threshold of three.
    (let [hash-a (scp/qset-hash flat-qset)
          state {:id :a :qset flat-qset :known-qsets {hash-a flat-qset}}
          stmts [{:from :a :qset-hash hash-a :votes #{:v}}
                 {:from :b :qset-hash 111 :votes #{:v}}]]
      (is (false? (node/quorum? scp/membership state stmts #(contains? (:votes %) :v))))))
  (testing "an unresolvable node OUTSIDE my transitive trust does not make the
           answer undecidable -- :unknown is not merely 'a hash is missing'"
    (let [hash-a (scp/qset-hash flat-qset)
          state {:id :a :qset flat-qset :known-qsets {hash-a flat-qset}}
          stmts [{:from :a :qset-hash hash-a :votes #{:v}}
                 {:from :b :qset-hash hash-a :votes #{:v}}
                 {:from :c :qset-hash hash-a :votes #{:v}}
                 {:from :stranger :qset-hash 999 :votes #{:v}}]]
      (is (true? (node/quorum? scp/membership state stmts #(contains? (:votes %) :v)))))))

(deftest unknown-never-counts-as-yes
  (let [hash-a (scp/qset-hash flat-qset)
        state {:id :a :qset flat-qset :known-qsets {hash-a flat-qset}}
        voted? #(contains? (:votes %) :v)
        accepted? #(contains? (:accepted %) :v)]
    (testing "accept: one node accepting is not v-blocking, and the quorum of
             voters is undecidable, so accept must not fire"
      (let [stmts [{:from :a :qset-hash hash-a :votes #{:v} :accepted #{}}
                   {:from :b :qset-hash 111 :votes #{:v} :accepted #{}}
                   {:from :c :qset-hash 222 :votes #{:v} :accepted #{}}]]
        (is (= :unknown (scp/federated-accept state stmts voted? accepted?)))))
    (testing "confirm: a quorum's worth of nodes have ACCEPTED, but two of their
             quorum sets are unreadable, so confirm must not fire either"
      (let [stmts [{:from :a :qset-hash hash-a :votes #{:v} :accepted #{:v}}
                   {:from :b :qset-hash 111 :votes #{:v} :accepted #{:v}}
                   {:from :c :qset-hash 222 :votes #{:v} :accepted #{:v}}]]
        (is (= :unknown (scp/federated-ratify state stmts accepted?)))
        (is (true? (scp/federated-accept state stmts voted? accepted?))
            "though accept DOES fire, on the purely local v-blocking clause --
             which is the asymmetry that keeps a node with an empty cache alive")))))

;; ============================================================
;; Fetching a missing quorum set
;; ============================================================

(defn- effects-of [impl state input] (:effects (node/step impl state input)))

(defn- nominate-msg [from qset votes]
  {:kind :nominate :from from :slot 0 :qset-hash (scp/qset-hash qset)
   :votes (set votes) :accepted #{}})

(def unanimous
  "Every node needed. Chosen so that BOTH unresolvable quorum sets are
  load-bearing: with either one missing, :a's own slice cannot be assembled."
  {:a {:threshold 4 :validators [:a :b :c :d]}
   :b {:threshold 4 :validators [:b :a :c :d]}   ; same set, same hash as :a
   :c {:threshold 2 :validators [:c :a :b]}
   :d {:threshold 2 :validators [:d :a :b]}})

(deftest a-node-blocked-on-a-missing-qset-fetches-and-then-progresses
  (let [impl (scp/make)
        tiered unanimous
        ;; :a knows only its own quorum set.
        {st :state} (node/init impl {:peer-id :a :qset (:a tiered) :value :v})
        deliver (fn [st from msg]
                  (node/step impl st (node/message-received from msg #{from})))
        ;; Statements from :b, :c, :d arrive; :c's and :d's quorum sets are
        ;; hashes :a has never seen.
        r1 (deliver st :b (nominate-msg :b (:b tiered) [:v]))
        r2 (deliver (:state r1) :c (nominate-msg :c (:c tiered) [:v]))
        r3 (deliver (:state r2) :d (nominate-msg :d (:d tiered) [:v]))
        blocked (:state r3)
        requests (->> (concat (:effects r1) (:effects r2) (:effects r3))
                      (filter #(= :send (node/effect-kind %)))
                      (map node/effect-params)
                      (filter #(= :get-qset (:kind (:msg %)))))]
    (testing "it asks, by unicast, the very node whose statement it cannot read"
      (is (= #{[:c (scp/qset-hash (:c tiered))]
               [:d (scp/qset-hash (:d tiered))]}
             (set (map (juxt :to (comp :hash :msg)) requests)))
          "and does NOT ask for :b's, which hashes to the same value as its own"))
    (testing "while blocked it accepts nothing, even though a quorum has voted"
      (is (empty? (:nom-accepted blocked)))
      (is (nil? (scp/externalized blocked)))
      (is (= :unknown (node/quorum? scp/membership blocked
                                    (conj (vec (vals (:nom-latest blocked)))
                                          (:own-nomination blocked))
                                    #(contains? (:votes %) :v)))
          "and the reason is :unknown, not false -- everyone :a needs has
           voted, and :a still cannot tell whether they form a quorum"))
    (testing "the answers unblock it in the step the LAST one arrives"
      (let [r4 (deliver blocked :c {:kind :qset :hash (scp/qset-hash (:c tiered))
                                    :qset (:c tiered)})
            r5 (deliver (:state r4) :d {:kind :qset :hash (scp/qset-hash (:d tiered))
                                        :qset (:d tiered)})]
        (is (empty? (:nom-accepted (:state r4)))
            "one of the two is not enough -- still :unknown")
        (is (contains? (:nom-accepted (:state r5)) :v)
            "and with the second, the fixpoint resolves and accept fires")))))

(deftest a-forged-quorum-set-reply-is-rejected
  (testing "quorum sets are content-addressed, and the address is CHECKED

           Without this a Byzantine peer answers a fetch with a quorum set of
           its choosing -- say `{:threshold 1 :validators [attacker]}` -- and
           manufactures a quorum out of nothing, which is a total safety break
           dressed up as a cache fill."
    (let [impl (scp/make)
          {st :state} (node/init impl {:peer-id :a :qset (:a tiered) :value :v})
          honest-hash (scp/qset-hash (:c tiered))
          forged {:threshold 1 :validators [:evil]}
          {st' :state} (node/step impl st (node/message-received
                                           :evil {:kind :qset :hash honest-hash :qset forged}
                                           #{:evil}))]
      (is (not (contains? (:known-qsets st') honest-hash)))
      (is (= (:known-qsets st) (:known-qsets st'))))))

(deftest fetching-is-not-an-effect-the-protocol-lacked
  (testing "the whole fetch cycle rides on `send-to` and `message-received`

           §4 of the design doc proposed a `[:request-qset]` effect and a
           `:qset-received` event. This test is the argument that neither is
           needed: a quorum set can only come from a peer, so the request is a
           unicast and the reply is a message. Adding an effect would have
           hidden a network round trip -- with its own loss, delay and
           dishonesty -- behind something that looks local."
    (let [s (run-to-consensus tiered {:seed-qsets? false :ticks 300})
          fetch-effects (->> (:trace s)
                             (filter #(= :unknown-effect (:event %))))]
      (is (empty? fetch-effects) "no effect kind the simulator does not understand")
      (is (every? #(scp/externalized (sim/node-state s %)) (:peer-ids s))
          "and it still reaches consensus with every cache starting empty")
      (is (every? #(> (count (:known-qsets (sim/node-state s %))) 1) (:peer-ids s))
          "having actually fetched something"))))

;; ============================================================
;; The fixpoint
;; ============================================================

(deftest one-event-drives-many-transitions
  (testing "`node/fixpoint` is load-bearing: a single arriving statement walks a
           node from 'nothing prepared' to EXTERNALIZE

           accept-prepared -> confirm-prepared -> accept-commit -> confirm-commit,
           each unlocked only by the previous one. A machine that made one
           transition per event would stop after the first and would need three
           more events that will never arrive."
    (let [impl (scp/make)
          qset {:threshold 3 :validators [:a :b :c :d]}
          {st :state} (node/init impl {:peer-id :a :qset qset :qsets {:a qset}})
          ext (fn [from] {:kind :externalize :from from :slot 0
                          :qset-hash (scp/qset-hash qset)
                          :commit {:counter 1 :value :v} :n-h 1})
          deliver (fn [st from] (:state (node/step impl st (node/message-received
                                                            from (ext from) #{from}))))
          after-b (deliver st :b)
          before (scp/rule-passes after-b)
          after-c (deliver after-b :c)]
      (is (= :prepare (scp/phase after-b))
          "one statement is neither v-blocking nor a quorum: nothing fires")
      (is (nil? (:b after-b)))
      (is (= :externalize (scp/phase after-c))
          "the second makes {:b :c} v-blocking, which unlocks accept-prepared,
           which unlocks accept-commit -- and accept-commit is what first gives
           this node a ballot of its own, so its own CONFIRM statement now
           exists and completes the quorum that confirm-commit needs")
      (is (= :v (scp/externalized after-c)))
      (is (>= (- (scp/rule-passes after-c) before) 3)
          "three rule applications inside one step, each unlocked by the last"))))

(deftest a-v-blocking-set-at-a-higher-counter-drags-this-node-up
  (testing "the liveness rule, and the one place v-blocking rather than quorum
           is the ONLY workable trigger: the node is behind precisely because it
           cannot assemble a quorum, so a quorum rule would deadlock it"
    (let [impl (scp/make)
          qset {:threshold 3 :validators [:a :b :c :d]}
          h (scp/qset-hash qset)
          {st :state} (node/init impl {:peer-id :a :qset qset :qsets {:a qset} :value :v})
          ;; Nomination first, so :a has a composite candidate and therefore a
          ;; ballot of its own to be behind with.
          nom (fn [from] {:kind :nominate :from from :slot 0 :qset-hash h
                          :votes #{:v} :accepted #{:v}})
          st (reduce (fn [s p] (:state (node/step impl s (node/message-received p (nom p) #{p}))))
                     st [:b :c :d])
          at-counter (fn [from n] {:kind :prepare :from from :slot 0 :qset-hash h
                                   :ballot {:counter n :value :v}})
          st1 (:state (node/step impl st (node/message-received :b (at-counter :b 5) #{:b})))
          st2 (:state (node/step impl st1 (node/message-received :c (at-counter :c 5) #{:c})))]
      (is (= 1 (:counter (:b st))) "nomination gave :a a ballot at counter 1")
      (is (= 1 (:counter (:b st1))) "one peer ahead is not v-blocking; :a stays")
      (is (= 5 (:counter (:b st2)))
          "two of four IS v-blocking, so :a jumps straight to their counter")
      (testing "and a peer that is BEHIND does not freeze the scan

               stellar-core's loop is ascending with `if (n < targetCounter)
               break`, so one lagging peer aborts it on the first iteration and
               the node never bumps again. See `rule-bump`'s docstring."
        (let [st3 (:state (node/step impl st2 (node/message-received
                                               :d (at-counter :d 1) #{:d})))
              st4 (:state (node/step impl st3 (node/message-received
                                               :b (at-counter :b 9) #{:b})))
              st5 (:state (node/step impl st4 (node/message-received
                                               :c (at-counter :c 9) #{:c})))]
          (is (= 1 (:counter (:ballot (get-in st3 [:ballot-latest :d]))))
              "the lagging statement really is below :a's counter")
          (is (= 9 (:counter (:b st5)))))))))

(deftest the-fixpoint-terminates
  (testing "no configuration in the suite exhausts `node/fixpoint`'s iteration
           budget -- it throws rather than spinning, so a green run is proof"
    (let [s (run-to-consensus tiered {:seed 5})]
      (is (every? #(scp/externalized (sim/node-state s %)) (:peer-ids s)))
      (is (every? #(< (scp/rule-passes (sim/node-state s %)) 200) (:peer-ids s))))))

;; ============================================================
;; Nomination and the ballot protocol
;; ============================================================

(deftest nomination-converges-and-the-ballot-externalizes
  (let [s (run-to-consensus flat-qset-config)]
    (is (every? #(scp/externalized (sim/node-state s %)) flat-peers))
    (is (= 1 (count (set (vals (externalized-by s)))))
        "one value, agreed")
    (is (every? #(= 1 (count (scp/candidates (sim/node-state s %)))) flat-peers)
        "nomination stopped churning: exactly one candidate each")
    (is (sim/agreement? s))))

(deftest nomination-has-no-safety-obligation-but-must-stop
  (testing "every node starts with a DIFFERENT value; nomination's only job is
           to stop, and the ballot protocol supplies the agreement"
    (let [s (run-to-consensus tiered {:values {:a :va :b :vb :c :vc :d :vd}})]
      (is (= 1 (count (set (vals (externalized-by s)))))))))

(defn- speak-up
  "Fire nomination timers until the node has something to say.

  A node votes for its own value only in a round where the leader lottery
  picked it (`NominationProtocol.cpp:456-464`); in other rounds it waits to hear
  from a leader. So `init` does not guarantee a vote, and a test that assumed
  one would be pinning the lottery rather than the protocol."
  [impl st]
  (loop [st st, fx [], n 0]
    (if (or (:own-nomination st) (> n 12))
      [st fx]
      (let [r (node/step impl st (node/timer-fired :nomination))]
        (recur (:state r) (into fx (:effects r)) (inc n))))))

(deftest the-value-arrives-as-an-effect-response
  (testing "a node configured with no value stays silent until the application
           supplies one through `request-value`/`value-ready`"
    (let [impl (scp/make)
          {st :state} (node/init impl {:peer-id :a :qset flat-qset})]
      (is (nil? (:own-nomination st)) "nothing to say yet")
      (is (empty? (:nom-votes st)))
      (let [{st' :state} (node/step impl st (node/value-ready :late))
            [st'' _] (speak-up impl st')]
        (is (= :late (:value st'')))
        (is (contains? (:nom-votes st'') :late)
            "and once the lottery picks it, that is the value it nominates")))))

;; ============================================================
;; Safety
;; ============================================================

(deftest intertwined-nodes-never-contradict-under-partition-and-loss
  (testing "the property SCP actually promises, over many schedules"
    (doseq [seed (range 1 13)]
      (let [s (-> (make-sim tiered {:seed seed :drop-rate 0.25})
                  (sim/run 40)
                  (sim/partition-network [#{:a :b} #{:c :d}])
                  (sim/run 60)
                  sim/heal
                  (sim/run 400 (all-externalized? [:a :b :c :d])))
            vals* (remove nil? (vals (externalized-by s)))]
        (is (>= 1 (count (set vals*)))
            (str "seed " seed " externalized " (externalized-by s)))
        (is (sim/agreement? s) (str "seed " seed))))))

(defn- safety-violations
  "Walk a run one tick at a time, watching for a node that externalizes a value
  contradicting one an intertwined peer has already externalized.

  Checking only the final state would be weaker than it looks: a value is
  irrevocable once externalized, so a contradiction is permanent -- but that is
  a claim about the implementation, and asserting it at every tick is how you
  find out it is true rather than assume it."
  [sim0 ticks peers]
  (loop [s sim0, n 0, seen {}, bad []]
    (if (>= n ticks)
      bad
      (let [now (into {} (keep (fn [p]
                                 (when-let [v (scp/externalized (sim/node-state s p))]
                                   [p v])))
                      peers)
            agreed (distinct (vals now))
            changed (keep (fn [[p v]]
                            (when (and (contains? seen p) (not= v (get seen p)))
                              [:changed p (get seen p) v]))
                          now)
            bad (cond-> bad
                  (> (count agreed) 1) (conj [:tick (:tick s) :split now])
                  (seq changed) (into changed))]
        (recur (sim/advance s) (inc n) (merge seen now) bad)))))

(deftest safety-is-checked-at-every-tick-not-just-at-the-end
  (doseq [seed (range 1 9)]
    (let [s (-> (make-sim tiered {:seed seed :drop-rate 0.2})
                (sim/partition-network [#{:a :b :c} #{:d}]))]
      (is (empty? (safety-violations s 150 [:a :b :c :d]))
          (str "seed " seed))))
  (testing "and once externalized, a value is never revised"
    (let [s (make-sim tiered {:seed 11 :drop-rate 0.1})]
      (is (empty? (filter #(= :changed (first %))
                          (safety-violations s 200 [:a :b :c :d]))))))
  (testing "the detector has been watched failing, per §15 of the design doc

           `split` has no quorum intersection, so the theorem does not hold
           there and the same monitor DOES report a split. A safety check that
           has never fired is not a safety check."
    (let [s (-> (make-sim split {:seed 3 :values (merge (zipmap [:a :b :c] (repeat :left))
                                                        (zipmap [:d :e :f] (repeat :right))
                                                        {:x :left})})
                (sim/partition-network [#{:a :b :c :x} #{:d :e :f}]))
          bad (safety-violations s 250 [:a :b :c :d :e :f :x])]
      (is (seq bad))
      (is (= :split (nth (first bad) 2))))))

(deftest safety-holds-when-a-quorum-is-permanently-partitioned-away
  (testing "no progress is fine; a contradiction is not"
    (let [s (-> (make-sim tiered {:seed 2})
                (sim/partition-network [#{:a} #{:b} #{:c} #{:d}])
                (sim/run 200))]
      (is (every? nil? (vals (externalized-by s)))
          "nobody can assemble a quorum, so nobody decides")
      (is (sim/agreement? s)))))

(deftest a-crashed-node-does-not-break-the-survivors
  (let [s (-> (make-sim tiered {:seed 4})
              (sim/run 10)
              (sim/crash :d)
              (sim/run 400 (all-externalized? [:a :b :c])))]
    (is (every? #(scp/externalized (sim/node-state s %)) [:a :b :c]))
    (is (= 1 (count (set (remove nil? (map #(scp/externalized (sim/node-state s %))
                                           [:a :b :c]))))))))

;; ============================================================
;; The classic FBA scenario: per-node guarantees
;; ============================================================

(deftest quorum-intersection-is-the-precondition-and-it-is-checkable
  (is (scp/intertwined? tiered))
  (is (scp/intertwined? (into {} (map (fn [n] [n flat-qset])) flat-peers)))
  (is (scp/intertwined? (select-keys split [:a :b :c])))
  (is (scp/intertwined? (select-keys split [:d :e :f])))
  (is (not (scp/intertwined? split))
      "the two clusters share no node, so the system-wide theorem does not apply"))

(deftest befouled-node-loses-safety-while-its-neighbours-keep-theirs
  (testing "the result that has no analogue in any other algorithm here

           `:x`'s quorum set is satisfied by EITHER cluster, so which value it
           externalizes is decided by the network, not by the protocol. Run the
           same configuration under two partitions and `:x` decides differently
           -- while `:a :b :c` agree with each other in both runs, and
           `:d :e :f` agree with each other in both runs. Safety is a property
           of an intertwined SET, not of the system."
    (let [run (fn [parts]
                (-> (make-sim split {:seed 3 :values (merge (zipmap [:a :b :c] (repeat :left))
                                                            (zipmap [:d :e :f] (repeat :right))
                                                            {:x :left})})
                    (sim/partition-network parts)
                    (sim/run 300 (all-externalized? [:a :b :c :d :e :f]))
                    sim/heal
                    (sim/run 200)))
          x-with-left (run [#{:a :b :c :x} #{:d :e :f}])
          x-with-right (run [#{:a :b :c} #{:d :e :f :x}])
          val-of (fn [s p] (scp/externalized (sim/node-state s p)))]
      (testing "each intertwined cluster is internally consistent in both runs"
        (doseq [s [x-with-left x-with-right]]
          (is (= 1 (count (set (map #(val-of s %) [:a :b :c])))))
          (is (= 1 (count (set (map #(val-of s %) [:d :e :f])))))
          (is (= :left (val-of s :a)))
          (is (= :right (val-of s :d)))))
      (testing "and :x, which is intertwined with neither, follows whoever reached it"
        (is (= :left (val-of x-with-left :x)))
        (is (= :right (val-of x-with-right :x))))
      (testing "so system-wide agreement is FALSE, and correctly so"
        (is (not (sim/agreement? x-with-left)))))))

;; ============================================================
;; Byzantine behaviour
;; ============================================================

(deftest a-malformed-statement-is-dropped-not-asserted-against
  (let [impl (scp/make)
        {st :state} (node/init impl {:peer-id :a :qset flat-qset :qsets {:a flat-qset}})
        bogus [{:kind :prepare :from :evil :slot 0 :qset-hash (scp/qset-hash flat-qset)
                :ballot {:counter 0 :value :v}}                       ; counter 0
               {:kind :confirm :from :evil :slot 0 :qset-hash (scp/qset-hash flat-qset)
                :ballot {:counter 1 :value :v} :n-commit 5 :n-h 2}    ; c > h
               {:kind :externalize :from :evil :slot 0 :qset-hash (scp/qset-hash flat-qset)
                :commit {:counter 3 :value :v} :n-h 1}]]              ; h < c
    (doseq [msg bogus]
      (let [{st' :state} (node/step impl st (node/message-received :evil msg #{:evil}))]
        (is (nil? (get-in st' [:ballot-latest :evil])) (pr-str msg))))))

(deftest an-old-statement-cannot-be-replayed-alongside-a-new-one
  (testing "only the newest statement per sender counts

           A Byzantine node that could get a stale statement counted next to
           its current one would be voting twice -- the federated form of the
           duplicate-sender bug `node/distinct-voters` exists to stop."
    (let [impl (scp/make)
          h (scp/qset-hash flat-qset)
          {st :state} (node/init impl {:peer-id :a :qset flat-qset :qsets {:a flat-qset}})
          newer {:kind :confirm :from :b :slot 0 :qset-hash h
                 :ballot {:counter 2 :value :v} :n-prepared 2 :n-commit 1 :n-h 2}
          older {:kind :prepare :from :b :slot 0 :qset-hash h
                 :ballot {:counter 1 :value :v}}
          st1 (:state (node/step impl st (node/message-received :b newer #{:b})))
          st2 (:state (node/step impl st1 (node/message-received :b older #{:b})))]
      (is (= newer (get-in st2 [:ballot-latest :b])) "PREPARE never displaces CONFIRM")
      (is (= 1 (count (:ballot-latest st2)))))))

(deftest the-ballot-timer-gate-is-per-counter-and-the-timer-always-rearms
  (testing "two defects in the same seven lines, and each is contradicted by the
            other's comment.

            (1) `:heard-from-quorum?` was set once and never cleared, so the
            gate meant \"have I EVER heard from a quorum\" rather than \"at this
            counter\" -- exactly the counter-to-infinity race the gate's own
            comment says it prevents. stellar-core clears it in `bumpToBallot`
            (`BallotProtocol.cpp:475`).

            (2) When the gate DID suppress the abandon, the ballot timer died
            for good: `timer-effects` emits a `set-timer` only when the counter
            changes, and the interpreter has already removed the timer that
            fired. So a node that armed its timer before hearing from a quorum
            could never abandon that counter by timeout, even after a quorum
            spoke. stellar-core re-arms in exactly this branch
            (`ballotProtocolTimerExpired` -> `startBallotProtocolTimer`,
            `BallotProtocol.cpp:502-504`).

            Neither was exercised: `heard-from-quorum` and `timer-fired :ballot`
            appeared nowhere in the suite."
    (let [impl (scp/make)
          h (scp/qset-hash flat-qset)
          prepare (fn [from n] {:kind :prepare :from from :slot 0 :qset-hash h
                                :ballot {:counter n :value :v}})
          fire (fn [st] (node/step impl st (node/timer-fired :ballot)))
          ctr (fn [st] (:counter (first (scp/ballot-state st))))
          armed-ballot? (fn [fx]
                          (some (fn [e] (and (= :set-timer (node/effect-kind e))
                                             (= :ballot (:timer-id (node/effect-params e)))))
                                fx))
          nom (fn [from] {:kind :nominate :from from :slot 0 :qset-hash h
                          :votes #{:v} :accepted #{:v}})
          deliver-all (fn [st msgs]
                        (reduce (fn [st [from m]]
                                  (:state (node/step impl st (node/message-received from m #{from}))))
                                st msgs))
          {st0 :state} (node/init impl {:peer-id :a :qset flat-qset :qsets {:a flat-qset}
                                        :value :v})
          ;; Nomination first: `abandon-ballot` needs a composite candidate, so
          ;; without one a ballot never forms and the timer has nothing to gate.
          nominated (deliver-all st0 (map (fn [p] [p (nom p)]) [:b :c :d]))
          ;; A quorum of PREPARE at counter 1 then gives :a a ballot and, with
          ;; it, `heard-from-quorum?` at that counter.
          heard (deliver-all nominated (map (fn [p] [p (prepare p 1)]) [:b :c :d]))]
      (is (= 1 (ctr heard)) "a ballot at counter 1")
      (is (:heard-from-quorum? heard) "and a quorum has spoken at it")

      ;; First timeout: the gate is open, so abandon to counter 2.
      (let [r1 (fire heard)
            st1 (:state r1)]
        (is (= 2 (ctr st1)) "the timeout abandoned counter 1")
        (is (armed-ballot? (:effects r1)) "and armed the timer for counter 2")
        (is (not (:heard-from-quorum? st1))
            "the bump cleared the flag: nobody has spoken at counter 2 yet")

        ;; Every subsequent timeout, with no new statements, must be suppressed
        ;; -- and must still re-arm, or the node is deaf to its own timer for
        ;; the rest of the run.
        (let [st (reduce (fn [st _]
                           (let [r (fire st)]
                             (is (armed-ballot? (:effects r))
                                 "a suppressed timeout must still re-arm the timer")
                             (:state r)))
                         st1
                         (range 20))]
          (is (= 2 (ctr st))
              "twenty ballot timeouts on a node nobody is talking to must not
               move the counter at all"))

        ;; And once a quorum does speak at counter 2, the timeout works again.
        (let [heard2 (reduce (fn [st from]
                               (:state (node/step impl st (node/message-received
                                                           from (prepare from 2) #{from}))))
                             st1 [:b :c :d])
              st3 (:state (fire heard2))]
          (is (:heard-from-quorum? heard2))
          (is (= 3 (ctr st3)) "the gate reopens at the new counter"))))))

(deftest a-quorum-set-that-names-a-node-twice-is-rejected
  (testing "`QuorumSetSanityChecker` carries `mKnownNodes` across the WHOLE tree
            (`QuorumSetUtils.cpp:68-76`); checking uniqueness only within one
            validator list let

                {:threshold 2 :validators [:a] :inner-sets [{:threshold 1 :validators [:a]}]}

            through, and `quorum-slice?` then counts the single node :a twice
            toward a threshold of two. A peer can advertise such a set over the
            wire (`handle-message :qset` validates with exactly this predicate),
            so one accomplice satisfies what looks like a two-node quorum."
    (is (scp/valid-qset? {:threshold 2 :validators [:a :b]}))
    (is (not (scp/valid-qset? {:threshold 2 :validators [:a]
                               :inner-sets [{:threshold 1 :validators [:a]}]})))
    (is (not (scp/valid-qset? {:threshold 2
                               :inner-sets [{:threshold 1 :validators [:a :b]}
                                            {:threshold 1 :validators [:b :c]}]}))
        "repeats across two inner sets count too")
    (is (scp/valid-qset? {:threshold 2
                          :inner-sets [{:threshold 1 :validators [:a :b]}
                                       {:threshold 1 :validators [:c :d]}]}))))

(deftest a-zero-threshold-satisfies-nothing
  (testing "`isQuorumSliceInternal`'s unsigned `thresholdLeft--` underflows
            rather than passing, so a zero threshold is never a slice.
            `v-blocking?` already guarded this and `quorum-slice?` did not, and
            the two must agree -- `:qsets`/`:known-qsets` supplied through config
            bypass `valid-qset?` entirely, which is the path every test uses."
    (is (not (scp/quorum-slice? {:threshold 0 :validators [:a :b]} #{})))
    (is (not (scp/quorum-slice? {:threshold 0 :validators [:a :b]} #{:a :b})))
    (is (not (scp/v-blocking? {:threshold 0 :validators [:a :b]} #{:a :b})))
    (is (scp/quorum-slice? {:threshold 1 :validators [:a :b]} #{:a}))))

(declare corrupt)

(defn- corrupt
  "Rewrite one outbound effect, descending into the durability barrier.

  Descending into `:then` is not optional: SCP's statements are its binding
  commitment, so every one of them leaves through a `persist-then`, and an
  adversary that only rewrote bare broadcasts could not equivocate at all."
  [f effect]
  (case (node/effect-kind effect)
    :broadcast (or (f (:msg (node/effect-params effect))) [effect])
    :persist-then (let [p (node/effect-params effect)]
                    [[:persist-then (update p :then #(vec (mapcat (partial corrupt f) %)))]])
    [effect]))

(defrecord Adversary [inner f]
  node/Node
  (capabilities [_] (node/capabilities inner))
  (init [_ cfg] (update (node/init inner cfg) :effects #(vec (mapcat (partial corrupt f) %))))
  (step [_ st in] (update (node/step inner st in) :effects #(vec (mapcat (partial corrupt f) %)))))

(def two-ballots
  "Send two PREPARE statements for the same slot with DIFFERENT values.

  This is the one lie that matters in SCP. A federated vote is a claim about a
  value at a ballot, so voting for two incompatible values at once is the
  federated form of double-signing, and it is the reason `federated-accept`
  needs the v-blocking clause to be sound rather than merely convenient."
  (fn [msg]
    (when (= :prepare (:kind msg))
      [(node/broadcast :scp (assoc-in msg [:ballot :value] :lie-one))
       (node/broadcast :scp (assoc-in msg [:ballot :value] :lie-two))])))

(deftest intertwined-nodes-agree-despite-an-equivocator
  (testing "the adversary FBA is actually about, which no simulation here ran.

           Every other Byzantine story in this file is a malformed or replayed
           statement checked one step at a time. The real one is a node that
           tells different peers different things, and it matters because
           `intertwined?` -- quorum intersection -- is only the right
           precondition once nodes can lie. Under crash and partition alone,
           plain intersection would have done.

           :d equivocates at every ballot, sending PREPARE for two incompatible
           values. At threshold 3 of 4, any two quorums are two 3-subsets of a
           4-set, so they share at least two nodes and therefore at least one
           WELL-BEHAVED node whatever :d does. That is exactly the hypothesis of
           SCP's safety theorem, and the three honest nodes must agree."
    (doseq [seed [1 4 9]]
      (let [peers [:a :b :c :d]
            honest [:a :b :c]
            s0 (sim/make {:seed seed
                          :nodes (into {} (map (fn [p]
                                                 [p (if (= :d p)
                                                      (->Adversary (scp/make) two-ballots)
                                                      (scp/make))]))
                                       peers)
                          :node-config (into {} (map (fn [p] [p {:qset flat-qset
                                                                 :qsets flat-qset-config
                                                                 :value p}]))
                                             peers)})
            ;; Stepped, not run in one go, because the WITNESS has to be
            ;; sampled while the lies are current. :d's latest statement at the
            ;; end of the run is an honest EXTERNALIZE -- the adversary only
            ;; rewrites PREPARE, and `isNewerStatement` keeps the newest -- so
            ;; looking at the final state shows no equivocation at all and the
            ;; witness silently passes for a test in which nobody ever lied.
            [s heard] (loop [s s0, t 0, heard #{}]
                        (let [heard (into heard
                                          (keep #(get-in (sim/node-state s %)
                                                         [:ballot-latest :d :ballot :value]))
                                          honest)]
                          (if (or (>= t 400) (and (> t 0) ((all-externalized? honest) s)))
                            [s heard]
                            (recur (sim/run s 4) (+ t 4) heard))))
            vals* (mapv #(scp/externalized (sim/node-state s %)) honest)]
        (is (scp/intertwined? (into {} (map (fn [p] [p flat-qset])) honest))
            "the hypothesis of the theorem being tested")
        (is (every? some? vals*)
            (str "seed " seed ": the honest nodes must actually DECIDE, or the
                  agreement assertion below is satisfied by three nils"))
        (is (= 1 (count (set vals*)))
            (str "seed " seed ": honest nodes externalized " (pr-str vals*)))
        (is (not-any? #{:lie-one :lie-two} vals*)
            (str "seed " seed ": and never a value only the equivocator voted for"))
        ;; The adversary must actually have been heard, or this test is three
        ;; honest nodes running an ordinary simulation.
        (is (seq (filter #{:lie-one :lie-two} heard))
            (str "seed " seed ": a lie must actually have been recorded by an
                  honest node -- otherwise this is three honest nodes running an
                  ordinary simulation. Heard: " (pr-str heard)))
        ;; `heard` accumulates across three nodes and the whole run, so it can
        ;; well hold both lies. What it cannot show is two live at once in ONE
        ;; node: `isNewerStatement` keeps the newest statement per sender, so
        ;; :d's second lie displaces its first and the equivocator gets exactly
        ;; one vote. That is `node/distinct-voters` at the federated level and it
        ;; is pinned where it belongs, in
        ;; `an-old-statement-cannot-be-replayed-alongside-a-new-one`.
        ))))

(deftest statements-for-another-slot-are-ignored
  (let [impl (scp/make)
        {st :state} (node/init impl {:peer-id :a :qset flat-qset :qsets {:a flat-qset} :slot 0})
        {st' :state} (node/step impl st (node/message-received
                                         :b (assoc (nominate-msg :b flat-qset [:v]) :slot 7)
                                         #{:b}))]
    (is (empty? (:nom-latest st')))))

(deftest one-peer-cannot-manufacture-a-quorum-by-naming-other-authors
  (testing "the author of a statement must be the peer that sent it

           `record-statement` filed statements under the BODY's `:from` and was
           never given the sender at all. Federated voting's whole safety
           argument is that a slice cannot be satisfied without genuinely
           distinct nodes -- so one peer, sending four statements that name :a,
           :b, :c and :d in turn, satisfied any slice by itself.

           This is independent of transport authentication: it breaks with a
           perfect wire too, because the missing check is not whether the sender
           is who they claim, but whether the author is the sender. Every
           existing SCP test is honest, and an honest node's statements are
           self-authored, so nothing here could see it.

           Note both directions below. :b's own statement is still accepted --
           the fix must reject impersonation, not correspondence."
    (let [impl (scp/make)
          {st :state} (node/init impl {:peer-id :a :qset flat-qset
                                       :qsets {:a flat-qset} :slot 0})
          ;; :b speaks for everyone.
          forged (reduce (fn [s author]
                           (:state (node/step impl s
                                              (node/message-received
                                               :b (nominate-msg author flat-qset [:v])
                                               #{:b}))))
                         st
                         [:a :b :c :d])]
      (is (= #{:b} (set (keys (:nom-latest forged))))
          "only :b's own statement was recorded; the other three were forgeries")
      (is (some? (get-in forged [:nom-latest :b]))
          "and :b speaking as :b is still perfectly good"))))

(deftest a-statement-from-an-unverified-sender-is-dropped
  (testing "SCP never looked at `verified-by` at all, while Tendermint and
           Bullshark both did. Under `:auth :none` the set is empty, so an
           unauthenticated deployment now visibly refuses to progress instead of
           quietly believing a self-declared name."
    (let [impl (scp/make)
          {st :state} (node/init impl {:peer-id :a :qset flat-qset
                                       :qsets {:a flat-qset} :slot 0})
          {st' :state} (node/step impl st (node/message-received
                                           :b (nominate-msg :b flat-qset [:v])
                                           #{}))]
      (is (empty? (:nom-latest st'))))))

;; ============================================================
;; Durability
;; ============================================================

(deftest the-broadcast-is-gated-behind-the-durability-barrier
  (testing "SCP's whole ballot state is a binding commitment: a node that forgot
           it had accepted a commit could externalize a contradictory value
           after a restart. So `b/p/p'/h/c` is written and the statement rides
           in the write's `:then`."
    (let [impl (scp/make)
          {st :state fx0 :effects} (node/init impl {:peer-id :a :qset flat-qset :value :v})
          [_ fx1] (speak-up impl st)
          fx (into (vec fx0) fx1)
          persists (filter #(= :persist-then (node/effect-kind %)) fx)]
      (is (seq persists))
      (is (empty? (filter node/outbound? fx))
          "nothing goes on the wire outside a barrier")
      (is (every? #(seq (node/deferred-effects %)) persists))
      (is (every? #(contains? (:writes (node/effect-params %)) :scp) persists))
      (is (every? #(every? node/outbound? (node/deferred-effects %)) persists)
          "and what the barrier gates is exactly the statement"))))

(deftest a-restart-resumes-from-durable-state-only
  (let [crashed (-> (make-sim tiered {:seed 6}) (sim/run 14) (sim/crash :a))
        before (sim/node-state crashed :a)
        restarted (sim/restart crashed :a)
        resumed (sim/node-state restarted :a)]
    (testing "it resumes at exactly the last write that LANDED -- not at the
             last one issued, because a write still in flight when the node
             died is genuinely lost, which is the whole point of the barrier"
      (let [landed (:scp (:writes (last (get-in crashed [:storage :a :landed]))))]
        (is (some? landed))
        (is (= (select-keys landed [:phase :b :p :pp :h :c])
               (select-keys resumed [:phase :b :p :pp :h :c]))))
      (is (= (scp/phase before) (scp/phase resumed)))
      (is (<= (scp/compare-ballots (:b resumed) (:b before)) 0)
          "and never ahead of where it actually was"))
    (testing "other nodes' statements did NOT come back -- they were never ours
             to keep, and the node re-learns them from the gossip timer"
      (is (seq (:ballot-latest before)))
      (is (empty? (:ballot-latest resumed)))
      (is (empty? (:nom-latest resumed))))
    (testing "and it still finishes, agreeing with everyone else"
      (let [s (sim/run restarted 500 (all-externalized? [:a :b :c :d]))]
        (is (every? #(scp/externalized (sim/node-state s %)) [:a :b :c :d]))
        (is (= 1 (count (set (vals (externalized-by s))))))))))

;; ============================================================
;; Configuration
;; ============================================================

(deftest a-flat-validator-list-is-refused
  (testing "the simulator hands every node `:validators`, which for SCP means
           nothing at all. Silently accepting it would be the `node`
           missing-:validators bug in reverse -- a configuration that looks
           complete and encodes no trust. Refuse loudly."
    (is (thrown? clojure.lang.ExceptionInfo
                 (node/init (scp/make) {:peer-id :a :validators [:a :b :c :d]})))
    (is (thrown? clojure.lang.ExceptionInfo
                 (node/init (scp/make) {:peer-id :a :qset {:threshold 0 :validators [:a]}}))
        "a threshold of zero makes every set a quorum")
    (is (thrown? clojure.lang.ExceptionInfo
                 (node/init (scp/make) {:peer-id :a :qset {:threshold 3 :validators [:a :b]}}))
        "a threshold no set can reach is a node that can never decide")))

(deftest the-simulators-validators-key-is-ignored
  (testing "and the node works without ever reading it"
    (let [s (run-to-consensus flat-qset-config)]
      (is (every? #(nil? (:validators (sim/node-state s %))) flat-peers)))))

;; ============================================================
;; The self-check
;; ============================================================

(deftest check-invariants-catches-every-state-it-is-meant-to
  (testing "`BallotProtocol::checkInvariants` (`BallotProtocol.cpp:624-656`).

            None of these states is reachable from a well-behaved transition --
            that is the point of a self-check, and it is also why it has to be
            tested by CONSTRUCTING them. A check that has only ever been run on
            states that satisfy it is not known to be a check at all.

            stellar compiles these out of release builds under `dbgAssert`. We
            do not: the cost is six comparisons beside a fixpoint of eleven
            rules, and a check absent from the build that matters is not a
            check."
    (let [ok {:phase :prepare :b {:counter 1 :value :v}}
          ball (fn [n v] {:counter n :value v})]
      (is (= ok (scp/check-invariants ok)) "a sane state passes through")

      (is (thrown-with-msg? Exception #"counter 0"
                            (scp/check-invariants {:phase :prepare :b (ball 0 :v)})))

      (is (thrown-with-msg? Exception #"incompatible with p"
                            (scp/check-invariants {:phase :prepare
                                                   :b (ball 3 :v)
                                                   :p (ball 1 :v)
                                                   :pp (ball 2 :v)}))
          "p' must be LESS than p and incompatible; here it is greater and
           compatible, which is two violations at once")

      (is (thrown-with-msg? Exception #"no current ballot"
                            (scp/check-invariants {:phase :prepare :c (ball 1 :v)})))

      (is (thrown-with-msg? Exception #"c must be <= h"
                            (scp/check-invariants {:phase :prepare
                                                   :b (ball 5 :v)
                                                   :c (ball 4 :v)
                                                   :h (ball 2 :v)}))
          "c above h")

      (is (thrown-with-msg? Exception #"h must be <= b"
                            (scp/check-invariants {:phase :prepare
                                                   :b (ball 1 :v)
                                                   :c (ball 1 :v)
                                                   :h (ball 3 :v)}))
          "h above b")

      (is (thrown-with-msg? Exception #"CONFIRM without c"
                            (scp/check-invariants {:phase :confirm :b (ball 1 :v)})))

      ;; EXTERNALIZE with c but no h reports the C/H violation, not the phase
      ;; one, because the `c` block runs BEFORE the phase switch -- as it does
      ;; in stellar, where `if (mCommit)` precedes it. Which makes the
      ;; `dbgAssert(mHighBallot)` in the EXTERNALIZE arm unreachable: with c set
      ;; the earlier block already required h, and with c absent the earlier
      ;; arm fires first. Reproduced anyway rather than tidied, since which
      ;; assert fires is not a behaviour anyone should depend on.
      (is (thrown-with-msg? Exception #"c must be <= h"
                            (scp/check-invariants {:phase :externalize
                                                   :b (ball 1 :v) :c (ball 1 :v)})))

      (is (thrown-with-msg? Exception #"EXTERNALIZE without c"
                            (scp/check-invariants {:phase :externalize :b (ball 1 :v)})))

      (is (thrown-with-msg? Exception #"unknown phase"
                            (scp/check-invariants {:phase :nonsense}))
          "an unrecognised phase is refused rather than passed over -- the same
           rule `schedule` applies to an unknown step"))))

;; ============================================================
;; Durability, and the two stalls
;; ============================================================

(deftest the-commit-rides-behind-the-durability-barrier
  (testing "SAFETY. `finish` used to concatenate the commit BEFORE the write,
            so the application was told a value had externalized while the
            state justifying it was still in flight. stellar-core has the
            opposite order: `setConfirmCommit` emits the statement
            (BallotProtocol.cpp:1469) before `valueExternalized` (:1473), and
            `persistSCPState` (HerderImpl.cpp:865) runs before the broadcast.

            The node is forced into the one state where both a commit and a
            write are pending. Asserting on a settled node proves nothing --
            `commit-effects` fires once, so a settled node emits no commit
            whichever order `finish` uses, and an earlier version of this test
            passed against the bug for exactly that reason."
    (let [s (sim/run (make-sim flat-qset-config {:values {:a :v :b :v :c :v :d :v}}) 200)
          decided (first (filter #(= :externalize (scp/phase (sim/node-state s %)))
                                 flat-peers))]
      (is (some? decided) "someone externalized, or this test proves nothing")
      (let [st (-> (sim/node-state s decided)
                   ;; Undelivered commit, and a statement that still needs
                   ;; sending -- so this step must produce both.
                   (assoc :committed? false :sent-ballot nil))
            {fx :effects} (node/step (scp/make) st (node/timer-fired :gossip))
            bare (filter #(= :commit (node/effect-kind %)) fx)
            gated (->> fx
                       (filter #(= :persist-then (node/effect-kind %)))
                       (mapcat #(:then (node/effect-params %)))
                       (filter #(= :commit (node/effect-kind %))))]
        (is (empty? bare)
            "a commit outside the barrier is a decision exposed before the state
             that justifies it is durable")
        (is (= 1 (count gated))
            "it must be there, inside the write's :then")))))

(deftest a-restart-after-externalizing-re-announces-the-decision
  (testing "SAFETY. `:externalized` and `:committed?` are not persisted and
            cannot be -- they record what the APPLICATION was told. But `phase`
            and `:c` are, and in `:externalize` they say which value was
            decided, so the decision is recoverable even though the delivery is
            not. Without this a node that crashed between the fsync and the
            commit reaching the application came back in `:externalize`,
            re-broadcast its EXTERNALIZE to peers, and told its own application
            nothing at all."
    (let [s (sim/run (make-sim flat-qset-config {:values {:a :v :b :v :c :v :d :v}}) 200)
          decided (first (filter #(= :externalize (scp/phase (sim/node-state s %)))
                                 flat-peers))]
      (is (some? decided) "someone externalized")
      (let [s2 (sim/restart (sim/crash s decided) decided)
            st (sim/node-state s2 decided)]
        (is (= :externalize (scp/phase st)) "the phase came back from disk")
        (is (some? (scp/externalized st))
            "and the decision with it, derived from phase and :c")
        (is (seq (filter #(= :resync (:event %)) (:trace s2)))
            "announced as a resync -- a restarting node stating its committed
             prefix, not extending it")))))

;; ============================================================
;; What one request may cost us
;; ============================================================

(deftest a-qset-we-never-asked-for-is-not-cached
  (testing "`:requested` was already tracked and already `disj`'d in this
            handler -- the membership test was simply never made

           So any peer could push unlimited quorum sets into `:known-qsets`,
           each up to `max-qset-nodes` entries, and nothing ever removed them.
           One message per entry, permanent, on every node that received it.

           The content-addressing check is about a DIFFERENT attack -- a forged
           preimage for a hash we wanted -- and does nothing about volume: an
           attacker hashing its own quorum sets satisfies it every time."
    (let [impl (scp/make)
          {st :state} (node/init impl {:peer-id :a :qset flat-qset
                                       :qsets {:a flat-qset} :slot 0})
          unsolicited (assoc flat-qset :threshold 2)
          h (scp/qset-hash unsolicited)
          pushed (:state (node/step impl st (node/message-received
                                             :b {:kind :qset :hash h :qset unsolicited}
                                             #{:b})))]
      (is (not (contains? (:known-qsets pushed) h))
          "a correctly-hashed quorum set we never requested is still refused")
      ;; And one we DID ask for is accepted, or the guard is just a wall.
      (let [wanting (assoc st :requested #{h})
            got (:state (node/step impl wanting (node/message-received
                                                 :b {:kind :qset :hash h :qset unsolicited}
                                                 #{:b})))]
        (is (contains? (:known-qsets got) h)
            "while the answer to a fetch we issued is still taken")))))

(deftest own-qset-is-served-with-a-shared-gossip-window-budget
  (let [impl (scp/make)
        init (fn [cfg] (:state (node/init impl (merge {:peer-id :a :qset flat-qset} cfg))))
        h (scp/qset-hash flat-qset)
        ask (fn [st peer hash]
              (node/step impl st (node/message-received peer {:kind :get-qset :hash hash} #{peer})))
        reply? (fn [r] (some #(= :qset (get-in (node/effect-params %) [:msg :kind])) (:effects r)))
        st (init {:qset-reply-limit 2})
        first-reply (ask st :outside h)
        second-reply (ask (:state first-reply) :another h)
        expired (node/step impl (:state second-reply) (node/timer-fired :gossip))]
    (is (reply? first-reply) "a validator can trust us without reciprocal membership")
    (is (not (reply? (ask (:state first-reply) :outside h))))
    (is (reply? second-reply))
    (is (not (reply? (ask (:state second-reply) :third h))))
    (is (reply? (ask (:state expired) :outside h)))
    (is (not (reply? (ask (init {:qset-reply-bytes 1}) :outside h))))
    (is (not (reply? (ask st :outside :unknown))))))

(deftest a-nomination-carrying-too-many-values-is-refused
  (testing "`nomination-rule` runs `federated-accept` ONCE PER DISTINCT VALUE,
            and each is two greatest fixpoints over `survivors` plus a
            `v-blocking?` walk. The sanity check required only that a statement
            carry SOME value, so one message with a million of them bought a
            million fixpoints inside `step` -- itself inside `settle`'s
            200-iteration fixpoint.

           Refused, not truncated: dropping values would silently change which
           of them federated voting could accept, which is a correctness change
           smuggled in as a resource bound."
    (let [many (into #{} (map (fn [i] [:v i])) (range (inc scp/max-nomination-values)))
          ok   (into #{} (map (fn [i] [:v i])) (range 10))]
      (is (false? (boolean (scp/statement-sane?
                            {:kind :nominate :from :b :slot 0
                             :votes many :accepted #{}})))
          "above the cap it is malformed")
      (is (true? (boolean (scp/statement-sane?
                           {:kind :nominate :from :b :slot 0
                            :votes ok :accepted #{}})))
          "an ordinary nomination is untouched")
      (is (false? (boolean (scp/statement-sane?
                            {:kind :nominate :from :b :slot 0
                             :votes #{} :accepted #{}})))
          "and an empty one is still malformed, as it always was")
      (is (false? (boolean (scp/statement-sane?
                            {:kind :nominate :from :b :slot 0
                             :votes (into #{} (take 200 many))
                             :accepted (into #{} (take 200 (drop 200 many)))})))
          "the cap is over votes AND accepted together, since both are walked"))))

(deftest self-omitting-federation-nominates-without-preloaded-sets
  (let [qsets (into {} (for [p flat-peers]
                         [p {:threshold 2 :validators (vec (remove #{p} flat-peers))}]))
        s (run-to-consensus qsets {:seed-qsets? false :ticks 500})]
    (is (every? some? (vals (externalized-by s))))
    (is (= 1 (count (set (vals (externalized-by s))))))))

(deftest gossip-replays-only-statements-with-completed-writes
  (let [impl (scp/make)
        cfg {:peer-id :a :qset {:threshold 2 :validators [:a :b]} :value :v}
        init (node/init impl cfg)
        [st more] (speak-up impl (:state init))
        effect (first (filter #(= :persist-then (node/effect-kind %))
                              (concat (:effects init) more)))
        w (node/effect-params effect)
        gossip (fn [st] (node/step impl st (node/timer-fired :gossip)))
        kinds (fn [r] (mapv node/effect-kind (:effects r)))
        pending (gossip st)
        landed (node/step impl (:state pending) (node/persisted (:token w) (:epoch w)))
        stable (gossip (:state landed))
        mixed (gossip (scp/bump-state (:state landed) :v 1))
        repeated (gossip (:state mixed))
        messages (fn [fx] (map #(get-in (node/effect-params %) [:msg :kind])
                               (filter #(= :broadcast (node/effect-kind %)) fx)))
        restart (node/init impl (assoc cfg :restored {:durable (:writes w)}))]
    (is (some? effect))
    (is (not-any? #{:broadcast :persist-then} (kinds pending)))
    (is (some #{:broadcast} (kinds stable)))
    (is (not-any? #{:persist-then} (kinds stable)))
    (is (= [:nominate] (messages (:effects mixed))))
    (is (= [:prepare] (messages (mapcat node/deferred-effects (:effects mixed)))))
    (is (= [:nominate] (messages (:effects repeated))))
    (is (not-any? #{:persist-then} (kinds repeated)))
    (is (not-any? #{:persist-then} (kinds restart)))
    (is (some #{:broadcast} (kinds (gossip (:state restart)))))))

(deftest quorum-intersection-requires-a-quorum-and-an-honest-intersection
  (is (false? (scp/intertwined? {})))
  (is (false? (scp/intertwined? {:a {:threshold 1 :validators [:absent]}})))
  (is (scp/intertwined? flat-qset-config #{:a}))
  (is (false? (scp/intertwined? flat-qset-config #{:a :b}))))

(deftest asymmetric-observer-discovers-the-quorum-set
  (let [observer-qset {:threshold 2 :validators [:a :b :c]}
        qsets (assoc flat-qset-config :observer observer-qset)
        s (run-to-consensus qsets {:seed-qsets? false :ticks 500})]
    (is (every? some? (vals (externalized-by s))))
    (is (= 1 (count (set (vals (externalized-by s))))))
    (is (= flat-qset (get-in (sim/node-state s :observer)
                             [:known-qsets (scp/qset-hash flat-qset)])))))

(deftest externalized-gossip-stops-growing-the-store
  (let [s (sim/run (make-sim flat-qset-config {}) 150)
        writes (fn [s] (count (get-in s [:storage :a :writes])))
        later (sim/run s 100)]
    (is (some? (scp/externalized (sim/node-state s :a))))
    (is (pos? (writes s)))
    (is (= (writes s) (writes later)))))
