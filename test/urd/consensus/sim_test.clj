(ns urd.consensus.sim-test
  "Tests for the deterministic simulator and its PRNG.

  The property that matters most here is REPRODUCIBILITY: a run must be a pure
  function of its seed and configuration, including under faults. If that ever
  breaks, every algorithm test built on the simulator becomes unfalsifiable,
  because a failure could not be re-examined."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.rng :as rng]
            [urd.consensus.sim :as sim]))

;; ============================================================
;; RNG
;; ============================================================

(deftest rng-is-deterministic
  (testing "the same seed yields the same sequence"
    (let [draw (fn [seed k]
                 (loop [r (rng/make seed), acc [], i 0]
                   (if (= i k)
                     acc
                     (let [[w r'] (rng/next-word r)] (recur r' (conj acc w) (inc i))))))]
      (is (= (draw 42 20) (draw 42 20)))
      (is (not= (draw 42 20) (draw 43 20))))))

(deftest rng-stays-in-32-bits
  (testing "values are 32-bit unsigned, so clj and cljs agree bit-for-bit"
    (let [words (loop [r (rng/make 12345), acc [], i 0]
                  (if (= i 500)
                    acc
                    (let [[w r'] (rng/next-word r)] (recur r' (conj acc w) (inc i)))))]
      (is (every? #(and (>= % 0) (<= % 0xFFFFFFFF)) words))
      (is (> (count (distinct words)) 450) "should not cycle quickly"))))

(deftest rng-zero-seed-is-not-a-fixed-point
  (testing "xorshift has 0 as a fixed point; seed 0 must be remapped"
    (let [[w _] (rng/next-word (rng/make 0))]
      (is (pos? w) "seed 0 would otherwise emit only zeros"))))

(deftest from-key-decorrelates-structured-seeds
  (testing "seeding from a structured key must not preserve its structure.

            xorshift32 is GF(2)-linear, so one round is a permutation rather
            than a mixing function and a structured difference between seeds
            survives into the output. SCP hit this hardest: djb2 gave four peers
            consecutive multiples of 33, and the highest node id led every round
            of every slot. Raft's election lottery, seeded the same way, was
            skewed by 4.4 sigma.

            Measured over unique minima only -- an earlier version of this
            measurement used `min-key`, which returns its LAST argument on ties,
            and with five peers drawing from ten values ties are common enough
            that the tie-break dominated the result. It made the bias look worse
            than it was AND made the fix look ineffective."
    (let [peers [:a :b :c :d :e]
          et 10
          n 4000
          draw (fn [seed-fn p t]
                 (let [[w _] (rng/next-word (seed-fn (+ (* 33 (count (name p))) (* 7 (int (first (name p)))) t)))]
                   (+ et (mod w et))))
          wins (fn [seed-fn]
                 (frequencies
                  (remove nil?
                          (for [t (range n)]
                            (let [ts (into {} (for [p peers] [p (draw seed-fn p t)]))
                                  m (apply min (vals ts))
                                  w (filter #(= m (ts %)) peers)]
                              (when (= 1 (count w)) (first w)))))))
          spread (fn [ws]
                   (let [total (reduce + (vals ws))
                         expected (/ (double total) (count peers))
                         sigma (Math/sqrt (* total 0.2 0.8))]
                     (/ (apply max (map #(abs (- % expected)) (vals ws))) sigma)))]
      (is (< (spread (wins rng/from-key)) 3.0)
          "from-key must produce a fair lottery (within 3 sigma)")
      (is (= 5 (count (wins rng/from-key)))
          "every peer must win sometimes"))))

(defspec rng-next-int-respects-bounds 200
  (prop/for-all [seed gen/nat
                 n (gen/choose 1 1000)]
                (let [[v _] (rng/next-int (rng/make seed) n)]
                  (and (>= v 0) (< v n)))))

(defspec rng-shuffle-is-a-permutation 200
  (prop/for-all [seed gen/nat
                 coll (gen/vector gen/small-integer 0 30)]
                (let [[shuffled _] (rng/shuffle (rng/make seed) coll)]
                  (= (frequencies coll) (frequencies shuffled)))))

(defspec rng-weighted-bag-draws-k-units-without-replacement 200
  (prop/for-all [seed gen/nat
                 k (gen/choose 1 40)]
                ;; Avalanche's sampling semantics, and both halves matter.
                ;;
                ;; The bag is a BAG: stake weight is what is drawn, so a node
                ;; CAN appear more than once and its multiplicity is its vote
                ;; weight in the poll.
                ;;
                ;; But the draw is WITHOUT REPLACEMENT over the units, so a node
                ;; can never appear more times than it has weight, and the bag
                ;; caps at the total weight rather than always totalling k. This
                ;; used to draw WITH replacement -- the same test passed, because
                ;; it asserted only the total -- and the consequence was that one
                ;; unit-weight peer out of four could fill an entire k=3 sample,
                ;; clearing alpha on its own.
                (let [weights {:a 1 :b 2 :c 5}
                      total 8
                      [bag _] (rng/sample-weighted-bag
                               (rng/make seed) [:a :b :c] weights k)]
                  (and (= (min k total) (reduce + 0 (vals bag)))
                       (every? (fn [[peer m]] (<= m (weights peer))) bag)))))

;; ============================================================
;; A toy node used to drive the simulator
;; ============================================================

(defrecord Decree []
  n/Node
  ;; Derived from what it emits, not guessed: the durable variant below gates
  ;; its commit behind a write, so `:persist-then` belongs here too.
  (capabilities [_] {:emits #{:broadcast :persist-then :commit}})
  (init [_ config]
    (let [peer-id (:peer-id config)]
      (n/result {:peer-id peer-id
                 :validators (:validators config)
                 :heard {peer-id peer-id}
                 :committed? false}
                [(n/broadcast :propose {:from peer-id :value peer-id})])))
  (step [_ state input]
    (if (= :message-received (:type input))
      (let [{:keys [from value]} (:msg input)
            heard (assoc (:heard state) from value)
            need (n/byzantine-threshold (count (:validators state)))]
        (if (and (not (:committed? state)) (>= (count heard) need))
          (n/result (assoc state :heard heard :committed? true)
                    [(n/persist-then {:writes {:decision (first (sort (vals heard)))}
                                      :epoch 1
                                      :then [(n/commit [(first (sort (vals heard)))])]})])
          (n/result (assoc state :heard heard))))
      (n/result state))))

(def peers [:a :b :c :d])

(defn- fresh [& [cfg]]
  (sim/make {:seed 7 :nodes (zipmap peers (repeat (->Decree))) :config (or cfg {})}))

;; ============================================================
;; Simulator behaviour
;; ============================================================

(deftest converges-on-a-quiet-network
  (let [s (sim/run (fresh) 60 sim/quiet?)]
    (is (sim/agreement? s))
    (is (every? seq (vals (sim/all-committed s))) "every node committed")))

(deftest persist-barrier-precedes-the-commit
  (testing "a commit gated behind persist-then only lands after the write"
    (let [s (sim/run (fresh) 60 sim/quiet?)
          writes (get-in s [:storage :a :writes])]
      (is (seq writes) "the durable write was recorded")
      (is (:durable? (first writes)) "and it was an fsync, not a buffered write"))))

(deftest partition-blocks-quorum
  (testing "a 2/2 split cannot reach a quorum of 3"
    (let [s (-> (fresh) (sim/partition-network [#{:a :b} #{:c :d}]) (sim/run 40))]
      (is (every? empty? (vals (sim/all-committed s)))))))

(deftest majority-side-of-a-partition-still-commits
  (testing "a 3/1 split lets the majority side finish; the minority stalls"
    (let [s (-> (fresh) (sim/partition-network [#{:a :b :c} #{:d}]) (sim/run 40))]
      (is (seq (sim/committed s :a)))
      (is (empty? (sim/committed s :d)))
      (is (sim/agreement? s) "a lagging node is not a disagreeing node"))))

(deftest restart-discards-in-memory-state
  (testing "restart replays from DURABLE state only"
    (let [s0 (sim/run (fresh) 3)
          before (sim/node-state s0 :b)
          s1 (sim/restart (sim/crash s0 :b) :b)
          after (sim/node-state s1 :b)]
      (is (> (count (:heard before)) (count (:heard after)))
          "unpersisted in-memory state must be lost, or the simulator would
           hide exactly the durability bugs it exists to find")
      (is (some? (get-in s1 [:storage :b])) "durable storage survives"))))

(deftest crashed-nodes-do-not-step
  (let [s (-> (fresh) (sim/run 2) (sim/crash :a))
        before (sim/node-state s :a)
        after (sim/node-state (sim/run s 20) :a)]
    (is (= before after))))

(deftest simulator-detects-a-real-agreement-violation
  (testing "the toy algorithm is genuinely unsafe under message loss, and the
            simulator catches it -- this is a regression test for the DETECTOR,
            not for the algorithm.

            `Decree` commits the minimum of whatever it happened to hear once it
            has a quorum's worth. Under loss, different nodes hold different
            subsets, so they commit different values. A simulator that reported
            agreement here would be useless."
    (let [s (sim/run (fresh {:drop-rate 0.3}) 60)
          committed (vals (sim/all-committed s))
          non-empty (remove empty? committed)]
      (is (> (count (distinct non-empty)) 1)
          "expected divergent commits under 30% loss")
      (is (not (sim/agreement? s))
          "and agreement? must report the violation"))))

;; ============================================================
;; Self-delivery and persist-token correlation
;; ============================================================

(defrecord SelfTalker []
  n/Node
  (capabilities [_] {:emits #{:persist-then :deliver-self}})
  (init [_ config]
    (n/result {:peer-id (:peer-id config) :got [] :acks []}
              ;; A self-addressed input placed BEHIND the durability barrier.
              ;; This is etcd's trick: the leader learns its own append landed
              ;; only once the write is durable.
              [(n/persist-then {:writes {:hard :state}
                                :epoch 7
                                :token :my-write-1
                                :then [(n/deliver-self {:type :self-ack :tag :after-fsync})]})
               (n/deliver-self {:type :self-ack :tag :immediate})]))
  (step [_ state input]
    (case (:type input)
      :self-ack (n/result (update state :got conj (:tag input)))
      :persisted (n/result (update state :acks conj [(:token input) (:epoch input)]))
      (n/result state))))

(deftest self-delivery-works-and-survives-a-hostile-network
  (testing "a node can address an input to itself; it is never dropped and
            never partitioned, unlike [:send {:to self}]"
    (let [s (sim/run (sim/make {:seed 1
                                :nodes {:solo (->SelfTalker)}
                                ;; Total loss and a partition of one: a network
                                ;; send would have no chance of arriving.
                                :config {:drop-rate 1.0}})
                     20)
          st (sim/node-state s :solo)]
      (is (= #{:immediate :after-fsync} (set (:got st)))
          "both self-deliveries arrived despite a 100% drop rate"))))

(deftest persist-token-is-caller-supplied
  (testing "the node names its own write, so it can correlate the completion.

            Previously the interpreter minted the token, which forced any
            algorithm with more than one write in flight to assume completions
            arrive in issue order -- an ordering the protocol never promised."
    (let [s (sim/run (sim/make {:seed 1 :nodes {:solo (->SelfTalker)}}) 20)
          st (sim/node-state s :solo)]
      (is (= [[:my-write-1 7]] (:acks st))
          "the token and epoch came back exactly as supplied"))))

(deftest self-delivery-does-not-recurse-within-a-step
  (testing "delivery is queued to the next tick, so a node emitting a
            self-delivery from its own handler cannot loop forever"
    (let [looper (reify n/Node
                   (capabilities [_] {:emits #{:deliver-self}})
                   (init [_ c] (n/result {:peer-id (:peer-id c) :n 0}
                                         [(n/deliver-self {:type :ping})]))
                   (step [_ state input]
                     (if (= :ping (:type input))
                       ;; Emits another self-delivery every time it handles one.
                       (n/result (update state :n inc) [(n/deliver-self {:type :ping})])
                       (n/result state))))
          s (sim/run (sim/make {:seed 1 :nodes {:solo looper}}) 10)]
      ;; One per tick, not unbounded.
      (is (= 10 (:n (sim/node-state s :solo)))))))

;; ============================================================
;; Reproducibility -- the property the whole approach rests on
;; ============================================================

(deftest reproducible-under-faults
  (testing "identical seed and faults produce an identical history"
    (let [run-it #(-> (fresh {:drop-rate 0.3 :duplicate-rate 0.2})
                      (sim/partition-network [#{:a :b :c} #{:d}])
                      (sim/run 25)
                      sim/heal
                      (sim/run 25))
          x (run-it), y (run-it)]
      (is (= (sim/all-committed x) (sim/all-committed y)))
      (is (= (:trace x) (:trace y)))
      (is (= (:tick x) (:tick y))))))

(defspec reproducible-across-seeds 50
  (prop/for-all [seed (gen/choose 1 100000)
                 drop-rate (gen/elements [0.0 0.1 0.3 0.5])]
                (let [run-it #(sim/run
                               (sim/make {:seed seed
                                          :nodes (zipmap peers (repeat (->Decree)))
                                          :config {:drop-rate drop-rate}})
                               40)
                      x (run-it), y (run-it)]
                  (and (= (sim/all-committed x) (sim/all-committed y))
                       (= (:trace x) (:trace y))))))

(defspec different-seeds-explore-different-schedules 30
  ;; Not strictly required for correctness, but if every seed produced the same
  ;; schedule the simulator would only ever explore one history.
  (prop/for-all [a (gen/choose 1 500)]
                (let [run-it (fn [seed]
                               (:trace (sim/run
                                        (sim/make {:seed seed
                                                   :nodes (zipmap peers (repeat (->Decree)))
                                                   :config {:drop-rate 0.4}})
                                        40)))]
                  ;; Over a spread of seeds we should see more than one history.
                  (> (count (distinct (map run-it (range a (+ a 12))))) 1))))

;; ============================================================
;; commit / revert / resync
;; ============================================================

(defrecord Revoker []
  n/Node
  ;; A node that exists to hand the interpreter revocation effects. It has to
  ;; DECLARE them -- feeding a `:revert` through a `Decree`, which never
  ;; revokes, is refused, and that refusal is the capability guard doing its
  ;; job rather than an inconvenience to work around.
  (capabilities [_] {:emits #{:commit :revert :resync}})
  (init [_ config] (n/result {:peer-id (:peer-id config)}))
  (step [_ state _] (n/result state)))

(deftest a-revert-whose-dropped-list-is-wrong-is-refused
  (testing "`node/revert` says an interpreter SHOULD reject a revert whose
            `:dropped` does not match the tail it holds, and now it does --
            including when the claimed list is EMPTY.

            The empty case used to mean `truncate to this vertex, whatever is
            there`, because a restarting node cannot know what the interpreter
            still holds and had no other way to say so. That reading is what
            made the guard skippable: any algorithm could pass `[]` and the
            check would not run. Splitting `resync` out of `revert` removed the
            need for the escape hatch, which is what let this become total."
    (let [sim (-> (sim/make {:seed 1 :nodes {:a (->Revoker)}})
                  (assoc-in [:committed :a] [:v1 :v2 :v3]))
          apply-fx (fn [fx] (#'sim/interpret-effects sim :a [fx]))]
      (is (thrown? Exception (apply-fx (n/revert :v1 [:wrong])))
          "a mismatched tail")
      (is (thrown? Exception (apply-fx (n/revert :v1 [])))
          "and an EMPTY one, which is no longer an escape hatch")
      (is (= [:v1] (get-in (apply-fx (n/revert :v1 [:v2 :v3])) [:committed :a]))
          "the correct tail truncates"))))

(deftest resync-replaces-the-prefix-wholesale
  (testing "a restarting node announces what it now believes, without claiming
            to revoke anything -- and without needing to know what the
            interpreter holds, which it cannot."
    (let [sim (-> (sim/make {:seed 1 :nodes {:a (->Revoker)}})
                  (assoc-in [:committed :a] [:old1 :old2]))
          after (#'sim/interpret-effects sim :a [(n/resync [:new1 :new2 :new3])])]
      (is (= [:new1 :new2 :new3] (get-in after [:committed :a])))
      (is (some #(= :resync (:event %)) (:trace after))
          "and it is traced as a resync, not as a revert -- a consumer can tell
           the difference, which was the whole reason to split them"))))

;; ============================================================
;; The crash model: what a buffered write is worth
;; ============================================================

(defrecord ProbeNode [emits on-init on-step]
  n/Node
  (capabilities [_] {:emits emits :topics #{:t}})
  (init [_ config] (on-init config))
  (step [_ st input] (on-step st input)))

(defrecord Scribe []
  n/Node
  (capabilities [_] {:emits #{:persist-then}})
  (init [_ _] (n/result {:persisted []} []))
  (step [_ state input]
    (case (:type input)
      :write (n/result state [(n/persist-then {:writes (:writes input)
                                               :durable? (:durable? input)
                                               :epoch 1
                                               :token (:token input)})])
      :persisted (n/result (update state :persisted conj (:token input)))
      (n/result state))))

(defn- scribe-sim []
  (sim/make {:seed 3 :nodes {:s (->Scribe)} :config {}}))

(defn- write! [s durable? token writes]
  ;; Run past `persist-latency` so the write actually lands before we crash.
  (-> (sim/inject s :s {:type :write :durable? durable? :token token :writes writes})
      (sim/run 3)))

(defn- survived
  "The writes that outlived the crash. Keyed on the write payload rather than
  the token: `:token` correlates a completion with its issue and is not part of
  the stored record."
  [s]
  (mapv :writes (get-in s [:storage :s :landed])))

(deftest a-buffered-write-after-the-last-fsync-is-lost
  (testing "this is the whole meaning of durable?, and the simulator used to
            ignore it -- every completed write landed and every crash test was
            therefore blind to the distinction it exists to draw"
    (let [s (-> (scribe-sim)
                (write! true :w1 {:a 1})
                (write! false :w2 {:b 2})
                (sim/crash :s))]
      (is (= [{:a 1}] (survived s)) "the buffered tail never reached the platter")
      (is (= {:a 1} (get-in s [:storage :s :durable]))
          ":durable is a fold over the survivors, not over what once landed")
      (is (= 1 (:lost-buffered (last (filter #(= :crash (:event %)) (:trace s)))))))))

(deftest a-buffered-write-before-an-fsync-survives-on-its-coat-tails
  (testing "an fsync flushes everything written before it -- etcd-raft's
            MustSync leaves a commit-index change unsynced for exactly this
            reason, so losing it would be a different bug, not a stricter model"
    (let [s (-> (scribe-sim)
                (write! false :w1 {:a 1})
                (write! true :w2 {:b 2})
                (sim/crash :s))]
      (is (= [{:a 1} {:b 2}] (survived s)))
      (is (= {:a 1 :b 2} (get-in s [:storage :s :durable]))))))

(deftest a-node-that-never-fsynced-keeps-nothing
  (let [s (-> (scribe-sim)
              (write! false :w1 {:a 1})
              (write! false :w2 {:b 2})
              (sim/crash :s))]
    (is (= [] (survived s)))
    (is (= {} (get-in s [:storage :s :durable])))))

(deftest a-restarted-node-sees-only-what-survived
  (testing "the restored views must agree with the crash, or an algorithm
            recovers state it never durably had"
    (let [s (-> (scribe-sim)
                (write! true :w1 {:hard-state {:term 1}})
                (write! false :w2 {:hard-state {:term 9}})
                (sim/crash :s)
                (sim/restart :s))
          restored (get-in s [:nodes :s :state])]
      ;; The node is rebuilt through `init`, so we assert on the storage the
      ;; restart read rather than on the toy node's own state.
      (is (= [{:hard-state {:term 1}}] (survived s)))
      (is (= {:term 1} (get-in s [:storage :s :durable :hard-state]))
          "term 9 was buffered and is gone; recovering it would be the ABA
           hazard the epoch guard exists to catch, handed to us by the harness")
      (is (some? restored)))))

(deftest writes-issued-records-everything-attempted
  (testing ":writes is the issue log and must NOT be narrowed by a crash --
            a test needs to see what was attempted as well as what survived"
    (let [s (-> (scribe-sim)
                (write! false :w1 {:a 1})
                (sim/crash :s))]
      (is (= [] (survived s)))
      (is (= 1 (count (get-in s [:storage :s :writes])))))))

;; ============================================================
;; Bandwidth: the other dimension the oracle could not see
;; ============================================================

(deftest a-bigger-message-costs-more-and-both-platforms-agree
  (testing "structural rather than `(count (pr-str x))`: printing is not
            guaranteed to agree between Clojure and ClojureScript for doubles or
            records, and accounting that differs by platform is worse than none"
    (is (< (sim/estimate-size {:a 1})
           (sim/estimate-size {:a 1 :b 2})
           (sim/estimate-size {:a 1 :b 2 :c "a longer string value"})))
    (is (< (sim/estimate-size {:finalized {}})
           (sim/estimate-size {:finalized (zipmap (range 10) (repeat {:x 1}))})
           (sim/estimate-size {:finalized (zipmap (range 100) (repeat {:x 1}))}))
        "a state-sync answer carrying more history costs more -- which is the
         whole point, since that is the shape the storm had")
    (is (= (sim/estimate-size {:a [1 2 3] :b "x"})
           (sim/estimate-size {:b "x" :a [1 2 3]}))
        "and it is a function of the value, not of map order")))

(deftest estimate-size-is-depth-bounded
  (testing "messages are attacker-supplied in several of these algorithms, so a
            deeply nested one must not hang the simulator"
    (let [deep (reduce (fn [acc _] {:next acc}) {:leaf 1} (range 500))]
      (is (pos? (sim/estimate-size deep))))))

(deftest bandwidth-is-accounted-per-peer-and-per-tick
  (let [s (sim/run (fresh) 30)
        sent (sim/bytes-sent s)
        peak (sim/peak-tick-bytes s)]
    (is (seq sent) "traffic is recorded at all")
    (is (every? pos? (vals sent)))
    (is (every? pos? (vals peak)))
    (is (every? (fn [[p b]] (<= b (get sent p))) peak)
        "a single tick cannot exceed the whole run")))

(deftest a-per-tick-budget-refuses-what-will-not-fit
  (testing "off by default -- existing tests describe schedules, not link
            capacities, and silently dropping their messages would change what
            they mean"
    (let [unlimited (sim/run (fresh) 30)
          squeezed (sim/run (fresh {:bandwidth-per-tick 1}) 30)]
      (is (empty? (sim/bandwidth-drops unlimited))
          "no budget, no drops")
      (is (seq (sim/bandwidth-drops squeezed))
          "a one-byte budget refuses essentially everything")
      (is (every? #(pos? (:bytes %)) (sim/bandwidth-drops squeezed))
          "and records what it refused"))))

(deftest traffic-stays-bounded-as-the-run-grows
  (testing "the guard the storm needed and nobody had.

            A fix can be correct per message and wrong per second: the
            state-sync fix was right about when to ask and turned every lagging
            node into a broadcaster, each answer carrying the responder's whole
            finalized map. Five nodes over kabel went from ten heights finalized
            each to one, and the simulator reported nothing, because the message
            COUNT had barely moved.

            So the assertion is on bytes per tick, and it is deliberately
            generous -- an order of magnitude, not a tight fit. What it catches
            is amplification, which is what a storm is."
    (let [short-run (sim/run (fresh) 40)
          long-run (sim/run (fresh) 200)
          peak-of #(apply max 0 (vals (sim/peak-tick-bytes %)))]
      (is (pos? (peak-of short-run)))
      (is (< (peak-of long-run) (* 10 (peak-of short-run)))
          (str "per-tick traffic must not grow with the length of the run -- "
               "short " (peak-of short-run) ", long " (peak-of long-run))))))

(deftest a-crashed-node-neither-writes-nor-speaks
  (testing "a write in flight at the moment of the crash never lands, and the
            effects gated behind it never go out.

            `crash` truncated the landed tail and left `:pending-persist`
            alone, while `complete-due-persists` iterated every peer without
            asking whether it was alive. So a dead node went on writing to disk
            and went on releasing the `:then` effects gated behind those writes
            -- it broadcast after it was dead.

            That defeats the barrier under crash, which is the one condition it
            exists for: the question is whether a node released its binding
            commitment before the write was durable, and the answer was coming
            from the corpse."
    (let [gated (fn [] [(n/persist-then {:writes {:k 1} :durable? true :epoch 1
                                         :token :t
                                         :then [(n/broadcast :t {:from :a})]})])
          node (->ProbeNode #{:persist-then :broadcast}
                            (fn [_] {:state {:heard []} :effects (gated)})
                            (fn [st input]
                              (n/result (update st :heard conj (:type input)) [])))
          s (sim/make {:seed 1 :nodes {:a node :b node}
                       :config {:persist-latency 5}})
          ;; Crash :a while its durable write is still in flight.
          s (sim/run s 1)
          _ (is (seq (get-in s [:pending-persist :a]))
                "the write must still be in flight, or this proves nothing")
          s (sim/run (sim/crash s :a) 10)]
      (is (empty? (get-in s [:storage :a :landed]))
          "a write that had not landed at the crash must never land")
      (is (= {} (get-in s [:storage :a :durable])))
      (is (not-any? #(= :message-received %) (:heard (sim/node-state s :b)))
          "and nothing gated behind that write may reach a peer"))))
