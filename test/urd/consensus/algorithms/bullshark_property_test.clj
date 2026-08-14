(ns urd.consensus.algorithms.bullshark-property-test
  "Generative tests for the claim the whole algorithm rests on.

  **The total order is a pure function of the certified DAG.** Everything
  Bullshark promises follows from that one sentence, and each property here is
  a different way of trying to falsify it:

  - two nodes that learned the same certificates in different orders must
    produce the same sequence (`ordering-is-arrival-order-independent`);
  - a node that never ran the ordering layer until the end must commit a prefix
    of what a node that ran it every round committed
    (`deferred-ordering-is-a-prefix-of-incremental`);
  - the garbage collector must not change the sequence (`gc-preserves-the-order`);
  - and in a live network with loss, delay, duplication and restarts, no two
    honest nodes may disagree on a position (`agreement-holds`).

  The DAG generator is the interesting part. It does NOT build the trivial
  complete DAG -- every author naming every parent -- because that DAG makes
  almost every property true by symmetry. It draws a random parent subset per
  author per round, subject only to the 2f+1 stake rule, which is exactly the
  freedom a real network has and exactly where a wrong tie-break shows up."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.rng :as rng]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.bullshark :as bs]
            [urd.consensus.algorithms.bullshark-test :as bt]))

;; ============================================================
;; Generating certified DAGs
;; ============================================================

(defn- gen-parents
  "A random subset of round `r-1` carrying at least 2f+1 stake.

  Built by shuffling the authors and taking the shortest prefix that clears the
  threshold, then extending it with a random tail -- so parent sets vary in size
  as well as in membership, which is what makes the anchor sometimes supported
  and sometimes not."
  [st r]
  (gen/let [order (gen/shuffle (vec (keys (get-in st [:dag (dec r)]))))
            extra (gen/choose 0 (count order))]
    (let [need (bs/quorum-threshold (:total-stake st))
          [chosen _] (reduce (fn [[acc w] a]
                               (if (>= w need)
                                 (reduced [acc w])
                                 [(conj acc a) (+ w (get (:stake st) a 0))]))
                             [[] 0]
                             order)
          chosen (into chosen (take extra (remove (set chosen) order)))]
      (into #{} (map #(:id (get-in st [:dag (dec r) %]))) chosen))))

(defn- gen-authors
  "A random author subset carrying at least 2f+1 stake.

  Rounds may be incomplete -- an author can miss a round entirely, which is
  what a slow validator looks like -- but never so incomplete that the next
  round could not legally be built on it. A generator that ignored this
  produced DAGs no honest network can produce, which is not a stronger test but
  a different and meaningless one: the ordering layer's guarantees are
  conditional on the 2f+1 parent rule, so violating it falsifies properties
  that were never claimed."
  [st]
  (gen/let [order (gen/shuffle (:validators st))
            extra (gen/choose 0 (count (:validators st)))]
    (let [need (bs/quorum-threshold (:total-stake st))
          [chosen _] (reduce (fn [[acc w] a]
                               (if (>= w need)
                                 (reduced [acc w])
                                 [(conj acc a) (+ w (get (:stake st) a 0))]))
                             [[] 0]
                             order)]
      (into chosen (take extra (remove (set chosen) order))))))

(defn- gen-round
  "Add round `r`: a quorum-carrying author subset, each with random parents."
  [st r]
  (gen/let [authors (gen-authors st)]
    (reduce (fn [g a]
              (gen/let [s g
                        parents (gen-parents s r)]
                (bt/cert-in s a r parents)))
            (gen/return st)
            (sort authors))))

(defn gen-dag
  "A certified DAG of `rounds` rounds over `validators`."
  [validators stake rounds]
  (reduce (fn [g r] (gen/bind g #(gen-round % r)))
          (gen/return (bt/state {:validators validators :stake stake
                                 :anchor-fn bs/stake-weighted-anchor}))
          (range 1 (inc rounds))))

(def gen-committee
  (gen/elements [[[:a :b :c :d] {:a 1 :b 1 :c 1 :d 1}]
                 [[:a :b :c :d] {:a 5 :b 1 :c 1 :d 1}]
                 [[:a :b :c :d :e :f :g] (zipmap [:a :b :c :d :e :f :g] (repeat 1))]
                 [[:a :b :c :d :e :f :g] {:a 3 :b 3 :c 1 :d 1 :e 1 :f 1 :g 1}]]))

(def gen-scenario
  (gen/let [[validators stake] gen-committee
            rounds (gen/choose 3 14)
            st (gen-dag validators stake rounds)]
    st))

;; ============================================================
;; The pure ordering layer
;; ============================================================

(defn- incremental
  "Order every round as it arrives, which is what a live node does."
  [st]
  (second (reduce (fn [[s acc] r]
                    (let [[s' out] (bs/commit-sequence s r bs/anchor-for)]
                      [s' (into acc out)]))
                  [st []]
                  (sort (keys (:dag st))))))

(defn- deferred
  "Order once, at the highest round -- a node that never ran until the end."
  [st]
  (second (bs/commit-sequence st (apply max (keys (:dag st))) bs/anchor-for)))

(defn- causal?
  "Is every vertex preceded by every parent that is also in the sequence?

  A parent absent from the sequence altogether is fine: it was committed by an
  earlier pass, or garbage collected."
  [out]
  (let [present (into #{} (map :id) out)]
    (loop [seen #{}, [c & more] out]
      (cond
        (nil? c) true
        (every? #(or (contains? seen %) (not (contains? present %)))
                (:parents (:header c)))
        (recur (conj seen (:id c)) more)
        :else false))))

(defspec ordering-is-total-and-duplicate-free 120
  (prop/for-all [st gen-scenario]
                (let [out (incremental st)
                      ids (map :id out)]
                  (and (= (count ids) (count (distinct ids)))
                       (every? pos? (map #(:round (:header %)) out))
                       (causal? out)))))

(defspec deferred-ordering-is-a-prefix-of-incremental 200
  (testing "a node that never ran the ordering layer until the very end commits
            a PREFIX of what a node that ran it every round committed

           Not equality, and the difference is instructive. A single evaluation
           at round R considers only the anchor at R-1; if that anchor lacks
           f+1 support nothing commits at all, even though earlier anchors were
           committable. So the deferred node can be behind. What it must never
           be is DIFFERENT -- and that it cannot be is precisely the 2f+1
           intersection argument: an anchor that gathered f+1 support is reached
           by every later committed anchor, so the back-fill finds it."
    (prop/for-all [st gen-scenario]
                  (let [live (mapv :id (incremental st))
                        late (mapv :id (deferred st))]
                    (= late (vec (take (count late) live)))))))

(defspec gc-preserves-the-order 120
  (testing "a shallow collector commits a prefix of what a deep one commits

           Not equality: garbage collection genuinely bounds how far back an
           unsupported anchor can be reached, so a shallow node may commit
           strictly less. What it must never do is commit something DIFFERENT
           at a position the deep node also filled."
    (prop/for-all [st gen-scenario]
                  (let [deep (mapv :id (incremental (assoc st :gc-depth 1000)))
                        shallow (mapv :id (incremental (assoc st :gc-depth 2)))
                        n (min (count deep) (count shallow))]
                    (= (take n deep) (take n shallow))))))

(defspec anchors-are-committed-in-round-order 120
  (prop/for-all [st gen-scenario]
                (let [anchor-rounds (->> (incremental st)
                                         (filter (fn [c]
                                                   (let [r (:round (:header c))]
                                                     (and (even? r) (pos? r)
                                                          (= (:author (:header c))
                                                             (bs/stake-weighted-anchor
                                                              r (:validators st) (:stake st)))))))
                                         (map #(:round (:header %))))]
                  (= anchor-rounds (sort anchor-rounds)))))

;; ============================================================
;; Arrival order, at the state machine
;; ============================================================

(defn- feed
  "Drive one node with `certs` in the given order; return the committed sequence."
  [validators stake certs]
  (let [{st :state} (n/init (bs/create) {:peer-id (first validators)
                                         :validators validators
                                         :stake stake
                                         :anchor-fn bs/stake-weighted-anchor})]
    (loop [st st, queue (vec certs), out []]
      (if (empty? queue)
        out
        (let [{st' :state fx :effects} (n/step (bs/create) st (n/vertex-received (first queue)))
              committed (mapcat #(:vertices (n/effect-params %))
                                (filter #(= :commit (n/effect-kind %)) fx))]
          (recur st' (subvec queue 1) (into out committed)))))))

(defspec ordering-is-arrival-order-independent 60
  (testing "the same certificates delivered in five different orders

           A node parks a certificate whose parents it lacks and retries it
           when they land, so any permutation is a legal delivery schedule. If
           the DFS tie-break or the sort were unstable this is where it would
           show."
    (prop/for-all [st gen-scenario
                   orders (gen/vector (gen/large-integer* {:min 0 :max 100000}) 5)]
                  (let [certs (vec (mapcat (fn [[_ authors]] (vals authors))
                                           (sort-by key (:dag st))))
                        validators (:validators st)
                        stake (:stake st)
                        runs (map (fn [seed]
                                    (mapv :id (feed validators stake
                                                    (first (rng/shuffle (rng/make seed) certs)))))
                                  orders)]
                    (= 1 (count (distinct runs)))))))

;; ============================================================
;; The live network
;; ============================================================

(def value-fn (fn [_sim peer ctx] {:snapshot [peer (:round ctx)]}))

(defn- run-network [{:keys [seed validators stake drop-rate max-delay duplicate-rate ticks]}]
  (sim/run (sim/make {:seed seed
                      :nodes (into {} (map (fn [v] [v (bs/create)])) validators)
                      :node-config (into {} (map (fn [v] [v {:stake stake}])) validators)
                      :config {:value-fn value-fn
                               :drop-rate drop-rate
                               :max-delay max-delay
                               :duplicate-rate duplicate-rate}})
           ticks))

(defspec agreement-holds 40
  (testing "no two honest nodes disagree on a position, under any schedule"
    (prop/for-all [seed (gen/large-integer* {:min 1 :max 100000})
                   [validators stake] gen-committee
                   drop-rate (gen/elements [0.0 0.1 0.3])
                   max-delay (gen/choose 3 10)
                   duplicate-rate (gen/elements [0.0 0.2])]
                  (let [s (run-network {:seed seed :validators validators :stake stake
                                        :drop-rate drop-rate :max-delay max-delay
                                        :duplicate-rate duplicate-rate :ticks 120})]
                    (and (sim/agreement? s)
             ;; And no certificate was ever rejected as malformed: an honest
             ;; network must not produce anything a peer refuses.
                         (every? (fn [v]
                                   (let [r (:rejected (sim/node-state s v))]
                                     (and (nil? (:malformed r)) (nil? (:thin-parents r)))))
                                 validators))))))

(defspec agreement-survives-crashes 30
  (testing "a node crashes, restarts, re-derives its order from its certificate
            store, and rejoins"
    (prop/for-all [seed (gen/large-integer* {:min 1 :max 100000})
                   victim-idx (gen/choose 0 3)
                   at (gen/choose 10 40)]
                  (let [validators [:a :b :c :d]
                        stake (zipmap validators (repeat 1))
                        victim (nth validators victim-idx)
                        s (run-network {:seed seed :validators validators :stake stake
                                        :drop-rate 0.0 :max-delay 3 :duplicate-rate 0.0
                                        :ticks at})
                        before (sim/committed s victim)
                        after (-> s (sim/crash victim) (sim/run 3) (sim/restart victim) (sim/run 80))]
                    (and (sim/agreement? after)
                         (= before (vec (take (count before) (sim/committed after victim))))
                         (empty? (filter #(= :revert-mismatch (:event %)) (:trace after))))))))

(deftest larger-committees-work
  (testing "seven validators, quorum 5, validity 3"
    (let [validators [:a :b :c :d :e :f :g]
          stake (zipmap validators (repeat 1))
          s (run-network {:seed 1 :validators validators :stake stake
                          :drop-rate 0.0 :max-delay 3 :duplicate-rate 0.0
                          :ticks 120})]
      (is (= 5 (bs/quorum-threshold 7)))
      (is (= 3 (bs/validity-threshold 7)))
      (is (sim/agreement? s))
      (is (> (count (sim/committed s :a)) 20))
      (is (every? #(>= (count (:signers %)) 5)
                  (->> (:certificates (sim/node-state s :a))
                       vals
                       (filter #(pos? (:round (:header %))))))
          "every certificate carries at least 2f+1 signers")
      (is (some #(= 5 (count (:signers %)))
                (->> (:certificates (sim/node-state s :a))
                     vals
                     (filter #(pos? (:round (:header %))))))
          "and typically exactly 2f+1: an author certifies the moment the
           threshold is met and does not wait for stragglers, which is where
           the 2f+1 x 64 bytes of the Ed25519 substitution is actually paid"))))
