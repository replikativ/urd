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

(defn- elected-rounds
  "The rounds of the anchors ELECTED as commit points, in the order elected.

  Read from `::bs/anchors` rather than reconstructed from the committed
  sequence. The previous version of this filtered the output for even-round
  vertices whose author matched `stake-weighted-anchor`, and that is not the
  same set: an anchor that fails the f+1 support test is skipped as a commit
  point, but its certificate is still ordered later as an ordinary member of
  some subsequent anchor's causal history.

  Seed 1786930319378 produced exactly that -- elected rounds 2, 4, 6, 10, 12,
  with the round-8 anchor certificate back-filled inside round 12's sub-DAG.
  The reconstruction read `[2 4 6 10 8 12]` and called it an ordering
  violation. The run was correct; the test could not see the difference between
  a decision and its side effect."
  [st]
  (second (reduce (fn [[s acc] r]
                    (let [[s' out] (bs/commit-sequence s r bs/anchor-for)]
                      [s' (into acc (::bs/anchors (meta out)))]))
                  [st []]
                  (sort (keys (:dag st))))))

(defspec anchors-are-committed-in-round-order 120
  (testing "commit points advance monotonically.

           This is what stops the total order from being rewritten: once an
           anchor at round R is a commit point, no anchor at or below R may
           become one afterwards, because everything up to R has already been
           handed to the application. Strictly increasing, not merely sorted --
           electing the same round twice would re-order its sub-DAG."
    (prop/for-all [st gen-scenario]
                  (let [rs (elected-rounds st)]
                    (and (apply <= 0 rs)
                         (= rs (distinct rs))
                         (every? even? rs))))))

;; ============================================================
;; Arrival order, at the state machine
;; ============================================================

(defn- feed
  "Drive one node with `certs` in the given order; return the committed sequence."
  [validators stake certs]
  (let [peer (first validators)
        s (sim/make {:nodes {peer (bs/create)}
                     :node-config {peer (merge (bs/test-attestations)
                                               {:validators validators :stake stake})}})
        fed (reduce #(sim/inject %1 peer (n/vertex-received %2)) s certs)]
    (sim/committed (sim/advance fed) peer)))

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

(deftest arrival-order-driver-delivers-a-known-commit
  (let [st (bt/dag-through 3 {:anchor-fn bs/stake-weighted-anchor})
        certs (mapcat vals (vals (into (sorted-map) (:dag st))))
        expected (mapv bs/vertex (incremental st))]
    (is (seq expected))
    (is (= expected (feed (:validators st) (:stake st) (reverse certs))))))

(deftest delayed-ancestor-crossing-a-commit-watermark
  (let [vs bt/vs
        author (bs/stake-weighted-anchor 2 vs bt/uniform)
        other (first (remove #{author} vs))
        ;; The round-2 anchor and its supporting round-3 certificates need
        ;; neither the author's round-1 block nor the other validator's round-2 block.
        ;; A fourth branch carries both forward into the round-4 anchor.
        headers (reduce (fn [st [r a]]
                          (let [parents (cond
                                          (and (= r 2) (not= a other)) (remove #{author} vs)
                                          (and (= r 3) (not= a other)) (remove #{other} vs)
                                          :else vs)]
                            (bt/cert-in st a r (bt/ids-at st (dec r) parents))))
                        (bt/state {})
                        (for [r (range 1 6) a vs] [r a]))
        certs (for [r (range 1 6) a vs] (get-in headers [:dag r a]))
        early (for [r (range 1 4) a vs
                    :when (not= a (if (= r 1) author other))]
                (get-in headers [:dag r a]))
        delayed (get-in headers [:dag 1 author])
        on-time (feed vs bt/uniform certs)
        late (feed vs bt/uniform (concat early (remove (set early) certs)))]
    (is (seq (feed vs bt/uniform early)))
    (is (= on-time late))
    (is (not-any? #(= (:id delayed) (:id %)) late))
    (is (some #(= 4 (:round %)) late))))

;; ============================================================
;; The live network
;; ============================================================

(def value-fn (fn [_sim peer ctx] {:snapshot [peer (:round ctx)]}))

(defn- run-network [{:keys [seed validators stake drop-rate max-delay duplicate-rate ticks]}]
  (sim/run (sim/make {:seed seed
                      :nodes (into {} (map (fn [v] [v (bs/create)])) validators)
                      :node-config (into {} (map (fn [v] [v (merge (bs/test-attestations)
                                                                   {:stake stake})]))
                                         validators)
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

;; ============================================================
;; Re-entry: the same round, twice
;; ============================================================

(deftest an-anchor-is-elected-at-most-once
  (testing "the `<= last-committed-round` guard, which nothing was exercising.

           `commit-sequence` is driven by the round of each ARRIVING
           certificate, and certificates arrive out of order and more than once
           -- a duplicate delivery, a catch-up that re-sends what we already
           have, two certificates of the same round each triggering a call. So
           the same `inserted-round` really does come round twice.

           `incremental`, which every ordering property here is built on, walks
           `(sort (keys (:dag st)))` -- each round once, ascending. Under that
           driver `r` is never at or below the high-water mark, so relaxing the
           guard from `<=` to `<` changes no result and every property still
           passes. Verified: that mutation survives all 300 generated cases of
           `anchors-are-committed-in-round-order`.

           Re-electing an anchor re-emits nothing, because the per-author
           watermarks stop the DFS -- so the damage is not duplicate output. It
           is that a commit point already handed to the application is elected
           again, and the second election's `order-anchors` walk starts from a
           round the first one already passed."
    (let [st (first (gen/sample gen-scenario 40))
          rounds (sort (keys (:dag st)))
          ;; Drive it once, normally.
          [st' elected]
          (reduce (fn [[s acc] r]
                    (let [[s2 out] (bs/commit-sequence s r bs/anchor-for)]
                      [s2 (into acc (::bs/anchors (meta out)))]))
                  [st []] rounds)]
      (is (seq elected) "the scenario has to commit something to prove anything")
      ;; Now replay every round again against the settled state.
      (let [[_ again]
            (reduce (fn [[s acc] r]
                      (let [[s2 out] (bs/commit-sequence s r bs/anchor-for)]
                        [s2 (into acc (::bs/anchors (meta out)))]))
                    [st' []] rounds)]
        (is (empty? again)
            (str "a second pass over the same rounds elects nothing new; got "
                 (vec again)))))))
