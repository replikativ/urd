(ns urd.consensus.algorithms.bullshark-test
  "Narwhal/Bullshark: the certified DAG and the zero-message ordering layer.

  The central claim under test is narrow and strong: **the total order is a
  pure function of the DAG**. Everything else -- multi-vertex commits,
  arrival-order independence, crash recovery, GC -- is a corollary of it, and
  each is tested as such rather than assumed.

  Two of these tests exist because the port was wrong in exactly the way they
  check, and the wrongness was invisible from the outside:

  - `certificates-arriving-out-of-order-are-parked-not-rejected`: validating
    parent structure and parent PRESENCE together turned every out-of-order
    arrival into a permanent rejection. The network still converged, because
    gossip redelivers until an order happens to work.
  - `a-lagging-node-catches-up`: catch-up was served from the consensus DAG,
    which the GC empties by design, so a node that fell behind could never
    return. It reads as a partition that did not heal."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.node :as n]
            [urd.consensus.pending :as pending]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.bullshark :as bs]))

;; ============================================================
;; A DAG under construction, without a network
;;
;; These build `ConsensusState` values directly. The ordering layer takes no
;; effects and produces none, so it can be exercised as a plain function --
;; which is itself the first thing worth demonstrating.
;; ============================================================

(def vs [:a :b :c :d])

(def atts
  "Vote attestations for tests. `init` now REFUSES to start without a signing
  and verifying function, because a certificate is a third party's aggregated
  claim relayed by non-signers, and a permissive default is exactly how the
  forgery hole survived a previous audit round."
  (bs/test-attestations))

(defn cert*
  "Build a certificate whose attestations actually verify.

  Tests used to name signers as a bare set, which is all a certificate could
  carry and all a peer could check. Naming them is no longer enough."
  [header signers]
  (bs/certificate header
                  (into {} (map (fn [s] [s ((:sign-vote atts) s (bs/header-id header))]))
                        signers)))
(def uniform (into {} (map (fn [v] [v 1])) vs))

(defn state
  ([] (state {}))
  ([{:keys [stake gc-depth anchor-fn validators]
     :or {stake uniform gc-depth 50 anchor-fn bs/round-robin-anchor}}]
   (let [validators (or validators vs)
         genesis (bs/genesis-certificates validators)]
     {:dag {0 genesis}
      :last-committed (into {} (map (fn [v] [v 0])) validators)
      :last-committed-round 0
      :certificates (into {} (map (fn [[_ c]] [(:id c) c])) genesis)
      :slots (into {} (map (fn [[a c]] [[a 0] (:id c)])) genesis)
      :gc-depth gc-depth
      :stake stake
      :total-stake (reduce + 0 (vals stake))
      :validators validators
      :anchor-fn anchor-fn})))

(defn cert-in
  "Put a certificate from `a` at round `r` naming `parents` into the state."
  [st a r parents]
  (let [c (cert* {:author a :round r :payload [a r] :parents (set parents)}
                 (set (:validators st)))]
    (-> st
        (assoc-in [:dag r a] c)
        (assoc-in [:certificates (:id c)] c)
        (assoc-in [:slots [a r]] (:id c)))))

(defn ids-at [st r authors]
  (into #{} (map #(:id (get-in st [:dag r %]))) authors))

(defn round-in
  "Add a full round `r`, every author naming every certificate of `r-1`."
  ([st r] (round-in st r (:validators st)))
  ([st r authors]
   (let [parents (ids-at st (dec r) (:validators st))]
     (reduce (fn [s a] (cert-in s a r parents)) st authors))))

(defn dag-through [n & [opts]]
  (reduce round-in (state (or opts {})) (range 1 (inc n))))

(defn drive
  "Feed every round into the ordering layer in ascending order, as a live node
  would. Returns [state sequence]."
  [st]
  (reduce (fn [[s acc] r]
            (let [[s' out] (bs/commit-sequence s r bs/anchor-for)]
              [s' (into acc out)]))
          [st []]
          (sort (keys (:dag st)))))

(defn shape [certs]
  (mapv (juxt #(:round (:header %)) #(:author (:header %))) certs))

;; ============================================================
;; Thresholds
;; ============================================================

(deftest thresholds-are-over-stake-not-headcount
  (testing "config/src/lib.rs:548-561, integer division"
    (is (= [3 4 5 5 7] (mapv bs/quorum-threshold [4 5 7 6 10])))
    (is (= [2 2 3 2 4] (mapv bs/validity-threshold [4 5 7 6 10]))))
  (testing "validity-threshold is f+1 exactly, for every committee size"
    (is (every? (fn [total]
                  (= (bs/validity-threshold total)
                     (inc (n/byzantine-tolerance total))))
                (range 1 40))))
  (testing "quorum-threshold agrees with the core's byzantine-threshold under
            uniform stake, and diverges from it under weighted stake -- which
            is why this algorithm carries its own"
    (is (every? #(= (bs/quorum-threshold %) (n/byzantine-threshold %)) (range 1 40)))
    ;; Four validators, ten stake each. The core's threshold function would be
    ;; handed the head count.
    (is (= 27 (bs/quorum-threshold 40)))
    (is (= 3 (n/byzantine-threshold 4)))))

;; ============================================================
;; Identity
;; ============================================================

(deftest certificate-identity-excludes-the-signer-set
  (testing "two nodes aggregating different quorums must name one vertex

           If the signer set were part of the digest they would be different
           vertices, the DAG would fork along an honest path, and parent
           lookups would miss."
    (let [h {:author :a :round 3 :payload {:x 1} :parents #{"p1" "p2"}}]
      (is (= (:id (cert* h #{:a :b :c}))
             (:id (cert* h #{:b :c :d})))))))

(deftest certificate-identity-covers-the-header
  (let [h {:author :a :round 3 :payload {:x 1} :parents #{"p1"}}]
    (is (not= (:id (cert* h #{:a}))
              (:id (cert* (assoc h :payload {:x 2}) #{:a}))))
    (is (not= (:id (cert* h #{:a}))
              (:id (cert* (assoc h :parents #{"p2"}) #{:a}))))
    (is (not= (:id (cert* h #{:a}))
              (:id (cert* (assoc h :round 4) #{:a}))))))

(deftest digests-are-strings
  (testing "not UUIDs -- see the namespace note on cross-platform comparison"
    (is (string? (bs/header-id {:author :a :round 1 :payload nil :parents #{}})))
    (is (every? string? (map :id (vals (bs/genesis-certificates vs)))))))

;; ============================================================
;; Anchor selection
;; ============================================================

(deftest anchors-are-a-pure-function-of-the-round
  (is (= (mapv #(bs/stake-weighted-anchor % vs uniform) (range 10))
         (mapv #(bs/stake-weighted-anchor % vs uniform) (range 10)))))

(deftest anchors-do-not-cycle-and-do-not-exclude-anyone
  (testing "the bias that frequency counts cannot see

           `stake-weighted-anchor` drew from `(rng/make round)` -- the round
           number straight in as generator state. xorshift32 is GF(2)-linear
           and one round of it does not decorrelate consecutive seeds, so the
           anchors for rounds 2..15 at n=4 came out `:c :d :a :b` repeating:
           exactly `round mod n`, the rule this function replaces.

           ANCHORS ONLY EXIST AT EVEN ROUNDS, so sampling that cycle every
           second round takes half of it. For rounds 4..14 only `:a` and `:c`
           could ever anchor -- two of four validators unreachable across six
           consecutive waves, and commits stalling if either was slow while the
           DAG was perfectly healthy.

           `anchor-selection-is-stake-weighted` above passed throughout,
           because over a thousand rounds the totals ARE uniform. The bias is
           in the order, not the counts, so the test has to look at the order."
    (let [anchors-at (fn [rounds] (mapv #(bs/stake-weighted-anchor % vs uniform) rounds))
          evens (anchors-at (range 0 40 2))]
      (is (= 4 (count (set (anchors-at (range 4 16)))))
          "every validator is reachable across six waves")
      (is (not= (anchors-at (range 2 6)) (anchors-at (range 6 10)))
          "and consecutive rounds do not repeat a fixed cycle")
      (is (< 2 (count (set (take 10 evens))))
          "the even rounds -- the only ones that select anything -- are not
           drawn from a two-element subset")
      (is (not= (mapv #(nth vs (mod % 4)) (range 2 16))
                (anchors-at (range 2 16)))
          "and the draw is not `round mod n` wearing a PRNG"))))

(deftest anchor-selection-is-stake-weighted
  (testing "a validator with three times the stake anchors roughly three times
            as often -- `round mod n` cannot express this at all"
    (let [weighted {:a 6 :b 2 :c 1 :d 1}
          picks (frequencies (map #(bs/stake-weighted-anchor % vs weighted)
                                  (range 1000)))]
      (is (> (:a picks) 400) (str picks))
      (is (< (:c picks 0) 200) (str picks))
      (is (> (:a picks) (* 2 (:b picks)))))))

(deftest round-robin-anchor-matches-narwhals-own-rule
  (is (= [:a :b :c :d :a] (mapv #(bs/round-robin-anchor % vs uniform) (range 5)))))

;; ============================================================
;; The ordering layer
;; ============================================================

(deftest anchors-exist-only-at-even-rounds
  (testing "bullshark.rs:49-52 -- a certificate at an even round considers an
            odd anchor round and must decline"
    (let [st (dag-through 6)]
      (is (empty? (second (bs/commit-sequence st 4 bs/anchor-for)))
          "inserted round 4 => candidate anchor round 3, which is odd")
      (is (empty? (second (bs/commit-sequence st 6 bs/anchor-for))))
      (is (seq (second (bs/commit-sequence st 3 bs/anchor-for)))
          "inserted round 3 => candidate anchor round 2"))))

(deftest genesis-is-never-committed
  (testing "`last-committed` seeded at 0 for every validator is what stops the
            DFS; without it the first commit carries n phantom vertices and
            every node agrees on them, so nothing catches it"
    (let [[_ out] (drive (dag-through 5))]
      (is (every? pos? (map #(:round (:header %)) out)))
      (is (= (count out) (count (distinct (map :id out))))))))

(deftest the-commit-rule-needs-f-plus-1-support
  (testing "one supporter out of four is not enough; two is"
    (let [base (-> (state) (round-in 1) (round-in 2))
          anchor (bs/anchor-for base 2)
          ;; :a is the only round-3 certificate naming the anchor.
          weak (-> base
                   (cert-in :a 3 (ids-at base 2 [:a :b :c]))
                   (cert-in :b 3 (ids-at base 2 [:a :b :d]))
                   (cert-in :c 3 (ids-at base 2 [:a :b :d]))
                   (cert-in :d 3 (ids-at base 2 [:a :b :d])))
          strong (cert-in weak :b 3 (ids-at base 2 [:a :b :c]))]
      (is (= :c (:author (:header anchor))))
      (is (= 2 (bs/validity-threshold 4)))
      (is (empty? (second (bs/commit-sequence weak 3 bs/anchor-for))))
      (is (seq (second (bs/commit-sequence strong 3 bs/anchor-for)))))))

(deftest an-unsupported-anchor-is-back-filled-retroactively
  (testing "utils::order_leaders -- the round-2 anchor never gathered f+1
            support, and is committed later, on the strength of the round-4
            anchor that reaches it"
    (let [base (-> (state) (round-in 1) (round-in 2))
          ;; Only :a names the round-2 anchor, so support is 1 < f+1.
          st (-> base
                 (cert-in :a 3 (ids-at base 2 [:a :b :c]))
                 (cert-in :b 3 (ids-at base 2 [:a :b :d]))
                 (cert-in :c 3 (ids-at base 2 [:a :b :d]))
                 (cert-in :d 3 (ids-at base 2 [:a :b :d]))
                 (round-in 4)
                 (round-in 5))
          [_ out] (drive st)]
      (is (= 13 (count out)))
      (is (= [[1 :b] [1 :d] [1 :c] [1 :a]
              [2 :c] [2 :b] [2 :a] [2 :d]
              [3 :b] [3 :d] [3 :c] [3 :a]
              [4 :a]]
             (shape out))
          "rounds 1-2 come from the back-filled anchor, 3-4 from the new one")
      (is (some #(and (= 2 (:round (:header %))) (= :c (:author (:header %)))) out)
          "the round-2 anchor itself is in the sequence"))))

(deftest one-certificate-can-commit-a-long-multi-anchor-sequence
  (testing "the case `:commit` was designed for and nothing had used

           A node holding a 21-round DAG that has never run the ordering layer
           commits 77 vertices and 10 anchors in ONE call, and the sequence is
           identical to the one a node that ordered every round as it arrived
           produced. That equality is the whole claim: the total order does not
           depend on when you evaluate it."
    (let [st (dag-through 21)
          [_ incremental] (drive st)
          [_ one-shot] (bs/commit-sequence st 21 bs/anchor-for)]
      (is (= 77 (count one-shot)))
      (is (= (mapv :id incremental) (mapv :id one-shot)))
      (is (= 10 (count (filter (fn [c]
                                 (let [r (:round (:header c))]
                                   (and (even? r)
                                        (= (:author (:header c))
                                           (bs/round-robin-anchor r vs uniform)))))
                               one-shot)))))))

(deftest ordering-is-independent-of-arrival-order
  (testing "the same certificates inserted in twenty different orders

           What this pins is that map ITERATION order cannot leak into the
           output through `linked?` or `cert-at`: all twenty builds hold the
           identical certificate values and differ only in the order they were
           `assoc`ed in.

           It does NOT distinguish a stable sort from an unstable one, which is
           what it used to claim. The DFS visits parents through
           `(sort (cert-parents x))`, so its sequence is already identical in
           all twenty runs and any deterministic sort gives the same twenty
           outputs. Arrival-order independence across a real network -- where
           the `:pending` parking path is exercised -- is covered by
           `ordering-is-arrival-order-independent` in the property suite."
    (let [build (fn [order]
                  (reduce (fn [st r]
                            (let [parents (ids-at st (dec r) vs)]
                              (reduce (fn [s a] (cert-in s a r parents)) st order)))
                          (state)
                          (range 1 8)))
          outs (mapv #(mapv :id (second (drive (build %))))
                     (repeatedly 20 #(shuffle vs)))]
      (is (= 1 (count (distinct outs))))
      (is (< 20 (count (first outs)))))))

(deftest within-a-round-the-order-is-the-dfs-order-not-the-author-order
  (testing "if it were author order the stable sort would be doing nothing and
            the test above would be vacuous"
    (let [[_ out] (drive (dag-through 5))
          by-round (group-by first (shape out))]
      (is (some (fn [[_ pairs]] (not= (map second pairs) (sort (map second pairs))))
                by-round)))))

(deftest gc-does-not-change-the-order-of-what-remains
  (testing "gc-depth 1, 3 and 50 produce the identical sequence under steady
            progress; GC only bounds how far back a stalled anchor can be
            back-filled from"
    (let [seqs (mapv #(mapv :id (second (drive (dag-through 21 {:gc-depth %}))))
                     [1 3 50])]
      (is (= 1 (count (distinct seqs))))
      (is (= 77 (count (first seqs)))))))

(deftest gc-actually-prunes
  (testing "otherwise the test above is green for the wrong reason

           Note which mechanism does the work: after committing through round
           20 the DAG is down to three rounds at gc-depth 50 as well as at
           gc-depth 1, because the per-author pass -- drop everything strictly
           below that author's own last committed round -- dominates the depth
           cutoff entirely under steady progress. The depth only bites on an
           author that has fallen behind."
    (let [[deep _] (drive (dag-through 21 {:gc-depth 50}))]
      (is (= 20 (:last-committed-round deep)))
      (is (< (count (keys (:dag deep))) 5)
          "22 rounds went in; almost nothing is retained")
      (is (empty? (get-in deep [:dag 1])))
      (is (every? (fn [[r authors]]
                    (every? (fn [[a _]] (>= r (get-in deep [:last-committed a]))) authors))
                  (:dag deep))))))

(deftest an-anchor-with-no-certificate-is-skipped
  (testing "an anchor that never produced a certificate cannot be committed and
            must not block the ones after it"
    (let [;; :c is the round-2 anchor under round-robin; leave it out of round 2.
          st (-> (state) (round-in 1) (round-in 2 [:a :b :d]) (round-in 3)
                 (round-in 4) (round-in 5))
          [_ out] (drive st)]
      (is (nil? (bs/anchor-for st 2)))
      (is (seq out))
      (is (not-any? #(and (= 2 (:round (:header %))) (= :c (:author (:header %)))) out)))))

;; ============================================================
;; DAG construction
;; ============================================================

(defn node-init [cfg]
  (:state (n/init (bs/create) (merge {:peer-id :a :validators vs} atts cfg))))

(defn insert [st c]
  (n/step (bs/create) st (n/vertex-received c)))

(deftest a-certificate-without-a-quorum-of-signers-is-rejected
  (testing "the signer-bitmap substitution for the BLS aggregate: the state
            machine checks that the SET of signers is decisive"
    (let [st (node-init {})
          parents (into #{} (map :id) (vals (get-in st [:dag 0])))
          thin (cert* {:author :b :round 1 :payload nil :parents parents}
                      #{:b :c})
          {st' :state} (insert st thin)]
      (is (= 1 (get-in st' [:rejected :malformed])))
      (is (nil? (get-in st' [:dag 1 :b]))))))

(deftest a-certificate-with-a-forged-digest-is-rejected
  (let [st (node-init {})
        parents (into #{} (map :id) (vals (get-in st [:dag 0])))
        c (assoc (cert* {:author :b :round 1 :payload nil :parents parents}
                        (set vs))
                 :id "not-the-real-digest")
        {st' :state} (insert st c)]
    (is (= 1 (get-in st' [:rejected :malformed])))))

(deftest a-certificate-with-too-few-parents-is-rejected
  (testing "primary/src/core.rs:229-245 -- a round r+1 header needs 2f+1 STAKE
            of distinct authors at round r, and Narwhal keeps this check out of
            `Header::verify` entirely"
    (let [st (node-init {})
          two (into #{} (comp (map :id) (take 2)) (sort-by :id (vals (get-in st [:dag 0]))))
          c (cert* {:author :b :round 1 :payload nil :parents two} (set vs))
          {st' :state} (insert st c)]
      (is (= 1 (get-in st' [:rejected :thin-parents])))
      (is (nil? (get-in st' [:dag 1 :b]))))))

(deftest a-parent-at-the-wrong-round-is-rejected-not-ignored
  (testing "`core.rs:225-229` `ensure!`s `x.round() + 1 == header.round` and
            errors out. Ours used `keep` with a round test, so a parent at the
            wrong round was silently left OUT OF THE TALLY -- and a certificate
            whose remaining parents happened to clear 2f+1 was admitted anyway,
            carrying an edge the ordering layer can never traverse
            (`order-sub-dag` and `linked?` only ever look at `(dec round)`).

            Here every genesis parent is present and decisive, plus one extra
            parent at round 1. The certificate at round 2 must be rejected, not
            quietly admitted with three good edges and one dangling one."
    (let [st (node-init {})
          gen-ids (into #{} (map :id) (vals (get-in st [:dag 0])))
          r1 (cert* {:author :a :round 1 :payload nil :parents gen-ids} (set vs))
          {st1 :state} (insert st r1)
          ;; A round-1 parent named by a round-2 certificate whose other parents
          ;; are all at round 0. The round-0 set alone clears 2f+1.
          mixed (conj gen-ids (:id r1))
          bad (cert* {:author :b :round 1 :payload nil :parents mixed} (set vs))
          {st2 :state} (insert st1 bad)]
      (is (some? (get-in st2 [:certificates (:id r1)])) "the good one landed")
      (is (= 1 (get-in st2 [:rejected :thin-parents]))
          "a mixed-round parent set is rejected outright")
      (is (nil? (get-in st2 [:dag 1 :b]))))))

(deftest certificates-arriving-out-of-order-are-parked-not-rejected
  (testing "a round-2 certificate that arrives before round 1

           The first version of this port ran the parent-structure check and
           the parent-presence check together, so a perfectly good certificate
           whose history had not arrived yet was rejected outright. The network
           still converged -- gossip redelivers until some order works -- so the
           only visible symptom was a rejection counter nobody was reading."
    (let [full (dag-through 2)
          r1 (vals (get-in full [:dag 1]))
          r2 (vals (get-in full [:dag 2]))
          st (node-init {})
          st (reduce (fn [s c] (:state (insert s c))) st r2)]
      (is (= 4 (count (:pending st))))
      (is (empty? (:rejected st)))
      (let [st (reduce (fn [s c] (:state (insert s c))) st r1)]
        (is (empty? (:pending st)) "parked certificates go in once parents land")
        (is (= 4 (count (get-in st [:dag 2]))))))))

(deftest two-certificates-for-one-slot-are-reported-not-absorbed
  (testing "Narwhal's dag is a HashMap keyed by (round, author), so the second
            silently OVERWRITES the first. It cannot happen with honest
            signers; `cannot happen` and `is not checked` are different claims."
    (let [st (node-init {})
          parents (into #{} (map :id) (vals (get-in st [:dag 0])))
          c1 (cert* {:author :b :round 1 :payload {:v 1} :parents parents}
                    (set vs))
          c2 (cert* {:author :b :round 1 :payload {:v 2} :parents parents}
                    (set vs))
          {st :state} (insert st c1)
          {st :state fx :effects} (insert st c2)]
      (is (= 1 (get-in st [:rejected :equivocation])))
      (is (= [:report-equivocation] (mapv n/effect-kind fx)))
      (is (= :b (:peer (n/effect-params (first fx)))))
      (is (= (:id c1) (get-in st [:dag 1 :b :id])) "the first one stands"))))

;; ============================================================
;; The node, in the simulator
;; ============================================================

(def value-fn (fn [_sim peer ctx] {:snapshot [peer (:round ctx)]}))

(defn make-sim [{:keys [seed peers node cfg] :or {seed 1 peers vs}}]
  (sim/make {:seed seed
             :nodes (into {} (map (fn [v] [v (or node (bs/create))])) peers)
             :node-config (into {} (map (fn [v] [v atts])) peers)
             :config (merge {:value-fn value-fn} cfg)}))

(deftest honest-nodes-produce-the-identical-total-order
  (testing "the central claim

           Nodes may be at different LENGTHS -- one node is a round behind
           another whenever a certificate is still in flight -- so the property
           is prefix equality, not equality. Asserting equality outright passes
           only by luck of the schedule."
    (let [s (sim/run (make-sim {:seed 1}) 80)
          seqs (mapv #(sim/committed s %) vs)]
      (is (sim/agreement? s))
      (is (every? #(> (count %) 15) seqs))
      (let [n (apply min (map count seqs))]
        (is (= 1 (count (distinct (map #(take n %) seqs))))
            "every node's first n vertices are the same n vertices, in order")))))

(deftest committed-vertices-carry-the-application-payload
  (let [s (sim/run (make-sim {:seed 1}) 60)
        committed (sim/committed s :a)]
    (is (every? #(contains? (:payload %) :snapshot) committed))
    (is (every? #(= (:snapshot (:payload %)) [(:author %) (:round %)]) committed)
        "the payload the application supplied for (peer, round) is what lands")))

(defn all-effects
  "Every effect a step produced, INCLUDING those gated behind a `persist-then`'s
  `:then`.

  Bullshark's commits ride there -- see
  `a-commit-never-rides-ahead-of-the-write-it-rests-on` -- so a probe that reads
  only the top level sees no commit at all and concludes the algorithm never
  decides anything. That is a property of where the probe looks, not of the
  algorithm."
  [fx]
  (into (vec fx)
        (mapcat (fn [e]
                  (when (= :persist-then (n/effect-kind e))
                    (:then (n/effect-params e)))))
        fx))

(deftest a-commit-arrives-with-no-message-of-its-own
  (testing "the ordering layer sends nothing

           `step` may return a `:commit` and no outbound effect at all. A
           runtime that assumed a decision is preceded by a vote round would not
           fit this algorithm; the simulator handles it without noticing, which
           is the result being reported."
    (let [log (atom [])
          probe (reify n/Node
                  (capabilities [_] (n/capabilities (bs/create)))
                  (init [_ cfg] (n/init (bs/create) cfg))
                  (step [_ st in]
                    (let [{s :state fx :effects} (n/step (bs/create) st in)
                          all (all-effects fx)]
                      (doseq [e all :when (= :commit (n/effect-kind e))]
                        (swap! log conj {:n (count (:vertices (n/effect-params e)))
                                         :outbound (count (filter n/outbound? all))}))
                      {:state s :effects fx})))
          s (sim/run (make-sim {:seed 3 :node probe}) 80)]
      (is (sim/agreement? s))
      (is (seq @log))
      (is (pos? (count (filter (comp zero? :outbound) @log)))
          "at least one commit with zero outbound effects")
      (is (> (count (filter (comp zero? :outbound) @log))
             (* 0.5 (count @log)))
          "and it is the common case, not a curiosity")
      (is (some #(> (:n %) 1) @log) "multi-vertex commits happen in a live run"))))

(deftest commits-concatenate-to-the-committed-sequence
  (testing "a consumer that appends each commit's vertices in the order they
            arrive must end up with exactly what the interpreter holds.

           This used to fold the commits back together using `:index`, checking
           that the indices tiled the sequence with no gap or overlap. `:index`
           is gone -- it was read by the interpreter never, and its only other
           reader was a Nakamoto test asserting it was non-monotone -- so the
           claim is now stated directly: position is implicit in the order the
           commits are emitted, and concatenation is the whole contract.

           Weaker than the old form in one respect and stronger in another. It
           can no longer catch a commit that names a wrong position, because
           there are no positions to name; it does catch a commit that emits the
           wrong vertices or emits them out of order, which is the failure a
           consumer would actually suffer."
    (let [log (atom {})
          probe (reify n/Node
                  (capabilities [_] (n/capabilities (bs/create)))
                  (init [_ cfg] (n/init (bs/create) cfg))
                  (step [_ st in]
                    (let [{s :state fx :effects} (n/step (bs/create) st in)]
                      (doseq [e (all-effects fx) :when (= :commit (n/effect-kind e))]
                        (swap! log update (:peer-id s) (fnil conj []) (n/effect-params e)))
                      {:state s :effects fx})))
          s (sim/run (make-sim {:seed 7 :node probe}) 60)]
      (is (sim/agreement? s))
      (is (= (set vs) (set (keys @log))))
      (doseq [peer vs]
        (let [rebuilt (into [] (mapcat :vertices) (get @log peer))]
          (is (seq rebuilt) (str peer ": committed nothing, so this proves nothing"))
          (is (= rebuilt (sim/committed s peer))
              (str peer ": the concatenated commits are the committed sequence")))))))

(deftest progress-survives-message-loss
  (testing "30% and 50% drop -- Tendermint recorded zero progress at 30%
            without a gossip timer inside the state machine"
    (doseq [[seed drop] [[7 0.3] [11 0.5]]]
      (let [s (sim/run (make-sim {:seed seed :cfg {:drop-rate drop}}) 150)]
        (is (sim/agreement? s) (str "drop " drop))
        (is (> (count (sim/committed s :a)) 5) (str "drop " drop))))))

(deftest a-minority-partition-cannot-commit-and-agreement-survives-healing
  (let [s (-> (make-sim {:seed 17})
              (sim/run 30)
              (sim/partition-network [#{:a :b} #{:c :d}]))
        halted (sim/run s 40)
        healed (sim/run (sim/heal halted) 80)]
    (is (sim/agreement? halted))
    (is (= (count (sim/committed halted :a)) (count (sim/committed s :a)))
        "neither half of a 2/2 split reaches 2f+1, so nothing commits")
    (is (sim/agreement? healed))
    (is (> (count (sim/committed healed :a)) (count (sim/committed halted :a))))))

(deftest a-lagging-node-catches-up
  (testing "catch-up must be served from the certificate STORE, not the DAG

           `record-committed` prunes each author's certificates below its own
           last committed round, so a healthy node's DAG holds almost nothing
           old. Serving `:want` from it means a node that fell behind asks for
           round 10 and every peer that could answer has already dropped it.
           This test failed exactly that way, and read as a partition that did
           not heal: three nodes agreed perfectly and the fourth sat at round 3
           forever."
    (let [s (-> (make-sim {:seed 17})
                (sim/run 20)
                (sim/partition-network [#{:a :b :c} #{:d}])
                (sim/run 100))
          behind (count (sim/committed s :d))
          healed (sim/run (sim/heal s) 200)]
      (is (< behind 10))
      (is (sim/agreement? healed))
      (is (empty? (:pending (sim/node-state healed :d))))
      (is (> (count (sim/committed healed :d)) 100)
          "the isolated node re-joins and orders the whole history it missed")
      (is (= (:round (sim/node-state healed :d)) (:round (sim/node-state healed :a)))))))

(deftest a-rejoining-node-resumes-PROPOSING-not-just-following
  (testing "ordering the history you missed is not the same as coming back

           `advance-round` stepped one round at a time and required a quorum AT
           the current round. After catching up, the current round is far below
           the frontier -- and the node's own `record-committed` GC has by then
           pruned everything below `last-committed-round`, so the round it sits
           on is empty and can NEVER acquire a quorum. It is stuck in a hole it
           dug itself.

           The node still looked fine: it ordered every certificate, committed
           the whole history, and agreed with its peers at every position. It
           simply never proposed another header, contributing nothing to the
           DAG from then on. `agreement?` cannot see this, because it is a
           liveness failure of one node and not a safety failure of any.

           Checked across several seeds. The single-seed assertion above passed
           throughout the broken period for a reason unrelated to what it
           claims to test: the biased anchor schedule happened to keep the
           rejoining node's round moving, and fixing that bias is what exposed
           this."
    (doseq [seed [3 5 11 17 23]]
      (let [s (-> (make-sim {:seed seed})
                  (sim/run 20)
                  (sim/partition-network [#{:a :b :c} #{:d}])
                  (sim/run 100))
            healed (sim/run (sim/heal s) 200)
            d (:round (sim/node-state healed :d))
            a (:round (sim/node-state healed :a))]
        (is (> d 20)
            (str "seed " seed ": :d was at round " d " while :a was at " a
                 " -- it came back as a permanent passive follower"))
        (is (<= (Math/abs (- d a)) 2)
            (str "seed " seed ": and it keeps up once back"))))))

;; ============================================================
;; Crash recovery
;; ============================================================

(deftest a-restarted-node-re-derives-its-order-from-the-certificate-store
  (testing "Narwhal reconstructs from a certificate store rather than replaying
            events, and that is only possible because ordering is pure

           Nothing about the committed sequence is remembered. The node reloads
           its certificates, re-runs `commit-sequence` over every round, and
           gets back the prefix it had emitted before it died."
    (let [s (sim/run (make-sim {:seed 5}) 40)
          before (sim/committed s :a)
          after (-> s (sim/crash :a) (sim/run 3) (sim/restart :a) (sim/run 60))]
      (is (pos? (count before)))
      (is (= before (vec (take (count before) (sim/committed after :a))))
          "the re-derived prefix is the one it had")
      (is (sim/agreement? after))
      (is (empty? (filter #(= :revert-mismatch (:event %)) (:trace after)))
          "the revert-to-root resync names what it drops correctly")
      (is (>= (count (sim/committed after :a)) (count before))))))

(deftest a-commit-never-rides-ahead-of-the-write-it-rests-on
  (testing "the structural invariant behind re-derivation

           `insert-certificate` used to insert the certificate, order the DAG,
           and emit the resulting `commit` -- all at the top level, while that
           certificate's own `persist-then` was still in flight. Ordering is
           pure, so a restarted node re-derives its prefix from the certificate
           store instead of replaying a log; that argument only holds if every
           certificate the decision rested on is IN the store, and committing
           ahead of the barrier is exactly the window where it is not.

           Tendermint and SCP already ride their commit in `:then`. Bullshark
           was the one algorithm that did not, and it is the one whose recovery
           story leans on it hardest.

           Scanned across a whole run rather than a single insertion: the
           first version of this test drove one certificate by hand, that
           insertion happened to produce no commit at all, and the assertion
           held just as well with the bug back in place."
    (let [bare (atom 0)
          gated (atom 0)
          probe (reify n/Node
                  (capabilities [_] (n/capabilities (bs/create)))
                  (init [_ cfg] (n/init (bs/create) cfg))
                  (step [_ st in]
                    (let [{s :state fx :effects} (n/step (bs/create) st in)]
                      (swap! bare + (count (filter #(= :commit (n/effect-kind %)) fx)))
                      (swap! gated + (count (filter #(= :commit (n/effect-kind %))
                                                    (remove (set fx) (all-effects fx)))))
                      {:state s :effects fx})))
          s (sim/run (make-sim {:seed 3 :node probe}) 80)]
      (is (sim/agreement? s))
      (is (pos? @gated)
          "commits do happen in this run, so the next assertion means something")
      (is (zero? @bare)
          "and every one of them was behind the barrier, not ahead of it"))))

(deftest a-restart-tells-the-consumer-what-it-holds-even-when-that-is-nothing
  (testing "restore resets `:commit-index` to whatever it can re-derive, and the
           consumer has to be told -- INCLUDING when the answer is `[]`

           The resync was emitted only `(when (seq sequence))`, which skipped
           precisely the dangerous case. With `:commit-index` back at 0 and no
           resync, the node re-emitted its whole order as it re-derived, and the
           consumer, never told to drop the old copy, appended the second one to
           the first. The committed log came back literally doubled.

           Checked at the effect level because downstream this surfaces only as
           an agreement failure, on roughly one seed in three."
    (let [s (sim/run (make-sim {:seed 5}) 40)
          storage (get-in s [:storage :a] {})
          landed (:landed storage [])
          ;; Restore from a store stripped of certificates: the extreme of
          ;; "I re-derived less than I had already announced".
          without-certs (filterv (fn [w] (not-any? #(= :cert (first (key %)))
                                                   (:writes w)))
                                 landed)
          cfg (merge {:peer-id :a :validators [:a :b :c :d]
                      :restored {:durable (:durable storage {})
                                 :writes without-certs}}
                     (get-in s [:node-config :a]))
          {:keys [state effects]} (n/init (get-in s [:nodes :a :impl]) cfg)]
      (is (seq without-certs)
          "the store is not empty -- this is a restart, not a first boot")
      (is (zero? (:commit-index state)))
      (is (some #(= :resync (first %)) effects)
          "a node that comes back holding nothing must SAY it holds nothing"))))

(deftest re-derivation-does-not-replay-events
  (testing "the restored state comes from certificates alone; no vote, header
            or message is replayed"
    (let [s (sim/run (make-sim {:seed 5}) 40)
          writes (get-in s [:storage :a :landed])
          kinds (frequencies (map ffirst (mapcat :writes writes)))]
      (is (pos? (:cert kinds)))
      (is (pos? (:voted kinds)))
      (is (= #{:cert :voted :proposed} (set (keys kinds)))
          "three things are durable, and no event log among them: the
           certificate archive, the double-sign guard, and this node's own
           proposals so it can re-send rather than re-sign them"))))

(deftest the-double-vote-guard-survives-a-restart
  (testing "the guard is restored from DURABLE state and from nothing else

           A vote whose write never landed was never sent either -- it lives in
           the `persist-then`'s `:then` -- so losing it on a crash is correct,
           and asserting that the whole in-memory map comes back would be
           asserting a durability lie. What must hold is: every slot that
           reached disk comes back with the same value, and nothing comes back
           that did not."
    (let [s (sim/run (make-sim {:seed 9}) 30)
          voted-before (:voted (sim/node-state s :b))
          durable (into {} (comp (map :writes)
                                 (mapcat identity)
                                 (filter (fn [[k _]] (= :voted (first k))))
                                 (map (fn [[k v]] [(second k) v])))
                        (get-in s [:storage :b :landed]))
          after (-> s (sim/crash :b) (sim/run 2) (sim/restart :b))
          voted-after (:voted (sim/node-state after :b))]
      (is (seq voted-before))
      (is (seq durable))
      (is (= durable voted-after))
      (is (every? (fn [[slot h]] (= h (get voted-before slot))) durable)
          "and the durable value is the one the running node was using"))))

(deftest a-restarted-node-does-not-equivocate-with-its-own-past-self
  (testing "the failure this test was written for

           A node that persisted only the DIGEST of its own header knew it must
           not sign a different one and had no way to re-send the one it had
           signed. On restart it asked the application for a payload, built a
           header over a fresh parent set, got a different digest, and signed
           that -- a second signature for a slot it had already signed for,
           produced by an honest node, across a crash. The guard it kept for
           exactly this purpose did not fire, because the guard was consulted
           for OTHER authors' headers and not for its own."
    (doseq [seed [9 21 33]]
      (let [s (sim/run (make-sim {:seed seed}) 30)
            before (:voted (sim/node-state s :b))
            after (-> s (sim/crash :b) (sim/run 2) (sim/restart :b) (sim/run 20))
            own-slots (fn [m] (into {} (filter (fn [[[a _] _]] (= :b a))) m))]
        (is (seq (own-slots before)))
        (is (every? (fn [[slot h]] (= h (get (:voted (sim/node-state after :b)) slot)))
                    (own-slots before))
            (str "seed " seed ": every slot :b signed for keeps its value"))
        (is (sim/agreement? after) (str "seed " seed))))))

;; ============================================================
;; Byzantine behaviour
;; ============================================================

(declare corrupt)

(defn- corrupt
  "Rewrite one outbound effect, descending into the durability barrier.

  Descending into `:then` is not optional here for the same reason it was not
  for Tendermint: every message this node signs leaves through a
  `persist-then`, so an adversary that only rewrote bare broadcasts could not
  equivocate at all."
  [f effect]
  (case (n/effect-kind effect)
    :broadcast (or (f (:msg (n/effect-params effect))) [effect])
    :persist-then (let [p (n/effect-params effect)]
                    [[:persist-then (update p :then #(vec (mapcat (partial corrupt f) %)))]])
    [effect]))

(defrecord Adversary [inner f]
  n/Node
  (capabilities [_] (n/capabilities inner))
  (init [_ cfg] (update (n/init inner cfg) :effects #(vec (mapcat (partial corrupt f) %))))
  (step [_ st in] (update (n/step inner st in) :effects #(vec (mapcat (partial corrupt f) %)))))

(def two-headers
  "Broadcast two different headers for the same (author, round)."
  (fn [msg]
    (when (= :header (:kind msg))
      (let [h (:header msg)]
        [(n/broadcast :bullshark (assoc msg :header (assoc h :payload {:equivocation 1})))
         (n/broadcast :bullshark (assoc msg :header (assoc h :payload {:equivocation 2})))]))))

(deftest an-equivocating-author-certifies-nothing
  (testing "one vote per (author, round) plus 2f+1 signers per certificate

           :a really does sign two conflicting headers at every round. Neither
           can reach 2f+1 distinct signers, because the three honest validators
           vote for at most one of them between them, so :a contributes no
           vertex to the DAG at all -- and the other three continue, since 3 of
           4 is a quorum."
    (let [s (sim/run (sim/make {:seed 23
                                :nodes (assoc (into {} (map (fn [v] [v (bs/create)])) vs)
                                              :a (->Adversary (bs/create) two-headers))
                                :node-config (into {} (map (fn [v] [v atts])) vs)
                                :config {:value-fn value-fn}})
                     120)
          slots-of-a (fn [peer]
                       (->> (:slots (sim/node-state s peer))
                            keys (filter #(= :a (first %))) (map second) set))]
      (is (sim/agreement? s))
      (is (> (count (sim/committed s :b)) 15) "the honest majority keeps going")
      (doseq [peer [:b :c :d]]
        (is (= #{0} (slots-of-a peer))
            (str peer " holds only :a's genesis certificate, never a certified header")))
      (is (pos? (count (:equivocations s))))
      (is (= #{:conflicting-headers}
             (set (map (comp :kind :evidence) (:equivocations s))))))))

(deftest equivocation-is-reported-with-both-statements
  (let [s (sim/run (sim/make {:seed 23
                              :nodes (assoc (into {} (map (fn [v] [v (bs/create)])) vs)
                                            :a (->Adversary (bs/create) two-headers))
                              :node-config (into {} (map (fn [v] [v atts])) vs)
                              :config {:value-fn value-fn}})
                   40)
        ev (first (:equivocations s))]
    (is (= :a (:peer ev)))
    (is (string? (:first (:evidence ev))))
    (is (string? (:second (:evidence ev))))
    (is (not= (:first (:evidence ev)) (:second (:evidence ev))))))

;; ============================================================
;; Weighted stake
;; ============================================================

(deftest weighted-stake-changes-the-quorum-not-the-headcount
  (testing "with {:a 5 :b 1 :c 1 :d 1}, total 8, quorum is 6 and validity 3

           :a is necessary for every certificate and no two of {b,c,d} can
           certify anything. This is the configuration `node/threshold-membership`
           gets wrong -- it would compare a stake sum against a threshold
           computed from the head count."
    (let [weighted {:a 5 :b 1 :c 1 :d 1}]
      (is (= 6 (bs/quorum-threshold 8)))
      (is (= 3 (bs/validity-threshold 8)))
      (let [s (sim/run (sim/make {:seed 31
                                  :nodes (into {} (map (fn [v] [v (bs/create)])) vs)
                                  :node-config (into {} (map (fn [v] [v (merge atts {:stake weighted})])) vs)
                                  :config {:value-fn value-fn}})
                       80)]
        (is (sim/agreement? s))
        (is (pos? (count (sim/committed s :a))))))))

(deftest the-certificate-store-is-bounded-but-outlives-the-dag
  (testing "both halves, because either alone is a bug.

            `:certificates` and `:slots` grew without limit. The store is
            deliberately NOT released with the consensus DAG -- catch-up is
            served from it, and serving catch-up from the DAG was a real defect
            once: the GC empties the DAG by design, so a node that fell behind
            could never return. But `deliberately outlives` is not `never
            released`, and a node running for a week held every certificate it
            had ever seen.

            So: retention deeper than `gc-depth`, and actually finite."
    (let [gc 2
          ;; `:store-depth` set explicitly, and the test is worthless without
          ;; it: the default floors at 100 rounds, so a 30-round run never
          ;; reaches the frontier and the store keeps everything -- which makes
          ;; a correct horizon and a wrong one indistinguishable. Two earlier
          ;; versions of this test passed against a store released on the DAG's
          ;; own frontier for exactly that reason.
          st (assoc (dag-through 30 {:gc-depth gc}) :store-depth 8)
          [driven _] (drive st)
          depth (bs/store-depth driven)
          rounds-in-store (map #(:round (:header %)) (vals (:certificates driven)))]
      (is (pos? (:last-committed-round driven)) "it committed, so GC ran")

      ;; The DAG is the working set and is small.
      (is (< (count (keys (:dag driven))) 6)
          (str "the DAG retains few rounds, got " (sort (keys (:dag driven)))))

      ;; The store is deeper than the DAG -- that is the point of it.
      (is (> depth gc) "store-depth must exceed gc-depth")

      ;; THE property, and the previous version of this test did not pin it:
      ;; asserting the store merely holds MORE than the DAG passed even when the
      ;; two were released on the same frontier, because a count is not a
      ;; horizon. What matters is that the store still holds certificates from
      ;; rounds the DAG has dropped -- that is what a lagging peer is served
      ;; from.
      ;; Stated as a QUANTITY against the DAG's round frontier, not as a
      ;; comparison with the DAG's floor. Two earlier versions compared against
      ;; the floor and both passed under a store released on `gc-depth`,
      ;; because the DAG's per-author pass drops certificates BELOW each
      ;; author's watermark and so raises its floor above its own round
      ;; frontier -- which made the store look deeper than the DAG even when
      ;; the two frontiers were identical.
      (let [lcr (:last-committed-round driven)]
        (is (<= (apply min rounds-in-store) (- lcr gc 1))
            (str "the store must reach strictly deeper than the DAG's round "
                 "frontier (" (- lcr gc) "); its lowest round is "
                 (apply min rounds-in-store))))

      ;; And it is bounded: nothing older than the retention frontier survives.
      (is (every? #(>= % (- (:last-committed-round driven) depth)) rounds-in-store)
          (str "nothing below the frontier remains, got " (sort (distinct rounds-in-store))))
      (is (every? (fn [[[_ r] _]] (>= r (- (:last-committed-round driven) depth)))
                  (:slots driven))
          "and the slot map is trimmed on the same frontier"))))

;; ============================================================
;; Forged certificates
;; ============================================================

(deftest a-certificate-naming-signers-who-did-not-sign-is-not-certified
  (testing "SAFETY. `certified?` used to sum stake over `:signers`, a list of
            names supplied by whoever sent the message, while its docstring
            claimed the signatures had been checked at the edge and arrived as
            `:verified-by`. Nothing checked them, certificates carried no
            signature bytes, and `:verified-by` authenticates only the peer who
            RELAYED the message -- which for a certificate is precisely not one
            of the parties whose attestation matters.

            Narwhal verifies the aggregate before anything touches the
            certificate (`Certificate::verify`, types/src/primary.rs:516-546)."
    (let [st (node-init {})
          parents (into #{} (map :id) (vals (get-in st [:dag 0])))
          header {:author :b :round 1 :payload {:x 1} :parents parents}
          ;; A Byzantine relayer names every validator and attests for none.
          forged (bs/certificate header (into {} (map (fn [v] [v :not-a-signature])) vs))
          {st' :state} (insert st forged)]
      (is (= 4 (count (:signers forged))) "it claims a full quorum")
      (is (nil? (get-in st' [:dag 1 :b]))
          "and contributes nothing: unverifiable attestations carry no stake"))))

(deftest a-certificate-with-a-partially-forged-quorum-is-not-certified
  (testing "padding real signatures with junk must not reach the threshold"
    (let [st (node-init {})
          parents (into #{} (map :id) (vals (get-in st [:dag 0])))
          header {:author :b :round 1 :payload {:x 1} :parents parents}
          hid (bs/header-id header)
          ;; Two genuine attestations (below the quorum of 3) plus two forged.
          votes (merge (into {} (map (fn [v] [v ((:sign-vote atts) v hid)])) [:a :b])
                       {:c :junk :d :junk})
          {st' :state} (insert st (bs/certificate header votes))]
      (is (nil? (get-in st' [:dag 1 :b]))
          "2 real + 2 forged is 2, not 4"))))

(deftest a-genuinely-signed-certificate-is-accepted
  (testing "the guard must not simply reject everything -- without this the two
            tests above pass against a `certified?` that returns false"
    (let [st (node-init {})
          parents (into #{} (map :id) (vals (get-in st [:dag 0])))
          header {:author :b :round 1 :payload {:x 1} :parents parents}
          {st' :state} (insert st (cert* header #{:a :b :c}))]
      (is (some? (get-in st' [:dag 1 :b]))))))

(deftest a-vote-we-cannot-verify-is-not-aggregated-into-our-own-certificate
  (testing "we are about to mint a certificate peers accept on our say-so, so
            an unverifiable vote here would be a forgery WE created"
    (let [st (assoc (node-init {}) :peer-id :a)
          hdr {:author :a :round 1 :payload {:x 1}
               :parents (into #{} (map :id) (vals (get-in st [:dag 0])))}
          hid (bs/header-id hdr)
          st (assoc-in st [:own-headers 1] {:header hdr :id hid})
          step (fn [s from att]
                 (:state (n/step (bs/create) s
                                 (n/message-received from
                                                     {:kind :vote :header-id hid
                                                      :round 1 :att att}
                                                     #{from}))))
          bogus (step st :b :junk)
          good (step st :b ((:sign-vote atts) :b hid))]
      (is (nil? (get-in bogus [:votes 1 :b])) "junk is not recorded")
      (is (some? (get-in good [:votes 1 :b])) "a real attestation is"))))

;; ============================================================
;; Headers whose parents have not arrived
;; ============================================================

(deftest a-header-with-missing-parents-is-parked-and-voted-for-later
  (testing "LIVENESS. The header used to be dropped the moment the `:want` went
            out -- a one-shot request with nothing to receive the answer -- so
            the vote was lost for good.

            This is the NORMAL case, not an edge case: `round-parents` names
            every certificate we hold at the previous round, deliberately a
            maximal set, and an author proposes the instant it reaches 2f+1, so
            a peer one certificate behind at that moment drops the header. Each
            such peer never revisited it, the author fell short of a quorum, and
            its certificate for that round never formed -- and when the author
            is the anchor, a whole wave is wasted.

            Narwhal parks the header itself and loops it back through
            `process_header` once the parents land (`core.rs:644`)."
    (let [st (node-init {})
          genesis-ids (into #{} (map :id) (vals (get-in st [:dag 0])))
          ;; Three round-1 certificates: a quorum of 4 validators is 3.
          r1 (mapv (fn [a]
                     (cert* {:author a :round 1 :payload [a 1] :parents genesis-ids}
                            #{:a :b :c}))
                   [:a :b :c])
          ;; The node holds two of them; the third is still in flight.
          st (reduce (fn [s c] (:state (insert s c))) st (take 2 r1))
          hidden (nth r1 2)
          ;; A round-2 header naming all three as parents.
          hdr {:author :d :round 2 :payload {:y 2}
               :parents (into #{} (map :id) r1)}
          {parked :state fx1 :effects}
          (n/step (bs/create) st (n/message-received :d {:kind :header :header hdr} #{:d}))]
      (is (some #(= :broadcast (n/effect-kind %)) fx1) "it asks for the parents")
      (is (nil? (get-in parked [:voted [:d 2]])) "and does not vote yet")
      (is (pos? (pending/held (:pending-headers parked)))
          "but the header is HELD, not dropped")
      ;; The missing parent arrives.
      (let [{after :state} (n/step (bs/create) parked (n/vertex-received hidden))]
        (is (some? (get-in after [:voted [:d 2]]))
            "the parked header is re-processed and finally voted for")
        (is (zero? (pending/held (:pending-headers after)))
            "and released from the pool")))))

(deftest a-parked-header-is-not-re-parked-on-redelivery
  (testing "a peer re-sending the same header must not grow the pool"
    (let [st (node-init {})
          genesis-ids (into #{} (map :id) (vals (get-in st [:dag 0])))
          hdr {:author :c :round 2 :payload {:y 2}
               :parents (conj genesis-ids "no-such-parent")}
          feed (fn [s] (:state (n/step (bs/create) s
                                       (n/message-received
                                        :c {:kind :header :header hdr} #{:c}))))
          once (feed st)
          twice (feed once)]
      (is (= (pending/held (:pending-headers once))
             (pending/held (:pending-headers twice)))
          "idempotent on the header id"))))

(deftest a-certificate-costs-at-most-one-verification-per-validator
  (testing "`certified?` verified the WHOLE attacker-supplied `:votes` map
            before the threshold arithmetic rejected it, so one certificate
            naming a million unknown signers cost a million Ed25519
            verifications inside `step`, on the event loop.

           Filtering by membership first is strictly equivalent -- a signer
           with no stake contributes zero weight whether or not its attestation
           verifies -- and bounds the work to the committee size."
    (let [verifications (atom 0)
          counting (fn [signer hid att]
                     (swap! verifications inc)
                     ((:verify-vote atts) signer hid att))
          st (assoc (state) :verify-vote counting :peer-id :a)
          h {:author :a :round 1 :payload [:a 1] :parents #{}}
          ;; A certificate padded with ten thousand signers nobody has heard of.
          padded (bs/certificate h (into {} (map (fn [i] [(keyword (str "ghost" i)) :junk]))
                                         (range 10000)))]
      (is (false? (boolean (#'bs/certified? st padded)))
          "it is still rejected")
      (is (<= @verifications (count vs))
          (str "and rejecting it cost at most one verification per validator: "
               @verifications)))))

(deftest a-want-is-bounded-and-only-served-to-validators
  (testing "`digests` was attacker-supplied and served whole, one `send-to` per
            hit -- and the runtime emulates unicast as a broadcast, so every
            reply reaches every peer. One `:want` naming fifty thousand digests
            made each of n nodes emit fifty thousand certificate messages, each
            delivered n times.

           An honest `:want` asks for one round's missing parents, at most one
           per validator, so the committee size is a generous cap."
    (let [s (sim/run (make-sim {:seed 5}) 40)
          st (sim/node-state s :a)
          ;; Every digest we hold, repeated far beyond any honest request.
          held (vec (keys (:certificates st)))
          many (vec (take 5000 (cycle held)))
          from-validator (n/step (bs/create) st
                                 (n/message-received :b {:kind :want :from :b
                                                         :digests many} #{:b}))
          from-stranger (n/step (bs/create) st
                                (n/message-received :zz {:kind :want :from :zz
                                                         :digests many} #{:zz}))]
      (is (<= (count (filter #(= :send (n/effect-kind %)) (:effects from-validator)))
              (count vs))
          "a validator gets at most one reply per committee member")
      (is (empty? (filter #(= :send (n/effect-kind %)) (:effects from-stranger)))
          "and a non-validator gets nothing at all"))))
