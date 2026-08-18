(ns urd.consensus.portability-test
  "Values that MUST be identical on Clojure and ClojureScript.

  This file is `.cljc` and contains no host interop, so the same assertions can
  be run under both. That matters more than it sounds: the divergence this file
  now pins was live for as long as the simulator existed, and was invisible
  because every test that could have caught it was JVM-only.

  The failure mode is specific and worth remembering. ClojureScript's `bit-and`
  returns a SIGNED 32-bit integer, so `(bit-and 0xFFFFFFFF 0xFFFFFFFF)` is -1
  rather than 4294967295. The bit pattern is correct; the number is not. Nothing
  breaks while the value is only ever xor'd and shifted -- but the moment it is
  compared or reduced modulo something, the two platforms take different
  branches. In `rng/next-int` that meant different draws, and therefore
  different message delays, different drop decisions and different sampled
  peers, in a namespace whose entire purpose is that a failing schedule
  reproduces anywhere.

  Numbers below were taken from the JVM and verified against Node."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.reconfig :as rc]
            [urd.consensus.node :as n]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.nakamoto :as nk]
            [urd.consensus.algorithms.snowman :as sm]
            [urd.consensus.algorithms.snowtree :as snowtree]
            [urd.consensus.algorithms.bullshark :as bs]
            [urd.consensus.bignat :as bn]
            [urd.consensus.proposer :as proposer]
            [urd.consensus.signing :as signing]
            [urd.consensus.rng :as rng]))

(defn- words [seed n]
  (loop [r (rng/make seed), acc [], i 0]
    (if (= i n) acc (let [[w r'] (rng/next-word r)] (recur r' (conj acc w) (inc i))))))

(defn- int-draws [seed bound n]
  (loop [r (rng/make seed), acc [], i 0]
    (if (= i n) acc (let [[v r'] (rng/next-int r bound)] (recur r' (conj acc v) (inc i))))))

(deftest rng-words-are-unsigned
  (testing "a 32-bit word must be a non-negative NUMBER, not just the right bits"
    (is (every? #(and (>= % 0) (<= % 4294967295)) (words 12345 200)))))

(deftest rng-agrees-across-platforms
  (testing "pinned sequences -- run this namespace under cljs too"
    (is (= [3336926330 1697253807 2816511904 1955480042
            718842323 3283620450 4285686168 3680911160]
           (words 12345 8)))
    ;; This is the assertion that fails on the old, signed implementation:
    ;; ClojureScript produced [83 55 11 49 71 56 62 87].
    (is (= [83 55 7 45 67 56 62 87] (int-draws 7 100 8)))))

(deftest election-timeouts-agree-across-platforms
  (testing "a node must not draw a different election timeout in the browser

           If it did, a schedule that reproduced a split vote on the JVM would
           not reproduce it in cljs, which is the one thing the logical clock is
           supposed to guarantee."
    (is (= [12 12 18 16 12]
           (mapv #(raft/randomized-election-timeout % 7 10) [:n1 :n2 :n3 :n4 :n5])))
    ;; A large term is the case that overflows a 32-bit FNV multiply in a double.
    (is (= [11 18 13 11 14]
           (mapv #(raft/randomized-election-timeout % 100000 10) [:n1 :n2 :n3 :n4 :n5])))
    ;; The DRAW is part of the key now -- PreVote does not bump the term, so
    ;; without it the offset is constant across pre-vote rounds. It has to agree
    ;; across platforms for the same reason the rest of this does.
    (is (= [12 17 17 12 17]
           (mapv #(raft/randomized-election-timeout :n1 7 % 10) (range 5))))))

(deftest election-timeouts-are-in-range-and-vary
  (testing "[et, 2et), and different for different nodes in the same term"
    (let [ts (mapv #(raft/randomized-election-timeout % 3 10)
                   [:n1 :n2 :n3 :n4 :n5 :n6 :n7])]
      (is (every? #(and (>= % 10) (< % 20)) ts))
      (is (> (count (distinct ts)) 1)
          "identical timeouts would make split votes unresolvable"))))

;; ============================================================
;; Tendermint's integer arithmetic
;;
;; Proposer selection is the only place in the Tendermint port that does
;; non-obvious integer maths, and it does it three ways in ten lines: a
;; truncating divide in `rescale`, a FLOORING divide in `center`, and an
;; arithmetic shift in `new-validator-priority`. All three round differently on
;; negatives, and the shift is 32-bit in ClojureScript.
;; ============================================================

(deftest proposer-selection-agrees-across-platforms
  (let [p0 (proposer/initial-priorities [:a :b :c :d])]
    (is (= [:a :b :a :c :d :a :b :a]
           (mapv #(proposer/proposer-for p0 {:a 4 :b 2 :c 1 :d 1} %) (range 8))))))

(deftest priority-centering-floors-on-both-platforms
  (testing "`quot` truncates toward zero and would give {:a 0 :b -1 :c 0 :d 0}
            here; CometBFT's big.Int.Div floors, and so must we"
    (is (= {:a 1 :b 0 :c 1 :d 1} (proposer/center {:a 0 :b -1 :c 0 :d 0})))))

(deftest priority-rescaling-truncates-toward-zero-on-both-platforms
  (testing "and this one must NOT floor: Go's int64 `/` truncates, so a
            negative priority rounds up, not down"
    (is (= {:a 7 :b 0 :c 0 :d 0} (proposer/rescale {:a 1000 :b 0 :c -3 :d 0} 8)))))

(deftest the-new-validator-shift-agrees-across-platforms
  (testing "ClojureScript's bit-shift-right is a 32-bit signed shift"
    (is (= [-1 -7 -9 -18 -1125]
           (mapv proposer/new-validator-priority [1 7 8 16 1000])))))

(deftest the-double-sign-guard-agrees-across-platforms
  (is (= [false false true true true false]
         (mapv #(signing/may-sign? % {:height 3 :round 2 :step :prevote})
               [{:height 3 :round 2 :step :prevote}
                {:height 3 :round 2 :step :propose}
                {:height 3 :round 2 :step :precommit}
                {:height 3 :round 3 :step :propose}
                {:height 4 :round 0 :step :propose}
                {:height 2 :round 9 :step :precommit}]))))

;; ============================================================
;; Nakamoto: 256-bit arithmetic and proof of work
;;
;; This is the part of the codebase with the most room to diverge and the least
;; chance of the divergence being visible. Cumulative work is a 256-bit
;; quantity; a JavaScript double holds 53 bits exactly. Had `bignat` been a
;; reader conditional over BigInteger and js/BigInt, every value below would
;; have been computed by two different implementations, and a fork-choice
;; comparison that disagreed by one unit would move the chain tip in a browser
;; and not on the JVM. It is one implementation, and these values pin it.
;; ============================================================

(def mainnet-genesis
  {:version 1
   :prev nk/zero-hash
   :merkle-root "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"
   :time 1231006505
   :bits 0x1d00ffff
   :nonce 2083236893})

(deftest big-arithmetic-agrees-across-platforms
  (testing "multiplication and division of 256-bit naturals"
    (is (= "000010c6f45449cb59c68de5940cbb3a00c64fb40c5045ab2cf943affe7d139d"
           (bn/to-hex (bn/div (bn/pow2 256) (bn/from-int 1000003)) 32))
        "a full-width division -- the loop `calc-work` runs")
    (is (= "00000000ddb06310dc4b61d816347d5111d40e6023f7473f82b28e242d2075a5"
           (bn/to-hex (bn/mul (bn/from-hex "deadbeefcafe0123456789abcdef")
                              (bn/from-hex "fedcba98765432100123456789ab"))
                      32))
        "a schoolbook multiply, whose accumulator is the widest intermediate
         anywhere in the library")
    (is (= 257 (bn/bit-length (bn/pow2 256))))))

(deftest proof-of-work-agrees-across-platforms
  (testing "the header encoding and double-SHA256, against Bitcoin's own genesis

           This is the most load-bearing value in the algorithm. If the byte
           order, the little-endian fields, or the digest differ between
           platforms, a browser node and a JVM node disagree about which blocks
           exist at all."
    (is (= "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
           (nk/header-id mainnet-genesis)))
    (is (nk/pow-valid? mainnet-genesis))
    (is (= 4295032833 (bn/to-int (nk/calc-work 0x1d00ffff)))
        "difficulty 1 is exactly 2^32 expected hashes")
    (is (= "00000000000000000000000000000000000000000000000000003fb3ab764c00"
           (bn/to-hex (nk/calc-work 0x1b0404cb) 32)))))

(deftest compact-codec-agrees-across-platforms
  (testing "the codec is bit manipulation on values above 2^31, which is exactly
           where ClojureScript's signed 32-bit bit operations bite"
    (is (= 0x0200ff00 (nk/target->compact (bn/from-int 255)))
        "the sign-bit renormalisation")
    (is (= 0x03010000 (nk/target->compact (nk/compact->target 0x05000001))))
    (is (= 31 (nk/compact-exponent 0x1f123456)))
    (is (= 128 (nk/compact-exponent 0x80123456))
        "THIS is the value above 2^31. 0x1f123456 is 5.2e8, well below it, so
         the case this test was named for was never actually exercised by it:
         cljs `bit-shift-right` treats its operand as a signed 32-bit integer,
         and only a compact value with the top bit set can catch that.")
    (is (= 255 (nk/compact-exponent 0xffffffff))
        "and the extreme: 0xffffffff >> 24 is -1 under a signed shift, 255 here")
    (is (nk/compact-negative? 0xff800000))
    (is (= 0x1b010132 (nk/retarget (nk/params {:pow-limit-bits 0x1d00ffff})
                                   0x1b0404cb 1000000 1000001))
        "a retarget clamped at the 1/4 bound")))

(deftest orphan-drain-order-agrees-across-platforms
  (testing "which of two equal-work siblings wins a tie is decided by the order
           the orphan pool drains, and the pool is a SET.

           `drain-orphans` sorts by header id for exactly this reason -- set
           iteration order is not guaranteed equal on the JVM and in a browser,
           and first-seen is Bitcoin's tie-break, so an unsorted iteration would
           be a platform-dependent FORK. That sort had no cross-platform test:
           `nakamoto_test.clj` is `.clj`-only, so a regression would have been
           invisible on the only platform the suite ran on.

           Two siblings on the same parent at the same difficulty carry the same
           work. Both arrive while their parent is missing; the parent then
           lands and drains them together. Whichever the drain reaches first
           becomes the tip and the second cannot displace it, because fork
           choice uses a strict `>`."
    (let [p (nk/params {:pow-limit-bits 0x207fffff :no-retargeting? true
                        :median-time-blocks 3})
          genesis {:version 1 :prev nk/zero-hash
                   :merkle-root (apply str (repeat 64 \a))
                   :time 1000000 :bits 0x207fffff :nonce 0}
          st (:state (n/init (nk/create) {:peer-id :p :validators [:p]
                                          :params p :genesis genesis
                                          :now 2000000000}))
          gid (nk/header-id genesis)
          root (nk/mine (nk/template st {:on gid
                                         :merkle-root (apply str (repeat 64 \b))
                                         :time 1000001})
                        1000000)
          rid (nk/header-id root)
          ;; `template` builds on OUR tip, which is still genesis, so the
          ;; parent is set explicitly: these two are children of `root`, which
          ;; this node has not seen.
          sib (fn [tag] (nk/mine (assoc (nk/template st {:on gid :merkle-root tag
                                                         :time 1000002})
                                        :prev rid)
                                 1000000))
          x (sib (apply str (repeat 64 \c)))
          y (sib (apply str (repeat 64 \d)))
          ;; Both siblings arrive first, so both are parked; then the parent.
          deliver (fn [order]
                    (:tip (reduce (fn [s h] (:state (nk/process-header s h nil)))
                                  st
                                  (concat order [root]))))]
      (is (some? x))
      (is (some? y))
      (is (= (deliver [x y]) (deliver [y x]))
          "the drain is sorted, so the winner does not depend on which sibling
           was parked first -- and, given a sorted drain, does not depend on the
           host's set iteration order either")
      (is (= (first (sort [(nk/header-id x) (nk/header-id y)])) (deliver [x y]))
          "and the winner is the lower id, which is the sort the code applies")
      (is (not= (nk/header-id x) (nk/header-id y))
          "the two siblings must actually differ, or nothing above is a tie"))))

(deftest snowman-choice-keys-agree-across-platforms
  (testing "the Tree indexes candidates by the BITS of a derived key, so if the
           two platforms derive different keys they build different tries from
           the identical block set -- different sibling groupings, different
           polls combining, and eventually different blocks accepted. Silently,
           with nothing on the wire to disagree about.

           `hasch/uuid` is content-addressed and synchronous on both platforms,
           which is why it was chosen over requiring hash-shaped ids; this is
           the test that makes that a claim rather than an assumption."
    (is (= ["2ee7865756e058e5889eb19111fa41c9"
            "3c0511d7889d5a928c93614b0a4a777a"
            "16c22e42748554688f89d77078fad2c4"
            "0fc20a9ac153592d888a707ff306fbb6"]
           (mapv sm/choice-key [:blk1 :genesis "x" 42])))
    (is (= 128 (snowtree/num-bits (sm/choice-key :blk1))))
    (is (= [0 1 0 0 0 1 1 1]
           (mapv #(snowtree/bit-at (sm/choice-key :blk1) %) (range 8)))
        "and the bit ORDER over that key is the same, which is the part the
         trie shape actually depends on")))

;; ============================================================
;; Bullshark: the total order itself
;;
;; This is the strongest cross-platform claim in the codebase, because it is
;; the only one where a divergence would be a CONSENSUS FAILURE rather than a
;; performance or scheduling difference: two nodes running the identical
;; certified DAG would commit the identical vertices in a different sequence,
;; each convinced it was correct, with no message lost and nothing to detect it
;; on. Bullshark's ordering layer sends nothing, so there is no disagreement to
;; observe -- only two divergent histories.
;;
;; Three things have to agree for the order to agree:
;;
;;   1. `hasch/uuid` over the header map -- the vertex identity;
;;   2. the STRING comparison of digests, which fixes the DFS push order.
;;      This is why digests are strings: the JVM's `UUID/compareTo` compares
;;      the two 64-bit halves as SIGNED longs, ClojureScript's compares the
;;      printed string, and those orders differ for any pair whose high bit
;;      differs -- half of all pairs;
;;   3. the STABILITY of `sort-by`, which preserves DFS order within a round
;;      (TimSort on the JVM, `goog.array/stableSort` in ClojureScript).
;;
;; Only (1) would be caught by a digest fingerprint alone, which is why the
;; whole committed sequence is pinned rather than a hash of one header.
;; ============================================================

(def ^:private bs-validators [:a :b :c :d])

(def ^:private bs-atts (bs/test-attestations))

(defn- bs-cert*
  "A certificate whose attestations verify. Signers used to be a bare set; a
  certificate is relayed by non-signers, so the names alone are worth nothing."
  [header signers]
  (bs/certificate header
                  (into {} (map (fn [s] [s ((:sign-vote bs-atts) s (bs/header-id header))]))
                        signers)))
(def ^:private bs-uniform {:a 1 :b 1 :c 1 :d 1})

(defn- bs-state []
  (let [genesis (bs/genesis-certificates bs-validators)]
    {:dag {0 genesis}
     :last-committed (into {} (map (fn [v] [v 0])) bs-validators)
     :last-committed-round 0
     :certificates (into {} (map (fn [[_ c]] [(:id c) c])) genesis)
     :slots {}
     :gc-depth 50
     :stake bs-uniform
     :total-stake 4
     :validators bs-validators
     :anchor-fn bs/round-robin-anchor}))

(defn- bs-dag
  "A complete DAG of `n` rounds: every author names every certificate below."
  [n]
  (reduce (fn [st r]
            (let [parents (into #{} (map :id) (vals (get-in st [:dag (dec r)])))]
              (reduce (fn [s a]
                        (let [c (bs-cert* {:author a :round r :payload [a r]
                                           :parents parents}
                                          (set bs-validators))]
                          (-> s
                              (assoc-in [:dag r a] c)
                              (assoc-in [:certificates (:id c)] c))))
                      st bs-validators)))
          (bs-state)
          (range 1 (inc n))))

(defn- bs-order [n]
  (mapv (fn [c] [(:round (:header c)) (:author (:header c))])
        (second (reduce (fn [[s acc] r]
                          (let [[s' out] (bs/commit-sequence s r bs/anchor-for)]
                            [s' (into acc out)]))
                        [(bs-dag n) []]
                        (range 0 (inc n))))))

(deftest bullshark-digests-agree-across-platforms
  (testing "content-addressed vertex identity, as strings"
    (is (= "2a105f13-f6c8-5569-9e4d-16fb96f523f9"
           (bs/header-id {:author :a :round 3 :payload {:x 1} :parents #{"p1" "p2"}})))
    (is (= "175ad1a9-6b63-5098-8496-ccc286bc33bc"
           (:id (bs-cert* {:author :a :round 3 :payload {:x 1}
                           :parents #{"p1" "p2"}}
                          #{:a :b :c}))))
    (is (= ["29966a27-531d-5851-97c0-2c90400af2a0"
            "10dc3042-d601-550c-bed0-b83f57668772"
            "1163405a-3ac1-54d0-846d-458bf1e3a5ed"
            "3f773d04-8383-596a-a3eb-53d891f9ef88"]
           (mapv #(:id (get (bs/genesis-certificates bs-validators) %)) bs-validators))
        "the genesis set every node derives from the committee alone")))

(deftest bullshark-total-order-agrees-across-platforms
  (testing "the committed sequence of a seven-round DAG, vertex by vertex

           Note the intra-round orders differ from round to round -- round 1 is
           b,d,c,a and round 2 is c,b,a,d -- which is the DFS-then-stable-sort
           at work. If this were author order or insertion order the assertion
           would be vacuous."
    (is (= [[1 :b] [1 :d] [1 :c] [1 :a]
            [2 :c] [2 :b] [2 :a] [2 :d]
            [3 :b] [3 :c] [3 :d] [3 :a]
            [4 :a] [4 :b] [4 :c] [4 :d]
            [5 :c] [5 :d] [5 :b] [5 :a]
            [6 :c]]
           (bs-order 7)))))

(deftest bullshark-anchor-selection-agrees-across-platforms
  (testing "a stake-weighted draw seeded by the round

           An anchor rule that disagreed between a browser and the JVM would
           split the network on the total order without a message being lost.

           These values changed when the draw moved from `rng/make` to
           `rng/from-key`. Worth noting what the old uniform pin was:

               [:b :b :c :d :a :b :c :d :a :b :c :d]

           `round mod n` from round 2 on, written out in full in a test file,
           and read for what it is by nobody -- including me, twice. A golden
           pin proves two platforms agree; it does not notice that what they
           agree on is degenerate. See `anchors-do-not-cycle-and-do-not-exclude-anyone`."
    (is (= [:a :a :b :b :a :d :b :b :d :b :a :b]
           (mapv #(bs/stake-weighted-anchor % bs-validators {:a 4 :b 2 :c 1 :d 1})
                 (range 12))))
    (is (= [:b :d :a :b :d :d :b :a :d :a :d :a]
           (mapv #(bs/stake-weighted-anchor % bs-validators bs-uniform) (range 12))))))

(deftest bullshark-thresholds-agree-across-platforms
  (testing "integer division, and both are over total STAKE"
    (is (= [1 2 3 3 4 5 5 6 7 7 27]
           (mapv bs/quorum-threshold [1 2 3 4 5 6 7 8 9 10 40])))
    (is (= [1 1 1 2 2 2 3 3 3 4 14]
           (mapv bs/validity-threshold [1 2 3 4 5 6 7 8 9 10 40])))))

;; ============================================================
;; The Tree's SHAPE, not just its inputs
;; ============================================================

(deftest the-trie-built-from-a-choice-set-agrees-across-platforms
  (testing "`snowman-choice-keys-agree-across-platforms` above pins the Tree's
            INPUTS -- the derived key, its bit count, and the bit order over it.
            It does not pin what the Tree BUILDS from them, and the building is
            where the arithmetic is: `unaryNode.Add`'s five-case split computes
            prefix boundaries, and `record-poll` collapses nodes on finalize.

            That gap matters more here than almost anywhere else in the
            codebase. The ClojureScript compiler emits nil-arithmetic warnings
            in `unary-add` -- it cannot prove the split index is non-nil,
            though the `(if (nil? index) ...)` guard above it does -- and on
            the JVM a nil there THROWS while under ClojureScript it yields NaN
            and corrupts the trie silently. Two nodes on different platforms
            would then group siblings differently from the identical block set,
            combine different polls, and accept different blocks, with nothing
            on the wire to disagree about.

            So the structure is pinned outright. If the split arithmetic ever
            differs between platforms -- by NaN or by anything else -- these
            values differ."
    (let [params {:k 3 :alpha-preference 2 :alpha-confidence 2 :beta 2}
          key-of (into {} (map (fn [c] [c (sm/choice-key c)])) [:a :b :c :d])
          built (-> (snowtree/tree params :a (key-of :a))
                    (snowtree/tree-add :b (key-of :b))
                    (snowtree/tree-add :c (key-of :c))
                    (snowtree/tree-add :d (key-of :d)))]
      (is (= {:binary 0 :confidence [0] :prefers 0 :finalized? false
              :children
              [{:binary 1 :confidence [0] :prefers 1 :finalized? false
                :children [{:unary [2 128] :confidence [0] :finalized? false}
                           {:unary [2 128] :confidence [0] :finalized? false}]}
               {:unary [1 4] :confidence [0] :finalized? false
                :child {:binary 4 :confidence [0] :prefers 1 :finalized? false
                        :children [{:unary [5 128] :confidence [0] :finalized? false}
                                   {:unary [5 128] :confidence [0] :finalized? false}]}}]}
             (snowtree/describe built))
          "the trie shape is a function of the keys alone, so both platforms
           must derive the identical one")

      (testing "and polling to a decision collapses it identically"
        (let [decided (-> built
                          (snowtree/tree-record-poll {:b 3})
                          (snowtree/tree-record-poll {:b 3}))]
          (is (= {:unary [2 128] :confidence [2] :finalized? true}
                 (snowtree/describe decided))
              "collapse-on-finalize leaves the same node on both platforms")
          (is (= :b (snowtree/tree-preference decided)))
          (is (true? (snowtree/tree-finalized? decided))))))))

(deftest reconfiguration-is-identical-on-both-platforms
  (testing "`urd.consensus.reconfig` is arithmetic over voting power, which is
            exactly the shape that has diverged here before.

           The power ceiling in particular: CometBFT derives theirs from
           `MaxInt64`, and a port that copied the derivation would be silently
           wrong under ClojureScript, where numbers are doubles and exact
           integer arithmetic stops at 2^53. It is written as a literal below
           2^53 for that reason, and this test is what stops the literal from
           drifting back into a computed value that only works on one platform.

           Requiring the namespace here is half the point -- until this, no
           ClojureScript build compiled it at all."
    (is (= 137438953472 rc/max-total-power)
        "the ceiling is the same number on both platforms")
    (is (< rc/max-total-power 9007199254740992)
        "and below 2^53, where a double stops being an exact integer")

    (let [cfg {:validators [:a :b :c] :powers {:a 1 :b 1 :c 1}
               :priorities {:a 0 :b 0 :c 0}}]
      (is (= {:validators [:a :b :c :d]
              :powers {:a 1 :b 1 :c 1 :d 1}
              :priorities {:a 0 :b 0 :c 0 :d -4}}
             (rc/apply-updates cfg [{:id :d :power 1}]))
          "including the joining penalty, which is an integer shift -- the
           operation whose ClojureScript behaviour differs from the JVM's")
      (is (= :duplicate-update
             (:error (rc/apply-updates cfg [{:id :a :power 2} {:id :a :power 3}])))
          "and the rejections are classified the same way on both"))))
