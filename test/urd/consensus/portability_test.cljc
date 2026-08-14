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
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.nakamoto :as nk]
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
    (is (= [16 19 10 17 14]
           (mapv #(raft/randomized-election-timeout % 7 10) [:n1 :n2 :n3 :n4 :n5])))
    ;; A large term is the case that overflows a 32-bit FNV multiply in a double.
    (is (= [17 18 13 18 15]
           (mapv #(raft/randomized-election-timeout % 100000 10) [:n1 :n2 :n3 :n4 :n5])))))

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
    (is (= 31 (nk/compact-exponent 0x1f123456))
        "extracting the exponent of a compact value above 2^31")
    (is (nk/compact-negative? 0xff800000))
    (is (= 0x1b010132 (nk/retarget (nk/params {:pow-limit-bits 0x1d00ffff})
                                   0x1b0404cb 1000000 1000001))
        "a retarget clamped at the 1/4 bound")))

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
                        (let [c (bs/certificate {:author a :round r :payload [a r]
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
           (:id (bs/certificate {:author :a :round 3 :payload {:x 1}
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
           split the network on the total order without a message being lost."
    (is (= [:a :a :a :a :b :b :c :d :a :a :a :a]
           (mapv #(bs/stake-weighted-anchor % bs-validators {:a 4 :b 2 :c 1 :d 1})
                 (range 12))))
    (is (= [:b :b :c :d :a :b :c :d :a :b :c :d]
           (mapv #(bs/stake-weighted-anchor % bs-validators bs-uniform) (range 12))))))

(deftest bullshark-thresholds-agree-across-platforms
  (testing "integer division, and both are over total STAKE"
    (is (= [1 2 3 3 4 5 5 6 7 7 27]
           (mapv bs/quorum-threshold [1 2 3 4 5 6 7 8 9 10 40])))
    (is (= [1 1 1 2 2 2 3 3 3 4 14]
           (mapv bs/validity-threshold [1 2 3 4 5 6 7 8 9 10 40])))))
