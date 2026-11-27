(ns urd.consensus.algorithms.nakamoto-test
  "Tests for the Nakamoto header-layer node.

  Two layers, and the first matters more than the second. The pure functions --
  the compact codec, cumulative work, the retarget, median-time-past -- are the
  prime verification targets, because a Nakamoto node is almost entirely
  arithmetic and almost none of the arithmetic is obvious. The node tests then
  check that the arithmetic is wired into fork choice correctly, in the
  simulator, under partitions.

  Every test runs at a deliberately trivial proof-of-work difficulty. Mining for
  real is out of scope by design: a JVM nonce loop is orders of magnitude off an
  ASIC, and it is not what is under test."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.bignat :as bn]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.nakamoto :as nk]))

;; ============================================================
;; Bitcoin mainnet conformance -- the one real-world anchor
;; ============================================================

(def mainnet-genesis
  "Bitcoin's actual genesis header. If anything in the serialization, the byte
  order, or the double-SHA256 is wrong, this hash is wrong."
  {:version 1
   :prev nk/zero-hash
   :merkle-root "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"
   :time 1231006505
   :bits 0x1d00ffff
   :nonce 2083236893})

(deftest genesis-header-hashes-to-the-real-block-id
  (testing "the whole encoding, end to end, against a value the world agrees on"
    (is (= 80 (count (nk/serialize-header mainnet-genesis))))
    (is (= "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
           (nk/header-id mainnet-genesis)))
    (is (nk/pow-valid? mainnet-genesis)
        "and Satoshi's nonce really does solve it")))

(deftest block-one-hashes-correctly-and-links
  (testing "a second real header, to pin the prev-hash byte order specifically --
            genesis alone cannot, because its prev is all zeros and reversing it
            is a no-op"
    (let [block-1 {:version 1
                   :prev "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
                   :merkle-root "0e3e2357e806b6cdb1f70b54c3a3a17b6714ee1f0e68bebb44a74b1efd512098"
                   :time 1231469665
                   :bits 0x1d00ffff
                   :nonce 2573394689}]
      (is (= "00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048"
             (nk/header-id block-1)))
      (is (nk/pow-valid? block-1)))))

;; ============================================================
;; The compact target codec
;; ============================================================

(deftest compact-codec-worked-cases
  (testing "the canonical non-canonical encodings normalise as btcd does"
    ;; 0x05000001 is 1 * 256^2 = 65536, whose canonical form uses exponent 3.
    (is (= 65536 (bn/to-int (nk/compact->target 0x05000001))))
    (is (= 0x03010000 (nk/target->compact (nk/compact->target 0x05000001))))
    ;; An exponent below 3 discards the low mantissa bytes.
    (is (= 0x1234 (bn/to-int (nk/compact->target 0x02123456))))
    (is (= 0x02123400 (nk/target->compact (nk/compact->target 0x02123456))))))

(deftest sign-bit-renormalisation
  (testing "255 cannot be written 0x01ff0000: the mantissa's top bit would land
            on the SIGN bit, so the value is divided by 256 and the exponent
            incremented -- `workmath/difficulty.go:113-118`"
    (is (= 0x0200ff00 (nk/target->compact (bn/from-int 255))))
    (is (= 255 (bn/to-int (nk/compact->target 0x0200ff00))))
    (testing "and 0x01ff0000 itself is therefore a NEGATIVE compact number,
              since bit 23 is the sign -- a header claiming it is rejected"
      (is (nk/compact-negative? 0x01ff0000))
      (is (= bn/zero (nk/calc-work 0x01ff0000)))
      (is (not (nk/target-valid? (nk/params {}) 0x01ff0000))))))

(deftest btcd-codec-conformance
  (testing "the two vectors btcd's own difficulty_test.go carries"
    ;; BigToCompact(-1) = 25231360; we encode magnitudes only, so the negative
    ;; flag is the caller's business, but the magnitude half must agree.
    (is (= 0x01010000 (nk/target->compact (bn/from-int 1))))
    (is (= 25231360 (+ 0x01010000 0x00800000)))
    ;; CompactToBig(10000000) = 0 -- exponent 0 shifts the mantissa away.
    (is (= bn/zero (nk/compact->target 10000000)))
    (is (= bn/zero (nk/calc-work 10000000)))))

(defspec compact-roundtrip-is-identity-on-canonical-inputs 300
  (testing "target->compact . compact->target = id, for every compact value that
            is already canonical"
    (prop/for-all [e (gen/choose 4 32)
                   m (gen/choose 1 0x7fffff)]
                  (let [c (+ (* e 16777216) m)
                        c' (nk/target->compact (nk/compact->target c))]
                    ;; Non-canonical inputs (a mantissa with trailing zero bytes)
                    ;; normalise to a smaller exponent, so we compare VALUES.
                    (= (nk/compact->target c) (nk/compact->target c'))))))

(defspec compact-encoding-never-sets-the-sign-bit 300
  (testing "a natural number must not encode as a negative target"
    (prop/for-all [bs (gen/vector (gen/choose 0 255) 1 32)]
                  (let [c (nk/target->compact (bn/from-bytes-be bs))]
                    (not (nk/compact-negative? c))))))

(defspec compact-encoding-never-rounds-up 300
  (testing "the 23-bit mantissa loses precision; it must lose it DOWNWARD, or a
            re-encoded target would be easier than the one it came from"
    (prop/for-all [bs (gen/vector (gen/choose 0 255) 1 32)]
                  (let [v (bn/from-bytes-be bs)]
                    (bn/le (nk/compact->target (nk/target->compact v)) v)))))

;; ============================================================
;; Cumulative work
;; ============================================================

(deftest calc-work-is-the-inverse-of-the-target
  (testing "floor(2^256 / (target+1)) -- a harder target is more work"
    (let [w-easy (nk/calc-work 0x207fffff)   ; ~2^255
          w-main (nk/calc-work 0x1d00ffff)   ; mainnet genesis, ~2^224
          w-hard (nk/calc-work 0x1b0404cb)]  ; a 2011-era mainnet target
      (is (bn/lt w-easy w-main))
      (is (bn/lt w-main w-hard))
      ;; Mainnet difficulty 1 is exactly 2^32 hashes of expected work, the
      ;; number the whole difficulty scale is defined against.
      (is (= 4295032833 (bn/to-int w-main))))))

(deftest work-of-an-invalid-target-is-zero
  (testing "btcd returns 0 rather than dividing by zero or by a negative"
    (is (= bn/zero (nk/calc-work 0)))
    (is (= bn/zero (nk/calc-work 0x00800000)))))

(defspec work-is-monotone-in-difficulty 200
  (testing "if target a is no larger than target b, a is worth at least as much"
    (prop/for-all [e1 (gen/choose 4 32) m1 (gen/choose 1 0x7fffff)
                   e2 (gen/choose 4 32) m2 (gen/choose 1 0x7fffff)]
                  (let [c1 (+ (* e1 16777216) m1)
                        c2 (+ (* e2 16777216) m2)]
                    (if (bn/le (nk/compact->target c1) (nk/compact->target c2))
                      (bn/ge (nk/calc-work c1) (nk/calc-work c2))
                      true)))))

;; ============================================================
;; Difficulty retarget
;; ============================================================

(def retarget-params
  (nk/params {:pow-limit-bits 0x1d00ffff
              :blocks-per-retarget 2016
              :target-timespan 1209600}))

(defn- encoded
  "A target as it survives a round trip through the compact encoding.

  The 23-bit mantissa truncates DOWNWARD, so the retarget's output is never
  exactly `old/4` -- it is the largest representable value at or below it. The
  clamp bound therefore has to be stated in encoded terms, or the test is
  asserting something the format cannot deliver."
  [t]
  (nk/compact->target (nk/target->compact t)))

(deftest retarget-clamps-at-four-times-either-way
  (let [p retarget-params
        old 0x1b0404cb
        old-t (nk/compact->target old)]
    (testing "a span far too short cannot make the target more than 4x harder"
      (let [new-t (nk/compact->target (nk/retarget p old 0 1))]
        (is (= new-t (encoded (bn/div-small old-t 4))))
        (is (bn/lt new-t old-t))))
    (testing "a span far too long cannot make it more than 4x easier"
      (let [new-t (nk/compact->target (nk/retarget p old 0 100000000))]
        (is (= new-t (encoded (bn/mul-small old-t 4))))
        (is (bn/gt new-t old-t))))
    (testing "an exactly on-target span leaves it alone"
      (is (= old (nk/retarget p old 0 1209600))))))

(defspec retarget-stays-within-the-clamp 300
  (prop/for-all [e (gen/choose 8 28) m (gen/choose 0x008000 0x7fffff)
                 span (gen/choose 0 20000000)]
                (let [p retarget-params
                      old (+ (* e 16777216) m)
                      old-t (nk/compact->target old)
                      new-t (nk/compact->target (nk/retarget p old 0 span))
                      limit (nk/compact->target (:pow-limit-bits p))]
                  (and (bn/le new-t limit)
                       (bn/le new-t (bn/mul-small old-t 4))
                       ;; The lower bound only binds when the pow limit did not
                       ;; take over -- capping at the limit can legitimately
                       ;; land below old/4 for a target that was already easier
                       ;; than the limit allows.
                       (or (= new-t limit)
                           (bn/ge new-t (encoded (bn/div-small old-t 4))))))))

(deftest retarget-never-goes-easier-than-the-pow-limit
  (let [p retarget-params]
    (is (= (:pow-limit-bits p) (nk/retarget p (:pow-limit-bits p) 0 100000000))
        "already at the limit and running slow: capped, not relaxed further")))

(deftest the-off-by-one-is-reproduced
  (testing "btcd asks for the ancestor `interval - 1` back, so the span covers
            2015 inter-block intervals while the divisor is sized for 2016.
            Mainnet therefore targets 600.2977 s/block, not 600. This is
            consensus, and reproducing it is the point."
    (let [p retarget-params
          ;; 2015 intervals of exactly 600s is what a PERFECT miner produces
          ;; under the intended 600s target -- and the retarget still makes the
          ;; difficulty go UP, because it measured 1209000 against 1209600.
          span (* 2015 600)
          harder (nk/retarget p 0x1b0404cb 0 span)]
      (is (bn/lt (nk/compact->target harder) (nk/compact->target 0x1b0404cb))
          "a chain hitting 600s exactly is judged too fast and gets harder")
      ;; The fixed point: the spacing at which difficulty does not move.
      (let [stable (quot (:target-timespan p) (dec (:blocks-per-retarget p)))]
        ;; Read out of `p`, not written as `(quot 1209600 2015)` -- that form
        ;; was arithmetic on two literals and asserted nothing whatever about
        ;; the implementation.
        (is (= 600 stable) "600.2977 truncates to 600 in integer seconds")
        (is (>= (bn/compare (nk/compact->target (nk/retarget p 0x1b0404cb 0 (* 2015 601)))
                            (nk/compact->target 0x1b0404cb))
                0)
            "one second slower per block and difficulty stops rising")))))

;; ============================================================
;; Median time past
;; ============================================================

(defn- chain-with-times
  "A synthetic block index carrying only heights, parents and timestamps --
  everything `median-time-past` reads. No proof of work is done, because none
  is needed to test a median."
  [times]
  {:params (nk/params {})
   :blocks (into {}
                 (map-indexed (fn [i t]
                                [i {:id i :parent (when (pos? i) (dec i))
                                    :height i :header {:time t}}])
                              times))})

(deftest median-time-past-is-btcds
  (testing "11 blocks INCLUDING the node itself, and `timestamps[n/2]` after
            sorting -- integer division, deliberately not an average"
    (let [times [10 20 30 40 50 60 70 80 90 100 110 120]
          st (chain-with-times times)]
      ;; At height 11 the window is heights 1..11 = [20..120], median 70.
      (is (= 70 (nk/median-time-past (:params st) st 11)))
      ;; Near the start the window is short and EVEN, which is where btcd's
      ;; integer division visibly differs from a true median: for [10 20] it
      ;; returns 20, not 15.
      (is (= 20 (nk/median-time-past (:params st) st 1)))
      (is (= 10 (nk/median-time-past (:params st) st 0))))))

(defspec median-time-past-returns-an-element-of-its-window 300
  (prop/for-all [times (gen/vector (gen/choose 0 1000000) 1 30)]
                (let [st (chain-with-times times)
                      h (dec (count times))
                      window (take-last (min 11 (count times)) times)]
                  (some #{(nk/median-time-past (:params st) st h)} window))))

(defspec median-time-past-is-invariant-under-permutation 200
  (testing "it is a median: only the multiset of the window matters"
    (prop/for-all [times (gen/vector (gen/choose 0 1000) 11 11)
                   perm (gen/shuffle (range 11))]
                  (let [a (chain-with-times times)
                        b (chain-with-times (mapv #(nth times %) perm))]
                    (= (nk/median-time-past (:params a) a 10)
                       (nk/median-time-past (:params b) b 10))))))

;; ============================================================
;; A test chain: trivial difficulty, so mining is a handful of hashes
;; ============================================================

(def easy-params
  {:pow-limit-bits 0x207fffff
   :blocks-per-retarget 100000        ; effectively off
   :target-timespan 1209600})

(def test-genesis
  {:version 1 :prev nk/zero-hash :merkle-root nk/zero-hash
   :time 1600000000 :bits 0x207fffff :nonce 0})

(defn- tag-hex
  "A distinct opaque payload commitment. The merkle root's CONTENTS are out of
  scope, so any 32 bytes will do -- but they must DIFFER between miners, or two
  miners on the same tip would produce the same block."
  [s]
  (let [h (bn/bytes->hex (map #(mod (+ 7 (* 31 (int %))) 256) (str s)))]
    (subs (str h (apply str (repeat 64 \0))) 0 64)))

(defn- scratch
  "A bare node state used as a pure chain BUILDER. `process-header` is a pure
  function of state, so a test can construct any branch it likes without a
  simulator, a network, or a clock."
  ([] (scratch easy-params))
  ([p]
   (:state (n/init (nk/create)
                   {:peer-id :scratch :validators [:scratch]
                    :params p :genesis test-genesis
                    ;; Far in the future, so the 2-hour bound never fires while
                    ;; building. The bound itself is tested separately.
                    :now 2000000000}))))

(defn- build
  "Mine `n` headers onto `on`, returning [state headers].

  Timestamps advance `spacing` seconds per block, one by default -- enough to
  clear median-time-past without outrunning any clock. A test that wants the
  retarget to move difficulty passes a spacing far from the target rate."
  ([state on n tag] (build state on n tag 1))
  ([state on n tag spacing]
   (loop [st state, on on, i 0, acc []]
     (if (= i n)
       [st acc]
       (let [tpl (nk/template st {:on on
                                  :merkle-root (tag-hex (str tag "-" i))
                                  :time (+ (get-in st [:blocks on :header :time])
                                           spacing)})
             h (or (nk/mine tpl 1000000)
                   (throw (ex-info "toy miner exhausted" {:tpl tpl})))
             st' (:state (nk/process-header st h nil))]
         (recur st' (nk/header-id h) (inc i) (conj acc h)))))))

;; ============================================================
;; Fork choice
;; ============================================================

(deftest headers-extend-the-chain-and-commit-in-order
  (let [[st hs] (build (scratch) (:tip (scratch)) 5 "a")]
    (is (= 5 (nk/height st (:tip st))))
    (is (= (mapv nk/header-id hs) (nk/path-from st (:genesis st) (:tip st))))))

(deftest a-shorter-side-branch-does-not-win
  (testing "strictly greater work, so a tie goes to the incumbent and
            first-seen wins -- `chain.go:1257` uses `>`, never `>=`"
    (let [st0 (scratch)
          g (:tip st0)
          [st1 _] (build st0 g 3 "main")
          tip1 (:tip st1)
          [st2 side] (build st1 g 3 "side")]
      (is (= tip1 (:tip st2))
          "an equal-work competing branch must NOT displace the incumbent")
      (is (= 3 (nk/height st2 (nk/header-id (last side))))
          "but it is still indexed, ready to win if it is extended"))))

(deftest one-more-block-flips-the-tie
  (let [st0 (scratch)
        g (:tip st0)
        [st1 _] (build st0 g 3 "main")
        [st2 side] (build st1 g 4 "side")]
    (is (= (nk/header-id (last side)) (:tip st2)))))

(deftest reorg-emits-revert-then-commit
  (testing "the shape of the effect pair is the whole experiment: one `:revert`
            naming the fork point, one `:commit` of the new branch, and nothing
            describing what was undone"
    (let [st0 (scratch)
          g (:tip st0)
          [st1 main] (build st0 g 3 "main")
          [st2 side] (build st1 g 4 "side")
          ;; Deliver the side branch to a FRESH node so we observe the effects.
          fresh (scratch)
          fresh (reduce (fn [s h] (:state (nk/process-header s h nil))) fresh main)
          results (reductions (fn [acc h] (nk/process-header (:state acc) h nil))
                              {:state fresh}
                              side)
          fx (mapcat :effects (rest results))
          reverts (filter #(= :revert (n/effect-kind %)) fx)
          commits (filter #(= :commit (n/effect-kind %)) fx)]
      (is (= 1 (count reverts)) "exactly one revert, at the moment of the flip")
      (is (= (nk/header-id (last side)) (:tip (:state (last results)))))
      (is (= (:genesis fresh) (:to-vertex (n/effect-params (first reverts))))
          "and it names the fork point, which here is the genesis block")
      (is (= (mapv nk/header-id main) (:dropped (n/effect-params (first reverts))))
          "and NAMES what it dropped, ascending, exactly the tail the interpreter
           still holds. This is the field the whole revocable-commit redesign
           exists to carry, and until now no test looked at it: reverse it,
           truncate it, or return [] and every Nakamoto test still passed. The
           simulator now throws on a mismatch rather than noting it in `:trace`
           and truncating anyway.")
      (is (= 4 (count (:vertices (n/effect-params (last commits)))))
          "the commit that follows carries the whole new branch at once"))))

(deftest a-deep-reorg-costs-no-more-than-a-shallow-one
  (testing "at the header layer the undo log is EMPTY: every consensus quantity
            is a fold over the ancestor path, so a reorg of any depth is a
            pointer swap. This asserts the SHAPE of the result, which is the
            claim -- one revert, one commit, regardless of depth."
    (let [st0 (scratch)
          g (:tip st0)
          [st1 main] (build st0 g 20 "main")
          fork (nk/header-id (nth main 1))               ; height 2
          [st2 side] (build st1 fork 25 "side")
          fresh (reduce (fn [s h] (:state (nk/process-header s h nil)))
                        (scratch) main)
          r (reduce (fn [acc h]
                      (let [res (nk/process-header (:state acc) h nil)]
                        {:state (:state res)
                         :effects (into (:effects acc) (:effects res))}))
                    {:state fresh :effects []}
                    side)
          fx (:effects r)]
      (is (= (nk/header-id (last side)) (:tip (:state r))))
      (is (= 1 (count (filter #(= :revert (n/effect-kind %)) fx)))
          "one revert for an 18-block detach")
      (is (= fork (-> (filter #(= :revert (n/effect-kind %)) fx)
                      first n/effect-params :to-vertex)))
      (is (= (mapv nk/header-id (drop 2 main))
             (-> (filter #(= :revert (n/effect-kind %)) fx)
                 first n/effect-params :dropped))
          "18 blocks named in ascending order -- the order the interpreter's
           committed vector is in, which is the INVERSE of btcd's descending
           detach list, because btcd has to undo them one at a time and we do
           not")
      (is (= 27 (nk/height (:state r) (:tip (:state r))))))))

(deftest heaviest-beats-longest
  (testing "Bitcoin has no height tie-break anywhere: a SHORTER branch carrying
            more cumulative work wins, and it wins even when it arrives second.

            Arranged with the retarget itself. One branch is mined a second
            apart, so every retarget clamps at 1/4 and the difficulty climbs;
            the other is mined a day apart, so it relaxes back to the pow limit.
            Three hard blocks then outweigh four easy ones."
    (let [p {:pow-limit-bits 0x207fffff
             :blocks-per-retarget 2
             :target-timespan 1200}
          st0 (scratch p)
          g (:tip st0)
          [st1 base] (build st0 g 2 "base" 1)
          base-tip (nk/header-id (last base))
          [st2 slow-branch] (build st1 base-tip 4 "slow" 86400)
          [st3 fast-branch] (build st2 base-tip 3 "fast" 1)
          id-of #(nk/header-id (last %))
          w-slow (:work-sum (nk/blk st3 (id-of slow-branch)))
          w-fast (:work-sum (nk/blk st3 (id-of fast-branch)))]
      (is (< (count fast-branch) (count slow-branch))
          "the winner really is the shorter chain")
      (is (bn/gt w-fast w-slow)
          "and it really does carry more work")
      (is (= (id-of fast-branch) (:tip st3))
          "so it is the tip, despite being three blocks against four")
      (testing "and the difficulty moved in opposite directions, which is what
                made the two branches differ at all"
        (is (bn/lt (nk/compact->target (:bits (last fast-branch)))
                   (nk/compact->target (:bits (first fast-branch))))
            "the target shrank along the fast branch")
        (is (= (:pow-limit-bits p) (:bits (last slow-branch)))
            "and the slow branch has relaxed all the way back to the limit")))))

;; ============================================================
;; What the core protocol looks like from here
;;
;; These two tests exist to PIN findings, not to check Bitcoin. They are the
;; evidence behind the friction notes in the namespace docstring, so that if
;; someone later changes the protocol to fix either one, a test says so.
;; ============================================================

(deftest nothing-is-gated-behind-the-durable-write
  (testing "the durability rule -- gate exactly the messages that constitute
            this node's binding commitment -- has an EMPTY left-hand side under
            proof of work. A node signs nothing, a header is self-authenticating
            and carries its own proof, and there is no equivocation to prevent,
            so relaying before the write lands is safe. Nakamoto is the
            algorithm that shows `:persist-then`'s barrier is optional."
    (let [st (scratch)
          h (nk/mine (nk/template st {:merkle-root (tag-hex "d")}) 1000000)
          fx (:effects (nk/process-header st h nil))
          persists (filter #(= :persist-then (n/effect-kind %)) fx)]
      (is (= 1 (count persists)))
      (is (empty? (:then (n/effect-params (first persists))))
          "nothing waits on the write")
      (is (some #(= :broadcast (n/effect-kind %)) fx)
          "and the relay goes out immediately, not from inside :then"))))

(deftest a-reorg-reoccupies-positions-in-the-committed-prefix
  (testing "the finding section 12 recorded, now that `:commit` has no `:index`
            to record it in.

            The old form of this test read `:index` off the commit effects and
            asserted the sequence was not monotone. That was the only place the
            field was ever read, and asserting non-monotonicity of a value
            defined as `a globally increasing consensus index` is a test that
            documents an incoherence rather than a behaviour. The BEHAVIOUR is
            still real and still worth pinning: a reorg gives back positions in
            the committed prefix and then refills them with different vertices.

            Here main reaches height 5 and a heavier side branch forks at height
            2. The revert hands back three positions; the commit that follows
            supplies six. Positions 3, 4 and 5 are occupied twice in one run, by
            different blocks -- which is precisely why no monotone counter could
            have described this."
    (let [st0 (scratch)
          g (:tip st0)
          [st1 main] (build st0 g 5 "main")
          [_ side] (build st1 (nk/header-id (nth main 1)) 6 "side")
          fresh (reduce (fn [s h] (:state (nk/process-header s h nil))) (scratch) main)
          r (reduce (fn [acc h]
                      (let [res (nk/process-header (:state acc) h nil)]
                        {:state (:state res) :effects (into (:effects acc) (:effects res))}))
                    {:state fresh :effects []}
                    side)
          params (fn [k] (->> (:effects r)
                              (filter #(= k (n/effect-kind %)))
                              (map n/effect-params)))
          dropped (:dropped (first (params :revert)))
          attached (mapcat :vertices (params :commit))]
      (is (= 1 (count (params :revert))) "one revert, at the flip")
      (is (= (mapv nk/header-id (drop 2 main)) dropped)
          "three positions handed back, named exactly")
      (is (= (mapv nk/header-id side) attached)
          "and six supplied in their place")
      (is (< (count dropped) (count attached))
          "the prefix is longer afterwards, but it passed back THROUGH those
           positions to get there"))))

(defspec cumulative-work-never-decreases-along-a-chain 50
  (prop/for-all [n (gen/choose 1 8)]
                (let [[st hs] (build (scratch) (:tip (scratch)) n "w")
                      ws (map #(:work-sum (nk/blk st (nk/header-id %))) hs)]
                  (every? (fn [[a b]] (bn/gt b a)) (partition 2 1 ws)))))

;; ============================================================
;; Validation
;; ============================================================

(deftest a-header-that-does-not-meet-its-target-is-rejected
  (let [st (scratch)
        tpl (nk/template st {:merkle-root (tag-hex "x")})
        solved (nk/mine tpl 1000000)
        broken (assoc solved :nonce (inc (:nonce solved)))]
    (is (nk/pow-valid? solved))
    ;; A different nonce is overwhelmingly unlikely to also solve it, but at
    ;; this trivial difficulty it can, so search for one that does not.
    (let [bad (first (remove nk/pow-valid?
                             (map #(assoc solved :nonce %) (range 100000 100100))))
          r (nk/process-header st bad nil)]
      (is (some? bad))
      (is (nil? (nk/blk (:state r) (nk/header-id bad))))
      (is (= 1 (get-in (:state r) [:rejected :high-hash]))))))

(deftest a-header-claiming-the-wrong-difficulty-is-rejected
  (let [st (scratch)
        tpl (assoc (nk/template st {}) :bits 0x1f00ffff)
        solved (nk/mine tpl 1000000)
        r (nk/process-header st solved nil)]
    (is (= 1 (get-in (:state r) [:rejected :unexpected-difficulty])))))

(deftest a-header-at-or-before-the-median-time-past-is-rejected
  (testing "`!header.Timestamp.After(medianTime)` -- equality is rejected too"
    (let [[st _] (build (scratch) (:tip (scratch)) 12 "t")
          mtp (nk/median-time-past (:params st) st (:tip st))
          tpl (assoc (nk/template st {:merkle-root (tag-hex "late")}) :time mtp)
          solved (nk/mine tpl 1000000)
          r (nk/process-header st solved nil)]
      (is (= 1 (get-in (:state r) [:rejected :time-too-old]))))))

(deftest a-header-too-far-in-the-future-is-rejected
  (testing "`now` is a parameter of the check, never a clock read"
    (let [st (assoc (scratch) :now 1600000000)
          p (:params st)
          tpl (assoc (nk/template st {:merkle-root (tag-hex "f")})
                     :time (+ 1600000000 (:max-future-drift p) 1))
          solved (nk/mine tpl 1000000)]
      (is (= :time-too-new (nk/check-header-sanity p solved 1600000000)))
      (is (nil? (nk/check-header-sanity p solved (+ 1600000000 10000)))
          "the same header is fine to a node whose clock has caught up"))))

(deftest a-malformed-header-is-rejected-without-crashing-the-machine
  (testing "open membership means anyone may send anything. btcd gets field
            shapes for free from Go's types and its wire decoder; here a
            timestamp that is not a uint32, or a parent hash that is not 64 hex
            characters, would throw while SERIALIZING -- inside a pure state
            machine, taking the node down. So it is checked before the hash."
    (let [st (scratch)
          good (nk/mine (nk/template st {:merkle-root (tag-hex "m")}) 1000000)]
      (is (nk/well-formed? good))
      (doseq [bad [(assoc good :time -1)
                   (assoc good :nonce 4294967296)
                   (assoc good :time 1.5)
                   ;; These three used to THROW rather than return false, on the
                   ;; JVM only: `u32?` tested integrality with `(long n)` before
                   ;; checking the range, and `long` is a CHECKED cast --
                   ;; `(long 1e30)` raises "Value out of range for long". So the
                   ;; predicate written to keep an adversarial header from
                   ;; killing the node was itself the thing that killed it, from
                   ;; the first line of `process-header`. cljs `long` truncates,
                   ;; so the same header was merely rejected there: a platform
                   ;; split as well as a crash.
                   (assoc good :time 1e30)
                   (assoc good :time ##Inf)
                   (assoc good :time ##NaN)
                   (assoc good :nonce 99999999999999999999N)
                   (assoc good :prev "not-a-hash")
                   (assoc good :prev (subs nk/zero-hash 1))
                   (assoc good :merkle-root (str "ZZ" (subs nk/zero-hash 2)))
                   (dissoc good :bits)]]
        (is (not (nk/well-formed? bad)) (pr-str bad))
        (let [r (nk/process-header st bad :peer)]
          (is (= 1 (get-in (:state r) [:rejected :malformed])))
          (is (= [:log] (map n/effect-kind (:effects r)))))))))

(deftest a-future-dated-header-is-rejected-through-the-node-not-just-the-predicate
  (testing "`check-header-sanity` was tested directly with a literal `now`, so
            the one thing that could actually be wrong -- that `connect-one`
            passes `(:now state)` and not the genesis time, or the header's own
            time -- was untested. `:time-too-new` was the only rejection reason
            that never appeared as a `:rejected` key in any assertion."
    (let [st (assoc (scratch) :now 1600000000)
          p (:params st)
          tpl (assoc (nk/template st {:merkle-root (tag-hex "fut")})
                     :time (+ 1600000000 (:max-future-drift p) 1))
          solved (nk/mine tpl 1000000)
          r (nk/process-header st solved :peer)]
      (is (= 1 (get-in (:state r) [:rejected :time-too-new])))
      (is (nil? (nk/blk (:state r) (nk/header-id solved))))
      ;; The same header, to a node whose clock has caught up, is fine -- which
      ;; is what pins that the check reads the NODE's clock.
      (let [later (assoc st :now (+ 1600000000 100000))
            r2 (nk/process-header later solved :peer)]
        (is (nil? (get-in (:state r2) [:rejected :time-too-new])))
        (is (some? (nk/blk (:state r2) (nk/header-id solved))))))))

(deftest a-full-orphan-pool-evicts-the-oldest-rather-than-refusing-the-newest
  (testing "btcd expires orphans after an hour and, when full, EVICTS to make
            room (`chain.go:298-340`). Refusing the newest instead -- which this
            did -- is strictly more grief-able: 256 junk headers naming parents
            that will never arrive wedged the pool permanently, after which every
            legitimate out-of-order header was dropped.

            The junk here is 300 headers whose parents do not exist. The real
            branch is delivered last, child-first, and must still land."
    (let [st0 (scratch)
          [_ real] (build st0 (:tip st0) 3 "late")
          ;; 300 orphans, each naming a parent nobody will ever produce.
          junk (for [i (range 300)]
                 (let [tpl (nk/template st0 {:merkle-root (tag-hex (str "junk-" i))})]
                   (assoc tpl :prev (tag-hex (str "ghost-" i)) :nonce i)))
          flooded (reduce (fn [s h] (:state (nk/process-header s h :peer))) st0 junk)
          n-held (reduce + 0 (map count (vals (:orphans flooded))))]
      (is (<= n-held 256) "the pool stays bounded")
      (is (pos? n-held))
      ;; Child first, then its parents: every one of these arrives as an orphan.
      (let [after (reduce (fn [s h] (:state (nk/process-header s h :peer)))
                          flooded
                          (reverse real))]
        (is (= (nk/header-id (last real)) (:tip after))
            "a legitimate branch delivered out of order still connects through a
             pool full of junk -- with the old refuse-when-full policy the child
             was dropped on arrival and the chain never extended")
        (is (= 3 (nk/height after (:tip after))))))))

(deftest an-expired-orphan-is-swept
  (testing "the other half of btcd's policy: orphans older than an hour go,
            whether or not the pool is full."
    (let [st0 (scratch)
          [_ hs] (build st0 (:tip st0) 2 "exp")
          orphaned (:state (nk/process-header st0 (second hs) :peer))
          held (reduce + 0 (map count (vals (:orphans orphaned))))
          ;; Advance the node's clock past the expiry, then admit one more.
          aged (update orphaned :now + 7200)
          tpl (nk/template st0 {:merkle-root (tag-hex "another")})
          another (nk/mine (assoc tpl :prev (tag-hex "ghost")) 1000000)
          swept (:state (nk/process-header aged another :peer))]
      (is (= 1 held))
      (is (= 1 (reduce + 0 (map count (vals (:orphans swept)))))
          "the aged orphan was swept as the new one was admitted")
      (is (= #{(nk/header-id another)} (set (keys (:orphan-at swept))))))))

(deftest a-header-with-an-unknown-parent-is-parked-not-rejected
  (let [st0 (scratch)
        [_ hs] (build st0 (:tip st0) 3 "o")
        ;; Deliver the third header first: its parent is unknown.
        r (nk/process-header st0 (nth hs 2) :peer)]
    (is (nil? (nk/blk (:state r) (nk/header-id (nth hs 2)))))
    (is (= 1 (count (get-in (:state r) [:orphans (:prev (nth hs 2))]))))
    (is (= [:send] (map n/effect-kind (:effects r)))
        "and the missing parent is requested from whoever sent it")))

(deftest orphans-drain-in-a-fixpoint-when-the-parent-arrives
  (testing "connecting one orphan can unlock the next, so a whole branch
            delivered backwards still lands"
    (let [st0 (scratch)
          [_ hs] (build st0 (:tip st0) 5 "o")
          parked (reduce (fn [s h] (:state (nk/process-header s h :peer)))
                         st0
                         (reverse (rest hs)))
          r (nk/process-header parked (first hs) :peer)]
      (is (= 5 (nk/height (:state r) (:tip (:state r)))))
      (is (empty? (:orphans (:state r)))))))

;; ============================================================
;; In the simulator
;; ============================================================

(def peers [:m1 :m2 :m3])

(defn- fresh-sim [& [cfg]]
  (sim/make {:seed 7
             :nodes (zipmap peers (repeat (nk/create)))
             :node-config (zipmap peers (repeat {:params easy-params
                                                 :genesis test-genesis
                                                 :now 2000000000}))
             :config (or cfg {})}))

(defn- deliver-headers [s peer headers]
  (reduce (fn [s h] (sim/inject s peer (n/vertex-received h))) s headers))

(deftest a-mined-chain-propagates-and-everyone-commits-it
  (let [[_ hs] (build (scratch) (:tip (scratch)) 6 "p")
        s (-> (fresh-sim)
              (deliver-headers :m1 hs)
              (sim/run 40))]
    (is (sim/agreement? s))
    (is (every? #(= (mapv nk/header-id hs) (vec %))
                (vals (sim/all-committed s)))
        "all three nodes committed the same six blocks, in order")))

(deftest headers-delivered-out-of-order-still-converge
  (testing "gossip does not promise order; the orphan pool plus the get-header
            request has to close the gap"
    (let [[_ hs] (build (scratch) (:tip (scratch)) 6 "u")
          s (-> (fresh-sim)
                (deliver-headers :m1 (reverse hs))
                (sim/run 60))]
      (is (sim/agreement? s))
      (is (every? #(= 6 (count %)) (vals (sim/all-committed s)))))))

(deftest a-partition-forks-the-chain-and-healing-reorgs-it
  (testing "the end-to-end deep-reorg case, in the simulator: two halves mine
            independently, and on healing the lighter branch is reverted"
    (let [st0 (scratch)
          g (:tip st0)
          [st1 common] (build st0 g 3 "common")
          common-tip (nk/header-id (last common))
          [st2 branch-a] (build st1 common-tip 2 "A")
          [st3 branch-b] (build st2 common-tip 6 "B")
          s (-> (fresh-sim)
                (deliver-headers :m1 common)
                (sim/run 10)
                (sim/partition-network [#{:m1} #{:m2 :m3}])
                (deliver-headers :m1 branch-a)
                (deliver-headers :m2 branch-b)
                (sim/run 20))]
      (is (= (nk/header-id (last branch-a)) (:tip (sim/node-state s :m1))))
      (is (= (nk/header-id (last branch-b)) (:tip (sim/node-state s :m2))))
      (is (not (sim/agreement? s)) "while partitioned the two halves disagree")
      (let [healed (-> s sim/heal (sim/run 80))]
        (is (sim/agreement? healed) "and after healing they do not")
        (is (every? #(= (nk/header-id (last branch-b)) (:tip (sim/node-state healed %)))
                    peers))
        (is (every? #(= (into (mapv nk/header-id common)
                              (mapv nk/header-id branch-b))
                        (vec %))
                    (vals (sim/all-committed healed)))
            "m1's committed prefix no longer contains branch A at all")
        (is (seq (get-in healed [:reverted :m1])))))))

(deftest committed-work-never-goes-backwards
  (testing "a node may revert blocks, but never to a lighter chain: the tip's
            cumulative work is monotone over the whole run"
    (let [st0 (scratch)
          g (:tip st0)
          [st1 a] (build st0 g 4 "a")
          [st2 b] (build st1 g 7 "b")
          [st3 c] (build st2 (nk/header-id (nth b 2)) 8 "c")
          all (concat a b c)
          works (loop [s (fresh-sim), hs all, acc []]
                  (if (empty? hs)
                    acc
                    (let [s' (sim/run (sim/inject s :m1 (n/vertex-received (first hs))) 1)
                          st (sim/node-state s' :m1)]
                      (recur s' (rest hs) (conj acc (nk/tip-work st))))))]
      (is (every? (fn [[x y]] (bn/ge y x)) (partition 2 1 works))))))

(defn- mine-on-node
  "Mine one block on whatever `peer` currently believes the tip is, and inject
  it into that peer -- the seam a real miner would use. Everything the miner
  needs is a pure query on the node's own state; it gets no privileged access."
  [s peer tag]
  (let [st (sim/node-state s peer)
        tpl (nk/template st {:merkle-root (tag-hex tag)})
        h (nk/mine tpl 1000000)]
    (sim/inject s peer (n/vertex-received h))))

(deftest an-equal-work-tie-is-not-resolved-by-the-protocol
  (testing "two branches of exactly equal work leave two nodes on different
            tips, permanently, because each keeps whichever it saw FIRST.

            This is not a bug and not a liveness failure -- it is what `>`
            rather than `>=` means, and Bitcoin has no tie-break to fall back
            on. The split persists until somebody mines on top of one of them.
            Any test that expects competing miners to converge without a
            subsequent block is asserting something Nakamoto does not promise."
    (let [st0 (scratch)
          g (:tip st0)
          [st1 x] (build st0 g 2 "X")
          [st2 y] (build st1 g 2 "Y")
          s (-> (fresh-sim)
                (deliver-headers :m1 x)
                (deliver-headers :m1 y)
                (deliver-headers :m2 y)
                (deliver-headers :m2 x)
                (sim/run 60))]
      (is (= (nk/header-id (last x)) (:tip (sim/node-state s :m1))))
      (is (= (nk/header-id (last y)) (:tip (sim/node-state s :m2))))
      (is (not (sim/agreement? s)))
      (testing "and one more block on either branch ends it immediately"
        (let [[_ z] (build st2 (nk/header-id (last y)) 1 "Z")
              healed (-> s (sim/inject :m1 (n/vertex-received (first z))) (sim/run 60))]
          (is (sim/agreement? healed))
          (is (apply = (map #(:tip (sim/node-state healed %)) peers))))))))

(defspec competing-miners-converge 15
  (testing "two miners racing on the same network, with delivery order drawn
            from the seed. They repeatedly find blocks on top of different tips,
            so this exercises reorgs rather than merely fork choice.

            The race ends with one uncontested block, because an equal-work tie
            is genuinely unresolved until someone extends one side -- see
            `an-equal-work-tie-is-not-resolved-by-the-protocol`."
    (prop/for-all [seed (gen/choose 1 100000)
                   gaps (gen/vector (gen/choose 1 4) 12 12)]
                  (let [s (reduce (fn [s [i gap]]
                                    (-> s
                                        (mine-on-node (if (even? i) :m1 :m2)
                                                      (str "r" i))
                                        (sim/run gap)))
                                  (sim/make {:seed seed
                                             :nodes (zipmap peers (repeat (nk/create)))
                                             :node-config (zipmap peers (repeat {:params easy-params
                                                                                 :genesis test-genesis
                                                                                 :now 2000000000}))})
                                  (map-indexed vector gaps))
                        s (-> (sim/run s 60) (mine-on-node :m1 "final") (sim/run 120))
                        tips (map #(:tip (sim/node-state s %)) peers)
                        committed (vals (sim/all-committed s))]
                    (and (sim/agreement? s)
                         (apply = tips)
                         (apply = committed)
                         ;; and the committed sequence really is the chain
                         (= (first committed)
                            (nk/path-from (sim/node-state s :m1)
                                          (:genesis (sim/node-state s :m1))
                                          (first tips))))))))

(deftest nakamoto-is-deterministic
  (let [[_ hs] (build (scratch) (:tip (scratch)) 5 "d")
        run-it #(-> (fresh-sim {:drop-rate 0.2})
                    (deliver-headers :m1 hs)
                    (sim/run 60))
        x (run-it), y (run-it)]
    (is (= (sim/all-committed x) (sim/all-committed y)))
    (is (= (:trace x) (:trace y)))))

(defspec converges-across-seeds 20
  (testing "convergence is not an artifact of one lucky schedule"
    (let [[_ hs] (build (scratch) (:tip (scratch)) 4 "s")]
      (prop/for-all [seed (gen/choose 1 10000)]
                    (let [s (-> (sim/make {:seed seed
                                           :nodes (zipmap peers (repeat (nk/create)))
                                           :node-config (zipmap peers (repeat {:params easy-params
                                                                               :genesis test-genesis
                                                                               :now 2000000000}))})
                                (deliver-headers :m1 hs)
                                (sim/run 60))]
                      (and (sim/agreement? s)
                           (every? #(= 4 (count (sim/committed s %))) peers)))))))

;; ============================================================
;; Durability
;; ============================================================

(deftest a-restarted-node-rebuilds-its-chain-from-durable-headers
  (testing "nothing is gated behind the write -- a header is
            self-authenticating -- but the headers are still persisted, and a
            restart must not lose the chain"
    (let [[_ hs] (build (scratch) (:tip (scratch)) 5 "r")
          s (-> (fresh-sim)
                (deliver-headers :m1 hs)
                (sim/run 20))
          before (:tip (sim/node-state s :m1))
          s' (-> s (sim/crash :m1) (sim/restart :m1) (sim/run 5))]
      (is (= before (:tip (sim/node-state s' :m1))))
      (is (= (mapv nk/header-id hs) (vec (sim/committed s' :m1)))
          "and it re-announces the same committed prefix, not a duplicate of it"))))

;; ============================================================
;; The clock across a restart
;; ============================================================

(deftest a-restarted-node-can-extend-the-chain-it-restored
  (testing "LIVENESS. `:now` defaults to the GENESIS timestamp and `restore`
            never touched it, so a restarted node came back with a clock
            reading from the beginning of the chain while its restored tip was
            far ahead. Every subsequent header then failed the two-hour future
            bound as `:time-too-new`: the node had rebuilt its chain perfectly
            and could not extend it.

            btcd never derives its clock from a header -- the bound comes from
            `timeSource.AdjustedTime()` (validate.go:495-521), which survives a
            restart because it was never in the chain.

            Every existing test hid this by passing `:now 2000000000`, a
            constant far in the future, INCLUDING the restart test above. This
            one deliberately does not."
    (let [;; A chain whose timestamps run well past the default clock.
          [built hs] (build (scratch) (:tip (scratch)) 8 "clock" 600)
          writes (mapv (fn [h] {:writes {[:header (nk/header-id h)] h}
                                :durable? true})
                       hs)
          ;; Restart with NO `:now` in config: the only clock available is what
          ;; the restored chain itself proves has already happened.
          {st :state} (n/init (nk/create) {:peer-id :a :validators [:a]
                                           :params easy-params
                                           :genesis test-genesis
                                           :restored {:durable {} :writes writes}})
          tip-time (get-in st [:blocks (:tip st) :header :time])]
      (is (= (nk/header-id (last hs)) (:tip st)) "the chain came back")
      (is (>= (:now st) tip-time)
          "and the clock is at least as late as the tip it restored")
      ;; The next header on that chain must now be acceptable.
      (let [[_ more] (build built (:tip built) 1 "next" 600)
            nxt (first more)
            {st' :state} (n/step (nk/create) st (n/vertex-received nxt))]
        (is (= (nk/header-id nxt) (:tip st'))
            "so the restored chain can actually be extended")))))

(deftest an-orphan-must-pass-the-context-free-checks-before-it-is-parked
  (testing "btcd runs `checkBlockSanity` BEFORE the orphan path; this did not

           `check-header-sanity` was only reached inside `connect-one`, i.e.
           only once the parent was known. So the orphan pool accepted headers
           on SHAPE alone: valid field types, a random `:prev`, and any nonce
           at all. No hashing required.

           That is the cheapest possible input on an open network, and the pool
           evicts FIFO at 256, so a stream of free junk keeps it permanently
           full and every legitimate out-of-order header is evicted on arrival.
           Each junk header also elicits a `:get-header` reply.

           Every check in `check-header-sanity` is context-free -- params and a
           clock, never the parent -- so a missing parent is no reason to skip
           any of them."
    (let [st (scratch)
          ;; Claims a difficulty far harder than its hash meets. Nothing about
          ;; a missing parent prevents noticing that.
          liar (assoc (nk/template st {:merkle-root (tag-hex "liar")})
                      :prev (tag-hex "ghost")
                      :bits 0x1d00ffff
                      :nonce 1)
          r (nk/process-header st liar :peer)]
      (is (zero? (reduce + 0 (map count (vals (:orphans (:state r))))))
          "not parked")
      (is (empty? (filter #(= :send (n/effect-kind %)) (:effects r)))
          "and no `:get-header` reply, so it is not an amplifier either")))

  (testing "the limit of what one header can prove, stated rather than implied

           `pow-valid?` checks the hash against the difficulty the header
           CLAIMS, and the sender chooses that. `target-valid?` is what stops
           them claiming an arbitrarily easy one -- so the floor is the params'
           pow limit, not the chain's real difficulty. At this fixture's
           regtest-grade limit that floor is low, which is precisely why the
           junk in the flood test above still parks."
    (let [st (scratch)
          easy (assoc (nk/template st {:merkle-root (tag-hex "easy")})
                      :prev (tag-hex "ghost2")
                      :bits 0x2100ffff          ; easier than the pow limit
                      :nonce 1)]
      (is (some? (nk/check-header-sanity (:params st) easy (:now st)))
          "a header claiming an easier target than the params allow is refused
           by `target-valid?`, which is the half that does not depend on how
           much work the sender actually did"))))

;; ============================================================
;; Snapshotting the header log
;; ============================================================

(deftest the-header-log-is-collapsed-instead-of-replayed-forever
  (testing "one record per header means restart cost grows with the age of the
            chain. A snapshot stands in for every header before it.

           What this does NOT do is bound memory: the index still holds every
           header. That is deliberate. Dropping old headers caps how deep a
           reorg can be validated, which is a consensus policy rather than a
           storage decision, and Bitcoin keeps every header forever for exactly
           that reason."
    (let [n 12
          [_ hs] (build (scratch) (:tip (scratch)) n "snap" 600)
          ;; Feed them through a live node with a short interval.
          st0 (:state (n/init (nk/create)
                              {:peer-id :a :validators [:a] :params easy-params
                               :genesis test-genesis :now 2000000000
                               :snapshot-interval 5}))
          [st records]
          (reduce (fn [[st acc] h]
                    (let [{st' :state fx :effects} (n/step (nk/create) st (n/vertex-received h))]
                      [st' (into acc (keep #(when (= :persist-then (n/effect-kind %))
                                              (n/effect-params %))
                                           fx))]))
                  [st0 []] hs)
          snaps (filter :checkpoint records)]
      (is (= n (count records)) "every header is still written")
      (is (= 2 (count snaps))
          "and at 5-header intervals over 12 headers, two of them rewrite the log")
      (let [snap (first (:checkpoint (last snaps)))
            headers (get-in snap [:writes ::nk/snapshot])
            heights (map #(get-in st [:blocks (nk/header-id %) :height]) headers)]
        (is (seq headers) "the snapshot carries headers")
        ;; A point-in-time record, so it holds what was indexed when it was
        ;; written -- not what the node holds now, which is more.
        (is (= heights (range (count headers)))
            "every height from genesis, contiguous and IN ORDER. Both halves
             matter: a gap means the snapshot does not stand in for the log it
             replaces, and wrong order means `restore` skips every header whose
             parent it has not indexed yet -- which is not an error, just a
             shorter chain, the shape of bug that survives a test suite")
        (is (contains? (set (map nk/header-id headers)) (:genesis st))
            "including genesis, without which nothing else can be indexed")
        ;; On the emitted record, not a hand-built one: the tie test below
        ;; proves restore HONOURS a carried tip, and this proves the writer
        ;; actually carries it. Each passes while the other is broken.
        (is (= (nk/header-id (nth hs (dec (* 2 5)))) (get-in snap [:writes ::nk/tip]))
            "and the snapshot names the tip as it stood when it was written")))))

(deftest a-node-restores-from-a-snapshot-alone
  (testing "the round trip that makes the snapshot worth writing. Restoring
            from ONLY the snapshot record must reach the same tip as replaying
            every individual header -- including the tip itself, which is
            carried rather than re-derived because equal-work candidates are
            resolved by arrival order and a snapshot is in height order."
    (let [[_ hs] (build (scratch) (:tip (scratch)) 10 "round" 600)
          per-header (mapv (fn [h] {:writes {[:header (nk/header-id h)] h}
                                    :durable? true})
                           hs)
          init-from (fn [writes]
                      (:state (n/init (nk/create)
                                      {:peer-id :a :validators [:a]
                                       :params easy-params :genesis test-genesis
                                       :restored {:durable {} :writes writes}})))
          full (init-from per-header)
          ;; The same chain, as one record.
          snap [{:writes {::nk/snapshot (->> (vals (:blocks full))
                                             (sort-by :height)
                                             (mapv :header))
                          ::nk/tip (:tip full)}
                 :durable? true}]
          collapsed (init-from snap)]
      (is (= (:tip full) (:tip collapsed)) "same tip from one record as from ten")
      (is (= (set (keys (:blocks full))) (set (keys (:blocks collapsed))))
          "and the same index")
      (is (= 1 (count snap)) "from a log that is one record instead of ten"))))

(deftest the-snapshot-carries-the-tip-because-equal-work-is-decided-by-order
  (testing "the one thing a snapshot cannot re-derive.

           `restore` adopts the first block to reach the highest work --
           `bn/gt` is strict, so among EQUAL-work candidates the replay order
           decides. That is correct for a log, which is in arrival order and
           therefore reproduces first-seen. A snapshot is in HEIGHT order, and
           two branches of the same length have the same work at every height,
           so which one it lists first is an artifact of how the index happened
           to iterate.

           Re-deriving the tip from a snapshot therefore lets a node come back
           on a different branch than the one it was on -- a fork caused by
           restarting, with no message and no fault. So the tip is carried.

           Constructed rather than generated: a single chain has no ties, which
           is why removing `::tip` passes every other test here."
    (let [base (scratch)
          fork (:tip base)
          [afterA branch-a] (build base fork 4 "branch-a" 600)
          [_ branch-b] (build afterA fork 4 "branch-b" 600)
          ;; A node that saw branch A first stays on it: B ties, and a tie does
          ;; not move the tip.
          live (reduce (fn [st h] (:state (n/step (nk/create) st (n/vertex-received h))))
                       (scratch)
                       (concat branch-a branch-b))
          tip-a (nk/header-id (last branch-a))
          genesis-h (get-in live [:blocks (:genesis live) :header])
          ;; A snapshot that lists B before A at every height -- exactly what
          ;; height-ordering may produce, and the opposite of arrival order.
          interleaved (vec (cons genesis-h
                                 (mapcat (fn [b a] [b a]) branch-b branch-a)))
          restore-from (fn [writes]
                         (:state (n/init (nk/create)
                                         {:peer-id :a :validators [:a]
                                          :params easy-params :genesis test-genesis
                                          :now 2000000000
                                          :restored {:durable {} :writes writes}})))]
      (is (= tip-a (:tip live))
          "the live node is on branch A -- it saw it first and B only tied")
      (is (= tip-a (:tip (restore-from
                          [{:writes {::nk/snapshot interleaved ::nk/tip tip-a}}])))
          "and it comes back on branch A, because the snapshot says so")
      (is (not= tip-a (:tip (restore-from [{:writes {::nk/snapshot interleaved}}])))
          "whereas re-deriving from the same headers picks branch B. This is
           the assertion that fails if `::tip` stops being carried -- and it
           needs a tie to exist at all, which no other test here has"))))

(deftest recovery-to-genesis-resynchronizes-the-consumer
  (let [{:keys [effects]} (n/init (nk/create) {:peer-id :a :genesis test-genesis
                                               :params easy-params :restored {:writes []}})
        resets (filter #(= :resync (n/effect-kind %)) effects)]
    (is (= [[]] (mapv #(:vertices (n/effect-params %)) resets)))))

(deftest a-runtime-clock-event-carries-real-seconds
  (let [node (nk/create)
        st (:state (n/init node {:peer-id :a :params easy-params :genesis test-genesis
                                 :unix-time 2000000000}))
        tick (assoc (n/timer-fired :clock) :unix-time 2000000001)]
    (is (= 2000000001 (:now (:state (n/step node st tick)))))))

(deftest a-repeated-orphan-keeps-its-arrival-order
  (let [st (scratch)
        [_ [_ child]] (build st (:tip st) 2 :orphan)
        parked (:state (nk/process-header st child :b))
        repeat-result (nk/process-header parked (assoc child :transport-tag 1) :b)]
    (is (= parked (:state repeat-result)))
    (is (= [:send] (map n/effect-kind (:effects repeat-result))))))
