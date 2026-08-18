(ns urd.consensus.algorithms.snowtree-test
  "The Snowball Tree -- what avalanchego runs under Snowman.

  Structure is most of what is being ported here, so these tests assert on it
  directly as well as on behaviour. avalanchego's own `tree_test.go` vectors are
  literal `ids.ID` byte arrays and cannot be replayed against urd's choices, so
  the STRUCTURAL claims are ported instead: the five cases of `unaryNode.Add`,
  the collapse when a node finalizes, the lazy reset, and the one behavioural
  difference from the flat form that motivates the whole structure.

  Keys here are four hex characters -- 16 bits -- which is enough to reach every
  case and small enough to read. Bit `i` is bit `i mod 4` of hex digit `i div 4`,
  least significant first, so:

      \"0000\"  all bits zero
      \"1000\"  bit 0 set
      \"2000\"  bit 1 set
      \"2008\"  bits 1 and 15 set"
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.algorithms.snowtree :as t]
            [urd.consensus.algorithms.snowflake :as sf]))

(def params {:k 4 :alpha-preference 3 :alpha-confidence 3 :beta 2})

(defn- poll [tr votes] (t/tree-record-poll tr votes))

;; ============================================================
;; Bits
;; ============================================================

(deftest bit-order-is-least-significant-first-within-a-hex-digit
  (testing "an arbitrary but FIXED total order is all the algorithm needs; what
            it cannot survive is an inconsistent one"
    (is (= [0 0 0 0] (mapv #(t/bit-at "0000" %) (range 4))))
    (is (= [1 0 0 0] (mapv #(t/bit-at "1000" %) (range 4))))
    (is (= [0 1 0 0] (mapv #(t/bit-at "2000" %) (range 4))))
    (is (= [0 0 1 0] (mapv #(t/bit-at "4000" %) (range 4))))
    (is (= [0 0 0 1] (mapv #(t/bit-at "8000" %) (range 4))))
    (is (= 1 (t/bit-at "2008" 15)) "the last bit of the last digit")
    (is (= 16 (t/num-bits "0000")))))

(deftest subset-predicates
  (is (t/equal-subset? 0 4 "0000" "0000"))
  (is (t/equal-subset? 1 16 "0000" "1000") "differ only at bit 0")
  (is (not (t/equal-subset? 0 16 "0000" "1000")))
  (is (t/equal-subset? 3 3 "0000" "ffff") "an empty range is equal")
  (is (= 0 (t/first-difference 0 16 "0000" "1000")))
  (is (= 1 (t/first-difference 0 16 "0000" "2000")))
  (is (= 15 (t/first-difference 2 16 "2000" "2008")))
  (is (nil? (t/first-difference 1 16 "0000" "1000")) "the difference is below the range")
  (is (nil? (t/first-difference 0 16 "abcd" "abcd"))))

;; ============================================================
;; `unaryNode.Add`: the five cases
;;
;; Case 1 is "no difference in this node's range", which does not split.
;; ============================================================

(deftest add-case-1-no-difference-does-not-split
  (testing "adding a choice already in the tree is a no-op"
    (let [tr (t/tree params :x "0000")
          tr' (t/tree-add tr :x "0000")]
      (is (= (t/describe tr) (t/describe tr'))))))

(deftest add-case-3-split-on-the-first-bit-this-node-covers
  (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "1000"))
        d (t/describe tr)]
    (is (= 0 (:binary d)) "the root became a binary node on bit 0")
    (is (= [{:unary [1 16] :confidence [0] :finalized? false}
            {:unary [1 16] :confidence [0] :finalized? false}]
           (:children d))
        "both sides are fresh unary nodes covering the rest of the key")))

(deftest add-case-5-split-on-an-interior-bit
  (testing "the root keeps the bits BELOW the split and a fresh copy takes the
            bits above, which is what preserves confidence already earned on the
            undisputed prefix"
    (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "2000"))
          d (t/describe tr)]
      (is (= [0 1] (:unary d)) "the root now covers only bit 0")
      (is (= 1 (:binary (:child d))) "and its child decides bit 1"))))

(deftest add-case-2-a-node-covering-exactly-one-bit
  (let [tr (-> (t/tree params :x "0000")
               (t/tree-add :y "2000")      ; case 5: root now covers [0,1)
               (t/tree-add :z "1000"))     ; case 2: split that single bit
        d (t/describe tr)]
    (is (= 0 (:binary d)) "the root is now a binary node on bit 0")
    (is (some? (:children d)) "and it kept the subtree that was below it")))

(deftest add-case-4-split-on-the-last-bit-this-node-covers
  (let [tr (-> (t/tree params :x "0000")
               (t/tree-add :y "2000")      ; case 5
               (t/tree-add :z "2008"))     ; the "2000" branch splits at bit 15
        d (t/describe tr)]
    (is (= [0 1] (:unary d)))
    (is (= 1 (:binary (:child d))))))

(deftest a-choice-on-a-decided-branch-is-refused
  (testing "`Tree.Add` checks the new key against the SETTLED prefix first
            (`tree.go:59-65`), which is how a rejected branch stays rejected"
    (let [tr (-> (t/tree params :x "1000") (t/tree-add :y "0000") (t/tree-add :z "2000"))
          ;; Two polls for the bit-0-is-zero side decide bit 0 against :x.
          decided (-> tr (poll {:y 2 :z 2}) (poll {:y 2 :z 2}))
          ;; :w sits on :x's side of bit 0.
          after (t/tree-add decided :w "3000")]
      (is (= 1 (:binary (t/describe decided)))
          "the root collapsed to the node deciding bit 1")
      (is (= (t/describe decided) (t/describe after)))
      (is (nil? (get (:choices after) "3000"))))))

;; ============================================================
;; RecordPoll
;; ============================================================

(deftest beta-consecutive-polls-finalize-a-single-choice
  (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "ffff"))
        one (poll tr {:x 4})
        two (poll one {:x 4})]
    (is (= :x (t/tree-preference one)))
    (is (not (t/tree-finalized? one)))
    (is (t/tree-finalized? two))
    (is (= :x (t/tree-preference two)))))

(deftest alternating-polls-never-finalize
  (testing "the consecutive-poll invariant, at the trie level. Every alternation
            flips the binary node's preference, which clears its confidence
            before the increment."
    (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "ffff"))
          done (reduce (fn [tr c] (poll tr {c 4})) tr (take 20 (cycle [:x :y])))
          d (t/describe done)]
      (is (not (t/tree-finalized? done)))
      ;; `tree-finalized?` alone does NOT pin the flip: remove the clear from
      ;; `binary-record-poll` and the root reaches beta on the second poll,
      ;; finalizes, and COLLAPSES to a child that is itself unfinalized -- so
      ;; the top-level flag reads false either way and the test passes for the
      ;; mutant. The structure is what distinguishes them.
      (is (= 0 (:binary d))
          "the root must still be the bit-0 node: it never decided anything")
      (is (= [1] (:confidence d))
          "and its confidence never gets past one, because every alternation
           clears it before incrementing"))))

(deftest a-poll-below-alpha-clears-confidence
  (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "ffff"))
        built (poll tr {:x 4})
        weak (poll built {:x 2})]
    (is (= [1] (:confidence (t/describe built))))
    (is (= [0] (:confidence (t/describe weak))))
    (is (not (t/tree-finalized? weak)))))

(deftest an-unsuccessful-poll-is-lazy-and-still-clears
  (testing "`Tree.RecordUnsuccessfulPoll` only sets a flag (`tree.go:89-91`);
            the reset is handed to the nodes on the next poll. The flag has to
            actually arrive, or a failed poll would cost nothing."
    (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "ffff"))
          built (poll tr {:x 4})
          flagged (t/tree-record-unsuccessful-poll built)]
      (is (= [1] (:confidence (t/describe built))))
      (is (= [1] (:confidence (t/describe flagged)))
          "nothing has walked the tree yet")
      (is (not (t/tree-finalized? (poll flagged {:x 4})))
          "and the next poll pays for it: without the reset this would be the
           second consecutive success and beta is 2"))))

(deftest a-finalized-unary-node-collapses-to-its-child
  (testing "the UNARY collapse specifically (`tree.go:437-440`), which the
            binary case below does not reach. Disabling it left every other test
            in this file green, which is the whole reason this one exists.

            :x and :y agree on bit 0 and differ at bit 1, so the root is a unary
            node covering the settled prefix with a binary child. A 2/2 split
            gives the root all four votes -- enough -- and the child two on each
            side, which is below alpha. So the root finalizes the shared prefix
            and hands its place to the child, while the contested bit stays
            open. That is the structure earning its keep: undisputed bits are
            settled once and never polled again."
    (let [tr (-> (t/tree params :x "0000") (t/tree-add :y "2000"))]
      (is (= [0 1] (:unary (t/describe tr))) "root covers only bit 0")
      (is (= 1 (:binary (:child (t/describe tr)))))
      (let [one (poll tr {:x 2 :y 2})
            two (poll one {:x 2 :y 2})
            d (t/describe two)]
        (is (= [1] (:confidence (t/describe one))) "the root counts all four votes")
        (is (= [0] (:confidence (:child (t/describe one))))
            "while the child sees 2 a side, below alpha")
        (is (nil? (:unary d)) "the root unary node is gone")
        (is (= 1 (:binary d)) "the binary child took its place")
        (is (not (t/tree-finalized? two)) "and the contested bit is still open")))))

(deftest finalizing-collapses-the-node-and-keeps-deciding
  (testing "a decided node returns its child in its place (`tree.go:437-440`),
            so the trie shrinks from the top as bits are settled"
    (let [tr (-> (t/tree params :x "1000") (t/tree-add :y "0000") (t/tree-add :z "2000"))]
      (is (= 0 (:binary (t/describe tr))) "root decides bit 0")
      (let [decided (-> tr (poll {:y 2 :z 2}) (poll {:y 2 :z 2}))]
        (is (= 1 (:binary (t/describe decided))) "root is now the bit-1 node")
        (is (not (t/tree-finalized? decided)) "bit 1 is still open")
        (let [done (-> decided (poll {:z 4}) (poll {:z 4}))]
          (is (t/tree-finalized? done))
          (is (= :z (t/tree-preference done))))))))

;; ============================================================
;; The reason the Tree exists
;; ============================================================

(deftest sibling-votes-combine-above-the-bit-where-they-diverge
  (testing "THE behavioural difference from the flat form, and the whole point
            of the structure.

            :y and :z share bit 0; :x does not. A 2/2 split between :y and :z
            delivers FOUR votes to the not-:x side of the top binary node, and
            two such polls settle bit 0 and eliminate :x.

            The flat form sees the same evidence as a plurality of 2, which is
            below alpha-preference 3, and does nothing at all -- no preference
            move, no confidence, and :x still preferred. Same votes, same
            parameters, opposite outcome."
    (let [tr (-> (t/tree params :x "1000") (t/tree-add :y "0000") (t/tree-add :z "2000"))
          after (-> tr (poll {:y 2 :z 2}) (poll {:y 2 :z 2}))]
      (is (= [1 0 0] (mapv #(t/bit-at "1000" %) [0 1 2])) ":x is the odd one out at bit 0")
      (is (= 1 (:binary (t/describe after))) "bit 0 is settled; :x is gone")
      (is (#{:y :z} (t/tree-preference after)))

      ;; The control, on the same evidence.
      (let [flat (reduce (fn [s _] (sf/snowflake-record-poll s 2 :y))
                         (sf/snowflake params :x)
                         (range 2))]
        (is (= [0] (:confidence flat)))
        (is (= :x (:preference flat)))
        (is (not (:finalized? flat)))))))

;; ============================================================
;; The unary/binary instances
;; ============================================================

(deftest the-unary-instance-has-no-guards-and-that-is-deliberate
  (testing "`unary_snowflake.go:45-64` has neither a `finalized?` guard nor an
            alpha-preference check -- the caller does the alpha check
            (`tree.go:421-425`). Reproduced rather than tidied, because tidying
            it would move where a threshold is enforced."
    (let [sf0 (sf/unary-snowflake params)
          done (reduce (fn [s _] (sf/unary-record-poll s 4)) sf0 (range 2))]
      (is (:finalized? done))
      ;; Still accepts polls afterwards; it just cannot un-finalize.
      (is (:finalized? (sf/unary-record-poll done 0))))))

(deftest extending-a-unary-instance-carries-its-confidence
  (testing "`Extend` (`unary_snowflake.go:74-82`). A run of bits polled into
            agreement does not start from zero when a new choice splits it --
            which is the whole economy of the structure."
    (let [built (sf/unary-record-poll (sf/unary-snowflake params) 4)
          binary (sf/unary-extend built 1)]
      (is (= [1] (:confidence built)))
      (is (= [1] (:confidence binary)))
      (is (= 1 (:preference binary))))))

(deftest the-binary-instance-does-guard-both
  (let [sf0 (sf/binary-snowflake params 0)]
    (is (= [0] (:confidence (sf/binary-record-poll sf0 2 0)))
        "below alpha-preference is an unsuccessful poll")
    (let [built (sf/binary-record-poll sf0 4 0)]
      (is (= [1] (:confidence built)))
      (is (= [1] (:confidence (sf/binary-record-poll built 4 1)))
          "a flip clears confidence, then the same poll increments it")
      (is (= 1 (:preference (sf/binary-record-poll built 4 1)))))
    (let [done (reduce (fn [s _] (sf/binary-record-poll s 4 0)) sf0 (range 2))]
      (is (:finalized? done))
      (is (= 0 (:preference (sf/binary-record-poll done 4 1)))
          "finalized is absorbing here, unlike the unary form"))))
