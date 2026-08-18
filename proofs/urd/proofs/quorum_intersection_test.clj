(ns urd.proofs.quorum-intersection-test
  "The verified thresholds and the shipped ones cannot drift apart.

  Same argument as `may-sign-test`: loading the proof namespace checks the
  theorem, but the code urd actually runs is a separate hand-written copy in
  `urd.consensus.node`. Compare them."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.node :as node]
            [urd.proofs.quorum-intersection :as proof]))

(deftest the-shipped-thresholds-are-the-verified-ones
  (testing "byzantine-threshold and byzantine-tolerance, against the
            definitions the theorem is stated over.

            The theorem is over all Nat and this walks a prefix, so it cannot
            be a substitute for it -- it is a bridge. What it catches is the
            failure the proof CANNOT catch: the shipped copy being edited
            while the verified original is not. Every residue mod 3 and both
            parities appear many times in this range."
    (doseq [n (concat (range 1 400)
                      ;; and a scatter well beyond, since a copy could diverge
                      ;; only in a branch that small n never reaches
                      [1000 1001 1002 9999 10000 10001 65535 65536 1000000])]
      (is (= (node/byzantine-threshold n) (proof/quorum n))
          (str "quorum disagrees at n=" n))
      (is (= (node/byzantine-tolerance n) (proof/tolerated n))
          (str "tolerance disagrees at n=" n)))))

(deftest the-property-holds-where-it-is-checkable
  (testing "the theorem is over all Nat; this walks a prefix of it, so that a
            change to either definition fails HERE as well as in the proof"
    (doseq [n (range 1 500)]
      (is (< (proof/tolerated n) (proof/shared n))
          (str "two quorums share no honest member at n=" n))))

  (testing "and the worked cases the docstrings quote"
    (is (= 3 (node/byzantine-threshold 4)))
    (is (= 4 (node/byzantine-threshold 5)))
    (is (= 5 (node/byzantine-threshold 7)))
    (is (= 0 (node/byzantine-tolerance 3)) "n=3 tolerates no Byzantine fault")
    (is (= 1 (node/byzantine-tolerance 4)))
    (is (= 2 (node/byzantine-tolerance 7)))))
