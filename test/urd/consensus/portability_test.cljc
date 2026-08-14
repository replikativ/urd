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
