(ns urd.proofs.may-sign-test
  "The proof and the shipped code cannot drift apart.

  `urd.proofs.may-sign` is checked by loading it: `a/theorem` verifies at load
  time, so a broken proof is a failing require. That covers the proof.

  It does not cover the thing that actually goes wrong, which is the SHIPPED
  predicate quietly diverging from the verified one. `urd.consensus.signing`
  carries a hand-written copy of the emitted definition -- it has to, because
  ansatz is JVM-only and urd is portable -- and a copy is exactly the kind of
  thing that gets edited without its original.

  So: compare them exhaustively over a small domain. 4^6 = 4096 triples is
  enough, because the property is lexicographic order over three coordinates
  and every case class (less, equal, greater at each level) appears many times
  in 0..3.

  Runs under `clj -M:proofs` only. Ansatz is not a runtime dependency and must
  never become one."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.signing :as signing]
            [urd.proofs.may-sign :as proof]))

(deftest the-shipped-predicate-is-the-verified-one
  (testing "exhaustive over 0..3 in each of six coordinates"
    (let [dom (range 4)
          mismatches (for [hn dom rn dom sn dom hl dom rl dom sl dom
                           :let [shipped (boolean (signing/may-sign hn rn sn hl rl sl))
                                 proved  (boolean (proof/may-sign hn rn sn hl rl sl))]
                           :when (not= shipped proved)]
                       {:args [hn rn sn hl rl sl] :shipped shipped :proved proved})]
      (is (= 4096 (count (for [hn dom rn dom sn dom hl dom rl dom sl dom] 1)))
          "precondition: the domain is the size we think it is")
      (is (empty? mismatches)
          (str "shipped and verified disagree on " (count mismatches)
               " inputs, first: " (first mismatches))))))

(deftest the-property-the-proof-states
  (testing "no-double-sign, as a runnable sanity check on the same inputs the
            theorem quantifies over -- not a substitute for the proof, which is
            over all Nat, but a guard against the two drifting"
    (is (every? false?
                (for [h (range 4) r (range 4) s (range 4)]
                  (signing/may-sign h r s h r s)))))

  (testing "and the wrapper's genesis lets a validator sign at height 0"
    (is (signing/may-sign? {:height 0 :round 0 :step :propose} nil))))
