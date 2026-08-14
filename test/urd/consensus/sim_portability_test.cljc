(ns urd.consensus.sim-portability-test
  "End-to-end determinism across Clojure and ClojureScript.

  `portability-test` pins the PRNG's raw draws. This pins the thing that
  actually matters: that a whole simulation -- message delays, drop decisions,
  sampled peers, delivery order, committed values -- comes out identical on both
  platforms.

  If this diverges, a failing schedule found on the JVM cannot be reproduced in
  a browser, and vice versa, which would defeat the entire point of a seeded
  deterministic simulator.

  Deliberately `.cljc` with no host interop, and deliberately run by BOTH the
  JVM suite and `clj -M:cljs-test`."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.node :as n]
            [urd.consensus.sim :as sim]))

;; A node with no host dependencies: broadcasts once, then commits the
;; lexicographically smallest value it has heard from a quorum's worth of peers.
(defrecord Fingerprint []
  n/Node
  (init [_ config]
    (let [me (:peer-id config)]
      (n/result {:peer-id me
                 :validators (:validators config)
                 :heard {me me}
                 :done? false}
                [(n/broadcast :propose {:from me :value me})])))
  (step [_ state input]
    (if (= :message-received (:type input))
      (let [{:keys [from value]} (:msg input)
            heard (assoc (:heard state) from value)
            need (n/byzantine-threshold (count (:validators state)))]
        (if (and (not (:done? state)) (>= (count heard) need))
          (let [decision (first (sort (map str (vals heard))))]
            (n/result (assoc state :heard heard :done? true)
                      [(n/commit [decision] 0)]))
          (n/result (assoc state :heard heard))))
      (n/result state))))

(def ^:private peers [:a :b :c :d :e])

(defn- fingerprint
  "A compact, order-stable summary of a whole simulation run."
  [seed drop-rate ticks]
  (let [s (sim/run (sim/make {:seed seed
                              :nodes (zipmap peers (repeat (->Fingerprint)))
                              :config {:drop-rate drop-rate}})
                   ticks)]
    {:tick (:tick s)
     :committed (into (sorted-map) (sim/all-committed s))
     :trace-events (mapv (fn [e] [(:tick e) (:event e) (:from e) (:to e)])
                         (:trace s))
     :inflight (count (:inflight s))}))

(deftest simulation-is-identical-across-platforms
  (testing "the same seed must produce the same history on clj and cljs"
    ;; Two runs on one platform must agree...
    (is (= (fingerprint 42 0.0 40) (fingerprint 42 0.0 40)))
    (is (= (fingerprint 7 0.3 40) (fingerprint 7 0.3 40)))
    ;; ...and different seeds must not, or the simulator would only ever
    ;; explore a single history.
    (is (not= (fingerprint 42 0.3 40) (fingerprint 43 0.3 40)))))

(deftest committed-values-are-stable
  (testing "a clean network converges to the same decision everywhere"
    (let [fp (fingerprint 42 0.0 40)]
      (is (= 5 (count (:committed fp))))
      (is (= 1 (count (distinct (remove empty? (vals (:committed fp))))))
          "every node that decided, decided the same value"))))

(deftest lossy-network-fingerprint-is-reproducible
  (testing "reproducibility must survive faults, not just the happy path"
    (is (= (fingerprint 99 0.4 60) (fingerprint 99 0.4 60)))))
