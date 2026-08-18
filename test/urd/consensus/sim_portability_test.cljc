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
  (capabilities [_] {:emits #{:broadcast :commit}})
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
                      [(n/commit [decision])]))
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

(def pinned-42
  "Computed on the JVM and written down. THIS is the cross-platform claim: a
  ClojureScript run has to produce these exact values, not merely agree with
  itself."
  {:tick 40
   :committed {:a [":a"] :b [":a"] :c [":a"] :d [":a"] :e [":a"]}
   :trace-events []
   :inflight 0})

(def pinned-7
  "A lossy schedule, so the drop decisions themselves are pinned. `:drop-rate`
  is drawn from the seeded PRNG, which is the exact mechanism that used to
  differ between platforms -- cljs `bit-and` yielding a signed 32-bit integer
  gave different delays, drops and sampled peers, and every test that could
  have caught it was `.clj`."
  {:tick 40
   :committed {:a [":a"] :b [":b"] :c [] :d [] :e [":a"]}
   :trace-events [[0 :dropped-randomly :a :b]
                  [0 :dropped-randomly :a :c]
                  [0 :dropped-randomly :b :c]
                  [0 :dropped-randomly :c :d]
                  [0 :dropped-randomly :d :a]
                  [0 :dropped-randomly :e :d]]
   :inflight 0})

(def pinned-99
  {:tick 60
   :committed {:a [":a"] :b [] :c [":a"] :d [":a"] :e []}
   :trace-events [[0 :dropped-randomly :a :b]
                  [0 :dropped-randomly :b :e]
                  [0 :dropped-randomly :c :e]
                  [0 :dropped-randomly :d :a]
                  [0 :dropped-randomly :d :c]
                  [0 :dropped-randomly :d :e]
                  [0 :dropped-randomly :e :b]]
   :inflight 0})

(deftest simulation-is-identical-across-platforms
  (testing "pinned LITERALS, because the previous form established nothing

           This file's stated claim is end-to-end determinism ACROSS Clojure
           and ClojureScript. Three of its assertions were

               (is (= (fingerprint 42 0.0 40) (fingerprint 42 0.0 40)))

           a call compared to itself. Not one literal appeared in the file, so
           both platforms passed while producing entirely different histories,
           and the one job this namespace has was not being done. Its siblings
           do it correctly -- `portability-test` pins `[3336926330 ...]` and
           `scp-portability-test` pins real vectors -- which is what made this
           one stand out.

           The lossy fingerprints matter most: drop decisions come from the
           seeded PRNG, and that is precisely the mechanism that DID differ
           between platforms once."
    (is (= pinned-42 (fingerprint 42 0.0 40)))
    (is (= pinned-7 (fingerprint 7 0.3 40)))
    (is (= pinned-99 (fingerprint 99 0.4 60)))
    ;; The pin is only worth something if a DIFFERENT generator stream would
    ;; break it -- which is exactly what a cross-platform divergence is. So:
    ;; another seed must not match, and must not match in the trace as well as
    ;; the committed values, since the trace is where drop decisions land.
    (is (not= pinned-7 (fingerprint 8 0.3 40))
        "a different stream produces a different history, so these literals
         genuinely constrain the generator rather than describing any run")
    (is (not= (:trace-events pinned-7) (:trace-events (fingerprint 8 0.3 40)))
        "including the drop decisions specifically, which is the mechanism
         that actually differed between platforms once")
    (is (not= (fingerprint 42 0.3 40) (fingerprint 43 0.3 40)))))

(deftest committed-values-are-stable
  (testing "a clean network converges to the same decision everywhere"
    (let [fp (fingerprint 42 0.0 40)]
      ;; NOT `(= 5 (count (:committed fp)))` -- `sim/all-committed` maps over
      ;; `(:peer-ids sim)`, so that count is the peer count whatever happened,
      ;; including when nothing committed at all.
      (is (= (set peers) (set (keys (:committed fp)))))
      (is (every? seq (vals (:committed fp)))
          "and every peer actually decided something, which is the part the
           count could not tell us")
      (is (= 1 (count (distinct (remove empty? (vals (:committed fp))))))
          "every node that decided, decided the same value"))))

(deftest lossy-network-fingerprint-is-reproducible
  (testing "reproducibility must survive faults, not just the happy path.
            Pinned above; this asserts the weaker within-platform property that
            two runs of one seed agree, which is still worth having and is all
            the previous version of the file ever checked."
    (is (= (fingerprint 99 0.4 60) (fingerprint 99 0.4 60)))
    (is (seq (:trace-events (fingerprint 99 0.4 60)))
        "and the lossy run really does drop things, or 'survives faults' is a
         claim about a schedule with no faults in it")))
