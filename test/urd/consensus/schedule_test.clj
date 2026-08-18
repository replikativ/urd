(ns urd.consensus.schedule-test
  "Does shrinking actually work now?

  This is the test that justifies schedules-as-data. Before, a property failure
  reported a seed, and shrinking that seed produced an unrelated run rather than
  a simpler one -- so a failure told you almost nothing. The claim is that a
  schedule shrinks to a small, readable counterexample. That claim is checkable,
  so it is checked."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as n]
            [urd.consensus.sim :as sim]
            [urd.consensus.schedule :as sched]
            [urd.consensus.schedule-gen :as sg]))

;; A node that decides once it has heard from a Byzantine quorum. It is safe on
;; a clean network and unsafe under message loss -- see `sim-test` -- which makes
;; it a convenient subject for a property that genuinely fails.
(defrecord Decree []
  n/Node
  (capabilities [_] {:emits #{:broadcast :commit}})
  (init [_ config]
    (let [me (:peer-id config)]
      (n/result {:peer-id me :validators (:validators config)
                 :heard {me me} :done? false}
                [(n/broadcast :propose {:from me :value me})])))
  (step [_ state input]
    (if (= :message-received (:type input))
      (let [{:keys [from value]} (:msg input)
            heard (assoc (:heard state) from value)
            need (n/byzantine-threshold (count (:validators state)))]
        (if (and (not (:done? state)) (>= (count heard) need))
          (n/result (assoc state :heard heard :done? true)
                    [(n/commit [(first (sort (map str (vals heard))))])])
          (n/result (assoc state :heard heard))))
      (n/result state))))

(def peers [:a :b :c :d])

(defn- run-schedule [schedule]
  (sched/run-with {:seed 1 :nodes (zipmap peers (repeat (->Decree)))}
                  schedule))

;; ============================================================
;; Schedules do what they say
;; ============================================================

(deftest schedule-steps-apply
  (testing "each step has the effect its name claims"
    (let [s (run-schedule [[:tick 2] [:crash :b] [:tick 1]])]
      (is (contains? (:crashed s) :b)))
    (let [s (run-schedule [[:isolate :a] [:tick 1]])]
      (is (some #(= #{:a} %) (:partitions s))))
    (let [s (run-schedule [[:isolate :a] [:tick 1] [:heal] [:tick 1]])]
      (is (nil? (:partitions s))))))

(deftest unknown-step-throws
  (testing "an unrecognised step must not be silently skipped -- a schedule that
            quietly did nothing would produce a passing test that never ran"
    (is (thrown? Exception (run-schedule [[:not-a-real-step]])))))

(deftest a-clean-schedule-converges
  (let [s (run-schedule [[:tick 40]])]
    (is (sim/agreement? s))
    (is (every? seq (vals (sim/all-committed s))))))

;; ============================================================
;; The point: shrinking
;; ============================================================

(deftest shrinking-yields-a-small-readable-counterexample
  (testing "a deliberately false property must shrink to a minimal schedule.

            The property asserted here -- that every node commits no matter what
            happens -- is FALSE: isolate a node for the whole run and it hears
            nobody. What matters is not that test.check finds that, but that
            what it hands back is SMALL. Shrinking a seed could never do this,
            because a smaller seed is a different run rather than a simpler one."
    (let [result (tc/quick-check
                  200
                  (prop/for-all [schedule (sg/gen-schedule peers {:max-steps 10 :settle 40})]
                                (let [s (run-schedule schedule)]
                                  ;; False in general: a node isolated for the
                                  ;; whole run cannot commit.
                                  (every? seq (vals (sim/all-committed s)))))
                  :seed 12345)]
      (is (false? (:pass? result)) "the property really is false")
      (when-not (:pass? result)
        (let [smallest (-> result :shrunk :smallest first)
              faults (remove #(= :tick (first %)) smallest)]
          (is (some? smallest))
          ;; The generator can emit up to 10 steps plus the trailing heal+tick.
          ;; A useful shrink gets well under that.
          (is (<= (count smallest) 6)
              (str "counterexample should be small, got " (count smallest)
                   " steps:\n" (sched/describe smallest)))
          (is (<= (count faults) 3)
              (str "should isolate the few faults that matter, got:\n"
                   (sched/describe smallest))))))))

(deftest describe-is-readable
  (is (= "  run 3 ticks\n  CRASH :b\n  isolate :a\n  heal"
         (sched/describe [[:tick 3] [:crash :b] [:isolate :a] [:heal]]))))

;; ============================================================
;; A real property, expressed over schedules
;; ============================================================

(deftest a-real-safety-violation-shrinks-to-four-steps
  (testing "the payoff, on a property anyone would actually write.

            `Decree` is unsafe by construction -- it commits the minimum of
            whatever it happened to hear once it has a quorum's worth, so under
            message loss different nodes hold different subsets and commit
            different values. Asserting agreement over it is a property that
            genuinely fails, which is exactly what a real one does when the
            algorithm is broken.

            The point is what you get back. Under the old seed-based scheme this
            failure reported `seed 999` and nothing else, and shrinking the seed
            produced an unrelated run. Now it reports:

                isolate :a
                run 1 ticks
                heal
                run 60 ticks

            Four steps, one fault, and the fault is the cause. That difference
            is the whole reason for schedules-as-data."
    (let [result (tc/quick-check
                  150
                  (prop/for-all [schedule (sg/gen-schedule peers {:max-steps 10 :settle 60})]
                                (sim/agreement? (run-schedule schedule)))
                  :seed 999)]
      (is (false? (:pass? result))
          "Decree is unsafe under loss; a passing result would mean the
           simulator had stopped detecting divergence")
      (let [smallest (-> result :shrunk :smallest first)
            faults (remove #(= :tick (first %)) smallest)]
        (is (<= (count smallest) 5)
            (str "counterexample should be minimal, got:\n" (sched/describe smallest)))
        (is (<= (count faults) 2)
            (str "and should name only the faults that matter, got:\n"
                 (sched/describe smallest)))
        ;; Re-running the shrunk schedule must reproduce the failure, or the
        ;; counterexample would be decorative.
        (is (not (sim/agreement? (run-schedule smallest)))
            "the reported schedule must actually reproduce the violation")))))
