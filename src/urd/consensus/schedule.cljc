(ns urd.consensus.schedule
  "Schedules as DATA, so a failing run shrinks to a minimal counterexample.

  ## The problem this solves

  Every property test in this project generated a *seed* and handed it to the
  simulator. test.check then dutifully shrank the seed -- and a numerically
  smaller seed produces a completely unrelated schedule, not a simpler one. So a
  failure reported \"seed 47283 fails\" and nothing more: no minimal case, no
  reduction, no way to see which fault mattered. Shrinking was structurally
  useless, which is most of the value of property testing.

  A schedule is instead an ordered vector of steps:

      [[:tick 3]
       [:crash :b]
       [:tick 5]
       [:partition [#{:a :b} #{:c :d}]]
       [:tick 10]
       [:heal]
       [:tick 20]]

  test.check shrinks a vector by dropping elements and simplifying each one, so
  it will remove the partition, then the crash, then shorten the ticks, and hand
  back the smallest schedule that still fails. That is a counterexample you can
  read.

  ## What is still drawn from the seed

  Message delays and duplication remain RNG-driven, because enumerating them as
  data would make schedules enormous without making counterexamples clearer. The
  faults that a human reasons about -- who crashed, who was partitioned from
  whom, when -- are data. Both are reproducible; only the second shrinks.

  A schedule with no fault steps is just \"run for n ticks\", so this subsumes
  the plain case rather than replacing it."
  (:require [clojure.string :as str]
            [urd.consensus.sim :as sim]))

;; ============================================================
;; Applying a schedule
;; ============================================================

(defn step
  "Apply one schedule step to a simulator."
  [s [op & args]]
  (case op
    :tick      (sim/run s (or (first args) 1))
    :crash     (sim/crash s (first args))
    :restart   (sim/restart s (first args))
    :partition (sim/partition-network s (first args))
    :heal      (sim/heal s)
    ;; Isolating one peer is expressible as a partition, but as its own step it
    ;; shrinks better: test.check can drop it wholesale rather than having to
    ;; simplify a set-of-sets into the right shape.
    :isolate   (let [p (first args)
                     others (set (remove #{p} (:peer-ids s)))]
                 (sim/partition-network s [#{p} others]))
    :inject    (sim/inject s (first args) (second args))
    :inject-all (sim/inject-all s (first args))
    ;; An unknown step is a bug in the generator, not something to skip
    ;; silently -- a schedule that quietly does nothing would produce a
    ;; "passing" test that never ran.
    (throw (ex-info "unknown schedule step" {:op op :args args}))))

(defn run
  "Apply a whole schedule."
  [s schedule]
  (reduce step s schedule))

(defn run-with
  "Build a simulator and run `schedule` against it.

  `sim-opts` is passed to `sim/make`; the seed still governs delays and
  duplication, while the schedule governs the faults."
  [sim-opts schedule]
  (run (sim/make sim-opts) schedule))

;; Generators live in `urd.consensus.schedule-gen`, under `test/`, so that
;; test.check stays off the runtime classpath.

;; ============================================================
;; Reporting
;; ============================================================

(defn describe
  "Render a schedule as something a human can read in a failure report."
  [schedule]
  (str/join
   "\n"
   (map (fn [[op & args]]
          (case op
            :tick (str "  run " (first args) " ticks")
            :crash (str "  CRASH " (first args))
            :restart (str "  restart " (first args))
            :isolate (str "  isolate " (first args))
            :partition (str "  partition " (pr-str (first args)))
            :heal "  heal"
            (str "  " op " " (pr-str args))))
        schedule)))
