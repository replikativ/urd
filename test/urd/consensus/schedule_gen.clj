(ns urd.consensus.schedule-gen
  "test.check generators for simulator schedules.

  Kept under `test/` so test.check stays off the runtime classpath. The point of
  generating a schedule as DATA rather than a seed is that test.check can shrink
  it: drop the partition, then the crash, then shorten the ticks, until what is
  left is the smallest history that still fails. Shrinking a seed cannot do that,
  because a smaller seed is an unrelated run rather than a simpler one."
  (:require [clojure.test.check.generators :as gen]))

(defn gen-tick
  ([] (gen-tick 1 10))
  ([lo hi] (gen/fmap (fn [n] [:tick n]) (gen/choose lo hi))))

(defn gen-fault
  "One fault step over `peers`.

  Listed mildest-first: `gen/one-of` shrinks toward earlier alternatives, and an
  isolate is far easier to read in a counterexample than an arbitrary partition."
  [peers]
  (let [peers (vec peers)]
    (gen/one-of
     [(gen/fmap (fn [p] [:isolate p]) (gen/elements peers))
      (gen/return [:heal])
      (gen/fmap (fn [p] [:crash p]) (gen/elements peers))
      (gen/fmap (fn [p] [:restart p]) (gen/elements peers))
      (gen/fmap (fn [ps]
                  (let [a (set ps), b (set (remove a peers))]
                    [:partition [a b]]))
                (gen/not-empty
                 (gen/vector-distinct (gen/elements peers)
                                      {:max-elements (max 1 (dec (count peers)))})))])))

(defn gen-schedule
  "A schedule over `peers`: interleaved ticks and faults, then quiet time.

  The trailing `[:heal]` and long tick are not decoration. Without them a
  schedule can end mid-partition, and then every run 'fails' to reach agreement
  for a reason that is not a bug -- which would make the property useless and,
  worse, would make it look like it was finding something."
  ([peers] (gen-schedule peers {}))
  ([peers {:keys [max-steps settle] :or {max-steps 12 settle 60}}]
   (gen/fmap (fn [steps] (vec (concat steps [[:heal] [:tick settle]])))
             (gen/vector (gen/one-of [(gen-tick) (gen-fault peers)])
                         0 max-steps))))

(defn gen-crash-heavy
  "Schedules weighted toward crash/restart cycles, for durability properties."
  [peers]
  (let [peers (vec peers)]
    (gen/fmap (fn [steps] (vec (concat (apply concat steps) [[:tick 80]])))
              (gen/vector
               (gen/fmap (fn [[p n m]] [[:crash p] [:tick n] [:restart p] [:tick m]])
                         (gen/tuple (gen/elements peers)
                                    (gen/choose 1 8)
                                    (gen/choose 1 8)))
               0 5))))
