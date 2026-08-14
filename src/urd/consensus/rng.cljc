(ns urd.consensus.rng
  "A deterministic, portable pseudo-random generator.

  `java.util.Random` is not available in ClojureScript, and even where a host
  PRNG exists the two platforms would not agree bit-for-bit -- which would mean a
  simulation run that fails on the JVM could not be reproduced in the browser.
  So we carry our own.

  This is xorshift32: three shift/xor rounds on a 32-bit word. It is fast, tiny,
  and has a period of 2^32-1, which is far more than a simulation needs. It is
  emphatically NOT cryptographic -- use `urd.crypto` for anything that must
  resist an adversary. This exists only so that a failing schedule is
  reproducible from its seed.

  ## Portability

  ClojureScript's bit operations coerce to 32-bit signed integers; Clojure's act
  on 64-bit longs. Every operation here therefore masks back to 32 bits with
  `mask32`, so both platforms produce identical sequences. The tests assert this
  by pinning a known sequence.

  ## Purity

  The generator is a value, not a mutable object: every draw returns
  `[value next-rng]`. Threading it explicitly is what lets a simulation be
  replayed, forked, or stepped backwards."
  (:refer-clojure :exclude [rand-int shuffle]))

(def ^:private mask 0xFFFFFFFF)

(defn- mask32 [x] (bit-and x mask))

(defn make
  "Create a generator from a seed. Seed 0 is remapped, since xorshift has 0 as a
  fixed point and would emit nothing but zeros."
  [seed]
  (let [s (mask32 (if (zero? seed) 0x9E3779B9 seed))]
    {:state (if (zero? s) 0x9E3779B9 s)}))

(defn next-word
  "Draw a 32-bit word. Returns [word rng']."
  [rng]
  (let [x (:state rng)
        x (mask32 (bit-xor x (mask32 (bit-shift-left x 13))))
        x (mask32 (bit-xor x (unsigned-bit-shift-right x 17)))
        x (mask32 (bit-xor x (mask32 (bit-shift-left x 5))))]
    [x {:state x}]))

(defn next-int
  "Draw an integer in [0, n). Returns [value rng'].

  Uses rejection sampling so the distribution is uniform -- a plain modulo would
  bias low values whenever n does not divide 2^32, which shows up as skewed
  peer selection in long simulation runs."
  [rng n]
  (assert (pos? n) "next-int needs a positive bound")
  (let [limit (- mask (mod mask n))]
    (loop [r rng, guard 0]
      (let [[w r'] (next-word r)]
        (cond
          (< w limit) [(mod w n) r']
          ;; Astronomically unlikely; bail out rather than spin forever.
          (> guard 64) [(mod w n) r']
          :else (recur r' (inc guard)))))))

(defn next-bool [rng]
  (let [[w r'] (next-word rng)]
    [(odd? w) r']))

(defn next-double
  "Draw a double in [0.0, 1.0)."
  [rng]
  (let [[w r'] (next-word rng)]
    [(/ (double w) 4294967296.0) r']))

(defn choose
  "Pick one element of `coll` uniformly. Returns [element rng']."
  [rng coll]
  (let [v (vec coll)]
    (if (empty? v)
      [nil rng]
      (let [[i r'] (next-int rng (count v))]
        [(nth v i) r']))))

(defn shuffle
  "Deterministic Fisher-Yates. Returns [shuffled rng']."
  [rng coll]
  (let [v (vec coll)]
    (if (< (count v) 2)
      [v rng]
      (loop [a (transient v), i (dec (count v)), r rng]
        (if (zero? i)
          [(persistent! a) r]
          (let [[j r'] (next-int r (inc i))
                ai (nth a i), aj (nth a j)]
            (recur (assoc! (assoc! a i aj) j ai) (dec i) r')))))))

(defn sample-without-replacement
  "Draw `k` distinct elements. Returns [sampled rng'].

  If k >= (count coll) the whole collection is returned, shuffled."
  [rng coll k]
  (let [[shuffled r'] (shuffle rng coll)]
    [(vec (take k shuffled)) r']))

(defn sample-weighted-bag
  "Draw `k` items weighted by `weight-fn`, WITH replacement of indices.

  Returns [bag rng'] where bag is {item -> multiplicity} totalling k.

  This models Avalanche's sampler faithfully, and the subtlety is deliberate:
  avalanchego samples *stake weight* without replacement, which means the same
  NODE can be drawn more than once, and that multiplicity is its vote weight in
  the poll. Returning a set here would silently change the protocol -- a node
  with half the stake would count once rather than half the sample."
  [rng coll weight-fn k]
  (let [items (vec coll)
        weights (mapv #(max 0 (weight-fn %)) items)
        total (reduce + 0 weights)]
    (if (or (empty? items) (zero? total))
      [{} rng]
      (loop [i 0, r rng, bag {}]
        (if (>= i k)
          [bag r]
          (let [[draw r'] (next-int r total)]
            (recur (inc i) r'
                   (loop [idx 0, acc 0]
                     (let [acc' (+ acc (nth weights idx))]
                       (if (or (< draw acc') (= idx (dec (count items))))
                         (update bag (nth items idx) (fnil inc 0))
                         (recur (inc idx) acc')))))))))))
