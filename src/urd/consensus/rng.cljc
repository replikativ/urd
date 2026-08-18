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

  ClojureScript's bit operations coerce to 32-bit SIGNED integers; Clojure's act
  on 64-bit longs. Every operation here therefore normalizes back to an unsigned
  32-bit VALUE with `mask32`, so both platforms produce identical sequences. The
  tests pin a known sequence, and `rng-agrees-across-platforms` in
  `urd.consensus.portability-test` is the one that must be run under BOTH.

  `bit-and` alone is not enough, and this was a real bug: in ClojureScript
  `(bit-and 0xFFFFFFFF 0xFFFFFFFF)` is -1, not 4294967295. The bit PATTERN is
  right but the NUMBER is negative, and the two places that treat the word as a
  number rather than as bits -- `next-int`'s rejection bound and its `mod` --
  then take different branches. Measured before the fix, `next-int` with seed 7
  and bound 100 gave [83 55 7 45 67 56 62 87] on the JVM and
  [83 55 11 49 71 56 62 87] under Node. So the simulator's message delays, drop
  decisions and peer sampling all differed between platforms, which is precisely
  what this namespace exists to prevent. The extra `unsigned-bit-shift-right`
  by zero is a no-op on the JVM and is the standard `>>> 0` coercion to an
  unsigned value in JavaScript.

  ## Purity

  The generator is a value, not a mutable object: every draw returns
  `[value next-rng]`. Threading it explicitly is what lets a simulation be
  replayed, forked, or stepped backwards."
  (:refer-clojure :exclude [rand-int shuffle]))

(def ^:private mask 0xFFFFFFFF)

(defn- mask32
  "The low 32 bits of `x`, as a NON-NEGATIVE number on both platforms."
  [x]
  (unsigned-bit-shift-right (bit-and x mask) 0))

(defn make
  "Create a generator from a seed. Seed 0 is remapped, since xorshift has 0 as a
  fixed point and would emit nothing but zeros."
  [seed]
  (let [s (mask32 (if (zero? seed) 0x9E3779B9 seed))]
    {:state (if (zero? s) 0x9E3779B9 s)}))

(defn- mul32
  "32-bit multiply, portable and overflow-free.

  A direct `(* a b)` overflows a JVM long once both operands approach 2^32, and
  silently loses precision in ClojureScript, where numbers are doubles with 53
  bits of mantissa. Splitting the left operand into 16-bit halves keeps every
  partial product under 2^48, which is exact on both platforms. This is the same
  decomposition `Math.imul` polyfills use."
  [a b]
  (let [a (mask32 a), b (mask32 b)
        lo (* (bit-and a 0xFFFF) b)
        hi (bit-and (* (unsigned-bit-shift-right a 16) b) 0xFFFF)]
    (mask32 (+ lo (mask32 (bit-shift-left hi 16))))))

(defn from-key
  "Seed a generator from a STRUCTURED key -- a hash, an id, a counter.

  Use this, not `make`, whenever the seed is derived from something with
  structure. xorshift32 is linear over GF(2): every step is a shift and an xor,
  so `next-word(a XOR b) = next-word(a) XOR next-word(b)`. One round is a
  permutation, not a mixing function, and a structured difference between seeds
  survives as a structured difference between outputs.

  That is not theoretical. SCP's nomination leader lottery hashed peer ids with
  djb2, giving four peers the consecutive values 870040764 / 870040797 /
  870040830 / 870040863 -- multiples of 33 apart, one per character step. Passing
  those through `next-word` did not decorrelate them, and the highest node id led
  EVERY round of EVERY slot. Raft's election timeouts, seeded the same way, were
  measurably skewed: over 2000 terms five peers won 296/367/477/400/460 times
  against an expectation of 400 each, roughly 5.8 sigma at the low end.

  Both were invisible in testing, and that is the instructive part. A broken
  leader lottery is indistinguishable from a working one until its permanent
  leader is partitioned away -- consensus was reached in every run, before and
  after.

  The fix is an avalanche finalizer (the murmur3 mix): multiply-xorshift rounds
  that make every input bit affect every output bit, applied BEFORE the state is
  handed to xorshift."
  [k]
  (let [h (mask32 (if (number? k) k (hash k)))
        ;; murmur3 fmix32
        h (mask32 (bit-xor h (unsigned-bit-shift-right h 16)))
        h (mul32 h 0x85ebca6b)
        h (mask32 (bit-xor h (unsigned-bit-shift-right h 13)))
        h (mul32 h 0xc2b2ae35)
        h (mask32 (bit-xor h (unsigned-bit-shift-right h 16)))]
    (make h)))

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

(defn- weighted-index
  "Which item does cumulative position `draw` land in?"
  [weights draw]
  (loop [idx 0, acc 0]
    (let [acc' (+ acc (nth weights idx))]
      (if (or (< draw acc') (= idx (dec (count weights))))
        idx
        (recur (inc idx) acc')))))

(defn sample-weighted-bag
  "Draw `k` units of WEIGHT, without replacement, weighted by `weight-fn`.

  Returns [bag rng'] where bag is {item -> multiplicity} summing to
  `(min k (total weight))`.

  Two halves, and getting either wrong changes the protocol:

  - The result is a BAG, not a set. avalanchego samples stake weight, so a node
    holding half the stake is drawn about half the sample and that multiplicity
    IS its vote weight in the poll (`weighted_without_replacement.go:6-8`).
    Returning a set would make a half-stake node count once.

  - The draw is WITHOUT replacement, over the units. Each unit of weight is
    consumed when drawn, so a node of weight 1 appears at most once. Drawing
    with replacement instead -- which this did, contradicting its own docstring
    -- lets one unit-weight peer out of four fill an entire k=3 sample. That is
    not a variance nuisance: alpha is a fraction of k, so a single peer's
    opinion then clears alpha on its own, and Snowball's safety argument, which
    assumes alpha distinct opinions out of a k-sample, no longer holds."
  [rng coll weight-fn k]
  (let [items (vec coll)
        weights0 (mapv #(max 0 (weight-fn %)) items)
        total0 (reduce + 0 weights0)]
    (if (or (empty? items) (zero? total0))
      [{} rng]
      (loop [i 0, r rng, weights weights0, total total0, bag {}]
        (if (or (>= i k) (zero? total))
          [bag r]
          (let [[draw r'] (next-int r total)
                idx (weighted-index weights draw)]
            (recur (inc i) r'
                   (update weights idx dec)
                   (dec total)
                   (update bag (nth items idx) (fnil inc 0)))))))))
