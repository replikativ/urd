(ns urd.consensus.bignat
  "Arbitrary-precision NATURAL numbers, in portable ClojureScript-safe arithmetic.

  This exists for exactly one reason: Nakamoto fork choice compares cumulative
  proof-of-work, which is a sum of terms of the form `floor(2^256 / (target+1))`.
  Those numbers do not fit in a JavaScript double, and the comparison must be
  EXACT -- btcd's rule is `>` and not `>=` (`chain.go:1257`), so ties go to the
  incumbent and first-seen wins. An approximate comparison would silently
  convert a tie into a reorg, which is a consensus fault, not a rounding error.

  ## Why not the host's big integers

  `java.math.BigInteger` exists; `js/BigInt` exists. Using them would mean a
  reader conditional in every arithmetic expression, and -- worse -- two
  independent implementations of the consensus arithmetic, which is precisely
  the shape of bug this repository has already been bitten by once: `rng`
  produced different draws under ClojureScript for as long as it existed,
  because `bit-and` there yields a SIGNED 32-bit integer. Nothing in this
  namespace can diverge that way, because it is one implementation.

  The JVM's BigInteger is still useful -- as an ORACLE. `bignat_test` property-
  tests every operation here against it.

  ## Representation

  A vector of limbs, base 2^16, LEAST significant first, with no trailing zero
  limbs. Zero is `[]`.

  Base 2^16 is chosen so that every intermediate stays exactly representable in
  a double. The largest quantity computed anywhere below is a schoolbook
  multiply accumulator, `limb*limb + limb + carry < 2^32 + 2^17`, about 4.3e9 --
  eleven orders of magnitude short of 2^53. A base of 2^24 would still fit a
  single product but not a long accumulation, and base 2^32 would not fit at
  all. Bit operations are never applied to anything wider than a limb, so
  ClojureScript's signed 32-bit `bit-and` is never reached.

  Everything here is total and non-negative: `sub` requires `a >= b`."
  (:refer-clojure :exclude [zero? compare]))

;; ============================================================
;; Representation
;; ============================================================

(def limb-bits 16)
(def limb-base 65536)
(def ^:private limb-mask 65535)

(def zero [])
(def one [1])

(declare bit-length)

(defn- trim
  "Drop trailing (most significant) zero limbs, so equality is structural."
  [v]
  (let [n (count v)]
    (loop [i n]
      (cond
        (= 0 i) zero
        (= 0 (nth v (dec i))) (recur (dec i))
        (= i n) (vec v)
        :else (subvec (vec v) 0 i)))))

(defn zero? [a] (empty? a))

(defn from-int
  "A non-negative integer below 2^53 as a bignat."
  [n]
  (when (neg? n)
    (throw (ex-info "bignat is unsigned" {:n n})))
  (loop [n n, acc []]
    (if (= 0 n)
      (trim acc)
      (recur (quot n limb-base) (conj acc (mod n limb-base))))))

(defn to-int
  "Back to a plain integer. Throws above 2^53, where a double stops being exact
  -- returning a silently-wrong number is the one thing this namespace exists to
  prevent."
  [a]
  ;; Checked BEFORE the fold, not after: on the JVM the multiply would throw a
  ;; long overflow first, and in ClojureScript it would not throw at all -- it
  ;; would return a rounded double. Same guard, both platforms.
  (when (> (bit-length a) 53)
    (throw (ex-info "bignat does not fit in an exact integer"
                    {:bits (bit-length a)})))
  (reduce (fn [acc l] (+ (* acc limb-base) l)) 0 (reverse a)))

;; ============================================================
;; Comparison
;; ============================================================

(defn compare
  "-1, 0 or 1. Structural: both arguments must be trimmed."
  [a b]
  (let [na (count a), nb (count b)]
    (cond
      (< na nb) -1
      (> na nb) 1
      :else (loop [i (dec na)]
              (if (neg? i)
                0
                (let [x (nth a i), y (nth b i)]
                  (cond (< x y) -1
                        (> x y) 1
                        :else (recur (dec i)))))))))

(defn lt [a b] (neg? (compare a b)))
(defn le [a b] (not (pos? (compare a b))))
(defn gt [a b] (pos? (compare a b)))
(defn ge [a b] (not (neg? (compare a b))))

;; ============================================================
;; Addition and subtraction
;; ============================================================

(defn add [a b]
  (let [n (max (count a) (count b))]
    (loop [i 0, carry 0, acc []]
      (if (and (>= i n) (= 0 carry))
        (trim acc)
        (let [s (+ (if (< i (count a)) (nth a i) 0)
                   (if (< i (count b)) (nth b i) 0)
                   carry)]
          (recur (inc i) (quot s limb-base) (conj acc (mod s limb-base))))))))

(defn sub
  "a - b, requiring a >= b. A negative result is a bug in the caller, so it
  throws rather than wrapping."
  [a b]
  (when (lt a b)
    (throw (ex-info "bignat subtraction would go negative" {:a a :b b})))
  (loop [i 0, borrow 0, acc []]
    (if (>= i (count a))
      (trim acc)
      (let [d (- (nth a i)
                 (if (< i (count b)) (nth b i) 0)
                 borrow)]
        (if (neg? d)
          (recur (inc i) 1 (conj acc (+ d limb-base)))
          (recur (inc i) 0 (conj acc d)))))))

;; ============================================================
;; Multiplication and division
;; ============================================================

(defn mul-small
  "a * m for a plain integer m in [0, 2^31). The largest intermediate is
  limb*m + carry < 2^47 + 2^31."
  [a m]
  (when (neg? m) (throw (ex-info "bignat is unsigned" {:m m})))
  (if (or (= 0 m) (zero? a))
    zero
    (loop [i 0, carry 0, acc []]
      (if (and (>= i (count a)) (= 0 carry))
        (trim acc)
        (let [t (+ (* (if (< i (count a)) (nth a i) 0) m) carry)]
          (recur (inc i) (quot t limb-base) (conj acc (mod t limb-base))))))))

(defn mul
  "Schoolbook multiply. O(n*m), which is ample for 256-bit quantities."
  [a b]
  (if (or (zero? a) (zero? b))
    zero
    (let [na (count a), nb (count b)]
      (trim
       (loop [i 0, acc (vec (repeat (+ na nb) 0))]
         (if (>= i na)
           acc
           (recur (inc i)
                  (loop [j 0, carry 0, acc acc]
                    (if (and (>= j nb) (= 0 carry))
                      acc
                      (let [k (+ i j)
                            t (+ (nth acc k)
                                 (* (nth a i) (if (< j nb) (nth b j) 0))
                                 carry)]
                        (recur (inc j) (quot t limb-base)
                               (assoc acc k (mod t limb-base)))))))))))))

(defn divmod-small
  "[quotient remainder] for a plain integer divisor d in (0, 2^31).
  The largest intermediate is r*2^16 + limb < 2^47."
  [a d]
  (when (not (pos? d)) (throw (ex-info "bignat division by zero" {:d d})))
  (loop [i (dec (count a)), r 0, acc (vec (repeat (count a) 0))]
    (if (neg? i)
      [(trim acc) r]
      (let [cur (+ (* r limb-base) (nth a i))]
        (recur (dec i) (mod cur d) (assoc acc i (quot cur d)))))))

(defn div-small [a d] (first (divmod-small a d)))

;; ============================================================
;; Bit access
;; ============================================================

(defn bit-length
  "Number of significant bits; 0 for zero."
  [a]
  (if (zero? a)
    0
    (let [top (nth a (dec (count a)))]
      (loop [b limb-bits]
        (if (pos? (bit-and top (bit-shift-left 1 (dec b))))
          (+ (* limb-bits (dec (count a))) b)
          (recur (dec b)))))))

(defn test-bit [a i]
  (let [l (quot i limb-bits)]
    (and (< l (count a))
         (pos? (bit-and (nth a l) (bit-shift-left 1 (mod i limb-bits)))))))

(defn shift-left
  "a * 2^n."
  [a n]
  (if (or (zero? a) (= 0 n))
    a
    (let [limbs (quot n limb-bits)
          bits (mod n limb-bits)
          shifted (if (= 0 bits)
                    (vec a)
                    ;; Done with mul rather than bit ops so nothing ever exceeds
                    ;; a limb-sized shift; the carry chain is explicit.
                    (loop [i 0, carry 0, acc []]
                      (if (and (>= i (count a)) (= 0 carry))
                        acc
                        (let [t (+ (* (if (< i (count a)) (nth a i) 0)
                                      (bit-shift-left 1 bits))
                                   carry)]
                          (recur (inc i) (quot t limb-base)
                                 (conj acc (mod t limb-base)))))))]
      (trim (into (vec (repeat limbs 0)) shifted)))))

(defn shift-right
  "floor(a / 2^n)."
  [a n]
  (let [limbs (quot n limb-bits)
        bits (mod n limb-bits)]
    (if (>= limbs (count a))
      zero
      (let [dropped (subvec (vec a) limbs)]
        (if (= 0 bits)
          (trim dropped)
          (let [d (bit-shift-left 1 bits)]
            (trim
             (vec (for [i (range (count dropped))]
                    (+ (quot (nth dropped i) d)
                       (* (mod (if (< (inc i) (count dropped))
                                 (nth dropped (inc i)) 0)
                               d)
                          (bit-shift-left 1 (- limb-bits bits)))))))))))))

(defn pow2 [n] (shift-left one n))

;; ============================================================
;; General division
;; ============================================================

(defn- shift-in-bit
  "2*a + b, for b in {0,1}. The inner step of binary long division."
  [a b]
  (loop [i 0, carry b, acc []]
    (if (and (>= i (count a)) (= 0 carry))
      (trim acc)
      (let [t (+ (* (if (< i (count a)) (nth a i) 0) 2) carry)]
        (recur (inc i) (quot t limb-base) (conj acc (mod t limb-base)))))))

(defn divmod
  "Floor division: [quotient remainder], for any non-zero divisor.

  Binary long division rather than Knuth D. It is O(bits * limbs), so a 256-bit
  divide is a few thousand operations -- more than fast enough, since the only
  caller is `calc-work`, once per header, and it is a lot easier to be sure it
  is right."
  [a b]
  (when (zero? b) (throw (ex-info "bignat division by zero" {:a a})))
  (if (lt a b)
    [zero a]
    (loop [i (dec (bit-length a)), q (vec (repeat (count a) 0)), r zero]
      (if (neg? i)
        [(trim q) r]
        (let [r' (shift-in-bit r (if (test-bit a i) 1 0))]
          (if (ge r' b)
            (recur (dec i)
                   (let [l (quot i limb-bits)]
                     (assoc q l (bit-or (nth q l)
                                        (bit-shift-left 1 (mod i limb-bits)))))
                   (sub r' b))
            (recur (dec i) q r')))))))

(defn div [a b] (first (divmod a b)))

;; ============================================================
;; Bytes and hex
;;
;; Big-endian throughout. Bitcoin's little-endian hash comparison is handled by
;; the caller reversing the bytes, exactly as btcd's `HashToBig` does.
;; ============================================================

(defn from-bytes-be
  "A sequence of unsigned bytes (0-255), most significant first."
  [bs]
  (reduce (fn [acc b]
            (when (or (neg? b) (> b 255))
              (throw (ex-info "not a byte" {:b b})))
            (add (shift-left acc 8) (from-int b)))
          zero
          bs))

(defn byte-length [a] (quot (+ (bit-length a) 7) 8))

(defn to-bytes-be
  "`n` unsigned bytes, most significant first, zero-padded. Throws if `a` does
  not fit -- a silently truncated target would be a consensus fault."
  [a n]
  (when (> (byte-length a) n)
    (throw (ex-info "bignat does not fit in the requested width"
                    {:bytes (byte-length a) :width n})))
  (vec (for [i (range (dec n) -1 -1)]
         (let [l (quot i 2)]
           (if (>= l (count a))
             0
             (let [limb (nth a l)]
               (if (even? i) (mod limb 256) (quot limb 256))))))))

(def ^:private hex-chars "0123456789abcdef")

(def ^:private hex-digit
  (into {} (map-indexed (fn [i c] [(str c) i]) hex-chars)))

(defn hex->bytes
  "An even-length hex string to a vector of unsigned bytes."
  [s]
  (when (odd? (count s))
    (throw (ex-info "hex string must have an even length" {:length (count s)})))
  (vec (for [i (range 0 (count s) 2)]
         (let [hi (hex-digit (subs s i (inc i)))
               lo (hex-digit (subs s (inc i) (+ i 2)))]
           (when (or (nil? hi) (nil? lo))
             (throw (ex-info "not a hex string" {:at i})))
           (+ (* 16 hi) lo)))))

(defn bytes->hex [bs]
  (apply str (mapcat (fn [b] [(nth hex-chars (quot b 16))
                              (nth hex-chars (mod b 16))])
                     bs)))

(defn from-hex [s] (from-bytes-be (hex->bytes s)))
(defn to-hex [a n] (bytes->hex (to-bytes-be a n)))
