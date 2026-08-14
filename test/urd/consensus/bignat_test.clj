(ns urd.consensus.bignat-test
  "`urd.consensus.bignat` against `java.math.BigInteger`.

  The point of the namespace under test is that it is ONE implementation shared
  by Clojure and ClojureScript, rather than a reader conditional over two host
  big-integer types that can silently disagree. That is only worth anything if
  the one implementation is right, so this file uses the JVM's BigInteger purely
  as an ORACLE -- never as the implementation.

  These are `.clj` and not `.cljc` on purpose: BigInteger does not exist under
  ClojureScript, and a test that quietly skipped there would be worse than no
  test at all. The cross-platform half lives in `portability-test`, which pins
  concrete values both platforms must agree on."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.bignat :as bn])
  (:import [java.math BigInteger]))

;; ============================================================
;; The oracle bridge
;; ============================================================

(defn- ->bi ^BigInteger [a]
  (BigInteger. (bn/bytes->hex (bn/to-bytes-be a (max 1 (bn/byte-length a)))) 16))

(defn- <-bi [^BigInteger b]
  (let [s (.toString b 16)]
    (bn/from-hex (if (odd? (count s)) (str "0" s) s))))

(def ^:private gen-bignat
  "Naturals up to 320 bits -- comfortably wider than the 256 bits consensus
  needs, so a carry that only shows up past the end of a target is still seen."
  (gen/fmap (fn [bs] (bn/from-bytes-be bs))
            (gen/vector (gen/choose 0 255) 0 40)))

;; ============================================================
;; Representation
;; ============================================================

(deftest zero-is-canonical
  (testing "there is exactly one representation of zero, so `=` is usable"
    (is (= bn/zero (bn/from-int 0)))
    (is (= bn/zero (bn/from-hex "0000000000")))
    (is (= bn/zero (bn/sub [5] [5])))
    (is (= bn/zero (bn/mul [7] bn/zero)))))

(defspec no-trailing-zero-limbs 300
  (prop/for-all [a gen-bignat]
                (or (empty? a) (pos? (peek a)))))

(defspec limbs-are-in-range 300
  (prop/for-all [a gen-bignat]
                (every? #(and (<= 0 %) (< % bn/limb-base)) a)))

(defspec bytes-roundtrip 300
  (prop/for-all [bs (gen/vector (gen/choose 0 255) 0 40)]
                (let [a (bn/from-bytes-be bs)]
                  (= a (bn/from-bytes-be (bn/to-bytes-be a (count bs)))))))

;; ============================================================
;; Arithmetic against the oracle
;; ============================================================

(defspec add-matches-biginteger 300
  (prop/for-all [a gen-bignat b gen-bignat]
                (= (.add (->bi a) (->bi b)) (->bi (bn/add a b)))))

(defspec sub-matches-biginteger 300
  (prop/for-all [a gen-bignat b gen-bignat]
                (let [[hi lo] (if (bn/ge a b) [a b] [b a])]
                  (= (.subtract (->bi hi) (->bi lo)) (->bi (bn/sub hi lo))))))

(defspec mul-matches-biginteger 300
  (prop/for-all [a gen-bignat b gen-bignat]
                (= (.multiply (->bi a) (->bi b)) (->bi (bn/mul a b)))))

(defspec divmod-matches-biginteger 300
  (prop/for-all [a gen-bignat b gen-bignat]
                (or (bn/zero? b)
                    (let [[q r] (bn/divmod a b)]
                      (and (= (.divide (->bi a) (->bi b)) (->bi q))
                           (= (.mod (->bi a) (->bi b)) (->bi r))
                           ;; The defining identity, checked independently of
                           ;; the oracle: a = q*b + r with 0 <= r < b.
                           (= a (bn/add (bn/mul q b) r))
                           (bn/lt r b))))))

(defspec small-ops-match-biginteger 300
  (prop/for-all [a gen-bignat
                 m (gen/choose 1 2000000)]
                (and (= (.multiply (->bi a) (BigInteger/valueOf m))
                        (->bi (bn/mul-small a m)))
                     (= (.divide (->bi a) (BigInteger/valueOf m))
                        (->bi (bn/div-small a m))))))

(defspec shifts-match-biginteger 200
  (prop/for-all [a gen-bignat n (gen/choose 0 200)]
                (and (= (.shiftLeft (->bi a) n) (->bi (bn/shift-left a n)))
                     (= (.shiftRight (->bi a) n) (->bi (bn/shift-right a n))))))

(defspec compare-matches-biginteger 300
  (prop/for-all [a gen-bignat b gen-bignat]
                (= (Integer/signum (.compareTo (->bi a) (->bi b)))
                   (bn/compare a b))))

(defspec bit-length-matches-biginteger 300
  (prop/for-all [a gen-bignat]
                (= (.bitLength (->bi a)) (bn/bit-length a))))

(defspec test-bit-matches-biginteger 200
  (prop/for-all [a gen-bignat i (gen/choose 0 330)]
                (= (.testBit (->bi a) i) (boolean (bn/test-bit a i)))))

(defspec hex-roundtrips 300
  (prop/for-all [a gen-bignat]
                (= a (bn/from-hex (bn/to-hex a 40)))))

;; ============================================================
;; Guards
;; ============================================================

(deftest negative-results-throw-rather-than-wrap
  (testing "silent wraparound in a work comparison would be a consensus fault,
            so subtraction below zero is an error"
    (is (thrown? clojure.lang.ExceptionInfo (bn/sub [1] [2])))
    (is (thrown? clojure.lang.ExceptionInfo (bn/from-int -1)))
    (is (thrown? clojure.lang.ExceptionInfo (bn/divmod [1] bn/zero)))))

(deftest to-int-refuses-inexact-values
  (testing "above 2^53 a double stops being exact; returning a wrong number
            quietly is the failure this namespace exists to prevent"
    (is (= 65536 (bn/to-int (bn/pow2 16))))
    (is (thrown? clojure.lang.ExceptionInfo (bn/to-int (bn/pow2 64))))))

(deftest to-bytes-refuses-to-truncate
  (is (thrown? clojure.lang.ExceptionInfo (bn/to-bytes-be (bn/pow2 256) 32)))
  (is (= 32 (count (bn/to-bytes-be (bn/from-int 1) 32)))))

;; ============================================================
;; The one value the whole algorithm rests on
;; ============================================================

(deftest two-to-the-256
  (testing "the numerator of CalcWork"
    (is (= 257 (bn/bit-length (bn/pow2 256))))
    (is (= (.pow (BigInteger/valueOf 2) 256) (->bi (bn/pow2 256))))))
