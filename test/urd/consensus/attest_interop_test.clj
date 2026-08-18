(ns urd.consensus.attest-interop-test
  "The certificate fixture, checked from the Clojure side.

  `doc/interop/verify_certificate.py` checks `doc/interop/certificate.json`
  with `cbor2` and `cryptography` and nothing else -- a light client that has
  never seen this codebase. This namespace checks the SAME file through
  geheimnis, so the fixture is pinned from both directions: if urd's encoding
  drifts, this fails; if the fixture were quietly regenerated to match a broken
  encoding, the Python script fails.

  A certificate that only its author can verify is not a certificate."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.core.async :refer [<!!]]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [urd.consensus.attest :as attest]
            [urd.crypto :as crypto]))

(defn- hex-map
  "The `{\"name\": \"hex\"}` object under `k`, as `{:keyword bytes}`.

  A hand-rolled reader rather than a JSON dependency: the fixture is a flat
  object of hex strings, and adding data.json to the core test path to read
  five lines would be the more surprising choice."
  [json k]
  (let [obj (second (re-find (re-pattern (str "\"" k "\"\\s*:\\s*\\{([^}]*)\\}")) json))]
    (into {} (map (fn [[_ n h]] [(keyword n) (crypto/hex->bytes h)]))
          (re-seq #"\"(\w+)\"\s*:\s*\"([0-9a-f]+)\"" obj))))

(defn- field [json k]
  (or (second (re-find (re-pattern (str "\"" k "\"\\s*:\\s*\"([^\"]*)\"")) json))
      (second (re-find (re-pattern (str "\"" k "\"\\s*:\\s*(\\d+)")) json))))

(def ^:private fixture (slurp (io/file "doc/interop/certificate.json")))

(def ^:private chain (field fixture "chain"))
(def ^:private height (Long/parseLong (field fixture "height")))
(def ^:private block (field fixture "block"))
(def ^:private votes (hex-map fixture "votes"))
(def ^:private validators (hex-map fixture "validators"))

;; Round-robin's `vote-payload`: the height is INSIDE what was signed.
(def ^:private payload [height block])

(deftest the-fixture-parsed
  (testing "guard the reader above -- a regex that matched nothing would make
            every assertion below vacuously true"
    (is (= "urd-testnet-1" chain))
    (is (= 12 height))
    (is (= 3 (count votes)))
    (is (= 3 (count validators)))
    (is (every? #(= 64 (count %)) (vals votes)) "64-byte Ed25519 signatures")
    (is (every? #(= 32 (count %)) (vals validators)) "32-byte public keys")))

(deftest the-certificate-python-verifies-also-verifies-here
  (let [cert (attest/certificate {:chain chain :payload payload :votes votes})
        r (<!! (attest/verify-certificate cert validators))]
    (is (:valid? r))
    (is (= #{:v1 :v2 :v3} (:voters r)))
    (is (= 3 (:quorum r)) "n=3 tolerates zero Byzantine faults, so unanimity")))

(deftest and-the-negative-controls-agree-too
  (testing "the same three checks `verify_certificate.py` prints. They are the
            reason the demo is not just a VALID with nothing behind it."
    (let [check (fn [c p]
                  (<!! (attest/verify-certificate
                        (attest/certificate {:chain c :payload p :votes votes})
                        validators)))]
      (is (empty? (:voters (check chain [(inc height) block])))
          "replayed one height later")
      (is (empty? (:voters (check "urd-mainnet" payload)))
          "claimed for another chain")
      (is (empty? (:voters (check chain [height "block-13"])))
          "payload tampered"))))
