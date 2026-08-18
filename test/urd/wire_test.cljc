(ns urd.wire-test
  "The wire format, pinned.

  These tests are `.cljc` on purpose: they run under both the JVM runner and
  the Node one, and the SAME hex must come out of both. That is the property
  `urd.wire` claims and the one nothing else in the suite would notice losing --
  a platform divergence here does not fail loudly, it produces a signature the
  other platform rejects, at whichever validator happens to be running the
  other runtime."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.crypto :as crypto]
            [urd.wire :as wire]))

(def ^:private payload
  "A realistic transaction signing payload: chain, sender, nonce, tx-data with
  a keyword attribute under a hex namespace and a tempid."
  {:chain "urd-testnet-1"
   :sender "deadbeefcafe"
   :nonce 7
   :tx-data [[:db/add -1 :deadbeefcafe/note "hello from python"]]})

(def ^:private expected
  "Produced independently by Python's `cbor2.dumps(payload, canonical=True)`.
  The payload shape is a ledger's -- skuld's, where `client.py` regenerates
  it -- but the ENCODING under test is urd's, and pinning it here is what makes
  a change to `urd.wire` fail in urd rather than downstream."
  (str "a4d827663a636861696e6d7572642d746573746e65742d31"
       "d827663a6e6f6e636507"
       "d827673a73656e6465726c646561646265656663616665"
       "d827683a74782d646174618184d827673a64622f61646420"
       "d827723a6465616462656566636166652f6e6f7465"
       "7168656c6c6f2066726f6d20707974686f6e"))

(deftest signing-bytes-are-pinned
  (testing "the exact bytes, on whichever platform is running this. Written out
            as a literal rather than compared against a second call, because a
            self-consistent encoder that changed its output would pass that."
    (is (= expected (crypto/bytes->hex (wire/signing-bytes payload))))))

(deftest signing-bytes-are-canonical
  (testing "map key order in the SOURCE does not reach the wire. `:canonical`
            sorts keys, so a client that builds its payload in a different
            order -- which every client written from the docstring will --
            still produces the bytes we signed."
    (let [shuffled {:tx-data (:tx-data payload) :nonce (:nonce payload)
                    :sender (:sender payload) :chain (:chain payload)}]
      (is (= expected (crypto/bytes->hex (wire/signing-bytes shuffled))))))

  (testing "and set element order does not either, which is the harder case:
            Clojure's set iteration order is hash-determined, so this is the
            one place where clj and cljs could legitimately differ."
    (let [ws (mapv #(str "member-" %) (range 24))]
      (is (= (crypto/bytes->hex (wire/signing-bytes (into #{} ws)))
             (crypto/bytes->hex (wire/signing-bytes (into #{} (reverse ws)))))))))

(deftest domain-separation-reaches-the-bytes
  (testing "a different chain is a different message. Trivially true, and worth
            a test anyway: `urd.consensus.auth` justifies the `:chain` field at
            length on the grounds that a testnet signature must not be a
            mainnet one, and that argument rests on this."
    (is (not= (crypto/bytes->hex (wire/signing-bytes payload))
              (crypto/bytes->hex (wire/signing-bytes (assoc payload :chain "urd-1")))))))
