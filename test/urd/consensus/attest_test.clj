(ns urd.consensus.attest-test
  "Real Ed25519 attestations, and what they refuse.

  Every other attestation test in this repository runs against
  `test-attestations`, which is a hash anyone can recompute. Those tests prove
  the algorithm CONSULTS its scheme; they cannot prove a scheme is worth
  consulting. These do."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.core.async :refer [<!!]]
            [urd.consensus.attest :as attest]
            [urd.consensus.node :as n]
            [urd.consensus.store :as store]
            [urd.consensus.stores.konserve :as disk]
            [konserve.filestore :as fs]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.algorithms.round-robin-test :refer [landed-step]])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; ============================================================
;; Keys
;; ============================================================

(def ^:private validators [:v1 :v2 :v3])

(defn- keyring
  "A keypair per validator. Generated once per test, never checked in: these
  are not fixtures, and a private key in a repository has a way of outliving
  the reason it was put there."
  []
  (into {} (map (fn [v] [v (<!! (attest/generate-keypair))])) validators))

(defn- public-keys [kr] (into {} (map (fn [[v kp]] [v (:public kp)])) kr))

(defn- scheme
  ([kr who] (scheme kr who "urd-test-chain"))
  ([kr who chain]
   (attest/attestations {:chain chain
                         :peer-id who
                         :private-key (:private (get kr who))
                         :public-keys (public-keys kr)})))

;; ============================================================
;; The primitive
;; ============================================================

(deftest a-real-attestation-round-trips
  (let [kr (keyring)
        {:keys [sign-vote]} (scheme kr :v1)
        {:keys [verify-vote]} (scheme kr :v2)
        payload [7 "proposal-abc"]
        att (sign-vote :v1 payload)]
    (testing "v2 believes v1's vote without holding v1's key -- which is the
              whole point, since a relayed vote reaches a node that never spoke
              to its author"
      (is (true? (verify-vote :v1 payload att))))
    (testing "and it is a real signature, not a digest of public inputs"
      (is (= 64 (count att))))))

(deftest an-attestation-is-bound-to-its-height
  (testing "THE property this change bought. Round-robin used to sign a bare
            proposal id, and a `snapshot-id` is permitted to be a
            content hash -- so proposing the same value at two heights produced
            the same id, and one saved attestation was a valid vote at every
            later height it recurred at."
    (let [kr (keyring)
          {:keys [sign-vote]} (scheme kr :v1)
          {:keys [verify-vote]} (scheme kr :v2)
          pid "the-same-value-proposed-twice"
          att (sign-vote :v1 (rr/vote-payload {:height 3} pid))]
      (is (true? (verify-vote :v1 (rr/vote-payload {:height 3} pid) att)))
      (is (false? (verify-vote :v1 (rr/vote-payload {:height 4} pid) att))
          "a height-3 vote must not count at height 4"))))

(deftest an-attestation-is-bound-to-its-chain
  (testing "a vote cast on a testnet is not a vote on mainnet -- the same
            argument `urd.consensus.auth` makes about messages, one layer down"
    (let [kr (keyring)
          payload [1 "p"]
          att ((:sign-vote (scheme kr :v1 "testnet")) :v1 payload)]
      (is (true? ((:verify-vote (scheme kr :v2 "testnet")) :v1 payload att)))
      (is (false? ((:verify-vote (scheme kr :v2 "mainnet")) :v1 payload att))))))

(deftest an-attestation-is-bound-to-its-voter
  (testing "v1's signature does not become v2's vote by relabelling it, which
            is exactly what a malicious relayer would try"
    (let [kr (keyring)
          payload [1 "p"]
          att ((:sign-vote (scheme kr :v1)) :v1 payload)]
      (is (false? ((:verify-vote (scheme kr :v3)) :v2 payload att))))))

(deftest we-can-only-sign-as-ourselves
  (testing "we hold one key. Being asked to vote as somebody else is a caller
            bug, and signing it silently would produce a vote that verifies
            against the wrong key and is dropped a long way from the cause."
    (let [kr (keyring)]
      (is (thrown? clojure.lang.ExceptionInfo
                   ((:sign-vote (scheme kr :v1)) :v2 [1 "p"]))))))

(deftest verification-refuses-rather-than-throws
  (testing "these bytes arrive from the network and are checked inside a pure
            transition. A malformed signature is a vote to ignore, not a node
            to crash -- and `urd.consensus.auth/try-verify` records what
            accepting a truthy exception costs: every malformed signature
            verifies and an empty one authenticates as anyone."
    (let [kr (keyring)
          {:keys [verify-vote]} (scheme kr :v1)
          payload [1 "p"]]
      (is (false? (verify-vote :v2 payload nil)))
      (is (false? (verify-vote :v2 payload (byte-array 0))))
      (is (false? (verify-vote :v2 payload (byte-array 64))))
      (is (false? (verify-vote :v2 payload "not-even-bytes")))
      (testing "and an unknown voter is false however well-formed its signature"
        (let [outsider (<!! (attest/generate-keypair))
              att ((:sign-vote (attest/attestations
                                {:chain "urd-test-chain" :peer-id :nobody
                                 :private-key (:private outsider)
                                 :public-keys {:nobody (:public outsider)}}))
                   :nobody payload)]
          (is (false? (verify-vote :nobody payload att))))))))

(deftest a-partial-config-refuses-to-build
  (testing "a validator that cannot check its peers' votes should refuse to
            start, not start and count them"
    (is (thrown? clojure.lang.ExceptionInfo
                 (attest/attestations {:peer-id :v1 :private-key (byte-array 32)
                                       :public-keys {:v1 (byte-array 32)}})))
    (is (thrown? clojure.lang.ExceptionInfo
                 (attest/attestations {:chain "c" :peer-id :v1
                                       :private-key (byte-array 32)})))))

;; ============================================================
;; Drop-in for the real algorithm
;; ============================================================

(deftest real-attestations-drive-a-real-round
  (testing "the scheme is a drop-in for `test-attestations`: round-robin
            reaches a commit with genuine signatures and nothing else changed.
            This is what `init`'s refusal to start without a scheme has been
            waiting for."
    (let [kr (keyring)
          impl (rr/create (zipmap validators (repeat nil)))
          st (:state (n/init impl (merge (scheme kr :v1)
                                         {:peer-id :v1 :validators validators})))
          ;; v1 proposes at height 0 and votes for its own proposal.
          proposed (landed-step impl st {:type :value-ready :value {:snapshot-id "s0"}})
          st1 (:state proposed)
          pid (:current-proposal-id st1)
          ;; v2 votes, genuinely.
          att2 ((:sign-vote (scheme kr :v2)) :v2 (rr/vote-payload st1 pid))
          r (landed-step impl st1 {:type :message-received :from :v2
                                   :msg {:kind :vote :proposal-id pid
                                         :voter :v2 :att att2}})]
      (is (some? pid))
      ;; Effects are `[kind payload]` vectors, not maps.
      (is (some #(= :commit (first %)) (:effects r))
          "two of three is a majority, so this commits")
      (testing "and the whole loop closes: the votes the algorithm broadcasts on
                `:finalizations` ARE a commit certificate, and a third party
                holding nothing but the validator set can check it. This is the
                assertion the rest of the namespace exists to support."
        (let [finalized (:msg (second (some #(when (= :broadcast (first %)) %)
                                            (:effects r))))
              votes (:votes finalized)
              cert (attest/certificate {:chain "urd-test-chain"
                                        :payload (rr/vote-payload st1 pid)
                                        :votes votes})
              checked (<!! (attest/verify-certificate cert (public-keys kr)))]
          (is (= #{:v1 :v2} (set (keys votes))))
          (is (every? #(= 64 (count %)) (vals votes)))
          (is (= #{:v1 :v2} (:voters checked))
              "both signatures verify against the keys, off the algorithm")
          (is (not (:valid? checked))
              "though two of three misses the BYZANTINE threshold, which for
               n=3 is unanimity -- round-robin committed on a crash-fault
               majority, and a certificate is held to the stricter bar on
               purpose")))

      (testing "and a forged vote from the third validator does not"
        (let [forged (landed-step impl st1 {:type :message-received :from :v3
                                            :msg {:kind :vote :proposal-id pid
                                                  :voter :v3 :att (byte-array 64)}})]
          (is (not-any? #(= :commit (first %)) (:effects forged))))))))

;; ============================================================
;; Commit certificates
;; ============================================================

(defn- cert-for
  "A certificate over `payload`, signed by `signers`."
  [kr chain payload signers]
  (attest/certificate
   {:chain chain
    :payload payload
    :votes (into {} (map (fn [v] [v ((:sign-vote (scheme kr v chain)) v payload)]))
                 signers)}))

(deftest a-certificate-proves-a-decision-to-a-stranger
  (let [kr (keyring)
        pks (public-keys kr)
        payload (rr/vote-payload {:height 12} "block-12")]

    (testing "three of three clears the Byzantine threshold for n=3, which is
              unanimity -- n=3 tolerates zero Byzantine faults"
      (let [r (<!! (attest/verify-certificate (cert-for kr "c" payload validators) pks))]
        (is (:valid? r))
        (is (= #{:v1 :v2 :v3} (:voters r)))
        (is (= 3 (:quorum r)))))

    (testing "two of three does not, and the result says so in numbers rather
              than as a bare false -- one signature short and signed by nobody
              are different situations"
      (let [r (<!! (attest/verify-certificate (cert-for kr "c" payload [:v1 :v2]) pks))]
        (is (not (:valid? r)))
        (is (= #{:v1 :v2} (:voters r)))
        (is (= 3 (:quorum r)))
        (is (= 3 (:of r)))))

    (testing "a tampered payload invalidates every signature at once, because
              each one covers it"
      (let [c (assoc (cert-for kr "c" payload validators)
                     :payload (rr/vote-payload {:height 12} "block-13"))
            r (<!! (attest/verify-certificate c pks))]
        (is (not (:valid? r)))
        (is (empty? (:voters r)))))

    (testing "and so does a tampered chain"
      (let [c (assoc (cert-for kr "c" payload validators) :chain "other")
            r (<!! (attest/verify-certificate c pks))]
        (is (not (:valid? r)))))

    (testing "an outsider cannot manufacture a quorum by minting keys, however
              valid their signatures are: a voter outside the set contributes
              nothing"
      (let [outsiders (into {} (map (fn [v] [v (<!! (attest/generate-keypair))]))
                            [:x1 :x2 :x3])
            c (cert-for (merge kr outsiders) "c" payload [:v1 :x1 :x2 :x3])
            r (<!! (attest/verify-certificate c pks))]
        (is (not (:valid? r)))
        (is (= #{:v1} (:voters r)))))

    (testing "a duplicated signature is one voter, not two. `:votes` is keyed
              by voter, so this cannot arise from the map -- but the count is
              over DISTINCT voters and that is what the assertion pins."
      (let [c (cert-for kr "c" payload [:v1 :v1 :v1])
            r (<!! (attest/verify-certificate c pks))]
        (is (not (:valid? r)))
        (is (= #{:v1} (:voters r)))))))

(deftest the-certificate-threshold-is-byzantine-not-crash
  (testing "a certificate is a claim made TO A STRANGER, so it uses
            floor(2n/3)+1 rather than round-robin's crash-fault majority. The
            two coincide at n=4 and diverge from n=5 on."
    (is (= 3 (attest/byzantine-quorum-size 3)))
    (is (= 3 (attest/byzantine-quorum-size 4)))
    (is (= 4 (attest/byzantine-quorum-size 5)))
    (is (= 5 (attest/byzantine-quorum-size 7)))
    (testing "and a caller with a different threat model can say so. Note the
              override takes a COUNT, not a validator set -- `rr/quorum-size`
              takes the set itself, so the two are not interchangeable and
              passing one where the other is expected is a real trap."
      (let [kr (keyring)
            payload (rr/vote-payload {:height 1} "p")
            crash-majority (fn [n] (inc (quot n 2)))
            r (<!! (attest/verify-certificate
                    (cert-for kr "c" payload [:v1 :v2]) (public-keys kr)
                    {:quorum-size crash-majority}))]
        (is (= 2 (crash-majority 3)))
        (is (= (crash-majority 3) (rr/quorum-size (zipmap validators (repeat nil))))
            "the same threshold round-robin itself uses, stated two ways")
        (is (:valid? r) "two of three IS a crash-fault majority")))))

(deftest ^:integration round-robin-recovers-a-real-vote-from-disk
  (let [dir (Files/createTempDirectory "urd-round-robin-recovery" (make-array FileAttribute 0))
        path (str dir)
        kr (keyring)
        node (rr/create)
        cfg #(merge (scheme kr :v1) {:peer-id :v1 :validators validators})
        chosen {:snapshot-id :p}
        voted (n/step node (:state (n/init node (cfg))) (n/value-ready chosen {:height 0}))
        record (select-keys (get-in voted [:effects 0 1]) [:writes :durable?])]
    (try
      (let [wal (disk/connect-fs-store! path)]
        (try (is (true? (<!! (store/write! wal record))))
             (finally (<!! (store/close-store! wal)))))
      (let [wal (disk/connect-fs-store! path)]
        (try
          (let [st (:state (n/init node (assoc (cfg) :restored (<!! (store/restore wal)))))
                vote (get-in st [:votes :p :v1])
                verifier (:verify-vote (scheme kr :v2))
                repeat (n/step node st (n/value-ready {:snapshot-id :another} {:height 0}))]
            (is (verifier :v1 (rr/vote-payload st :p) vote))
            (is (= chosen (:current-proposal st)))
            (is (= [chosen] (keep #(get-in % [1 :msg :proposal]) (:effects repeat)))))
          (finally (<!! (store/close-store! wal)))))
      (finally (fs/delete-store path)))))
