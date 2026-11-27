(ns urd.consensus.auth-test
  "The verification edge.

  Until this existed the library performed no signature check anywhere:
  `verified-by` was `#{(:sender msg)}`, a field the sending peer wrote into its
  own message, so it carried the attacker's claim about the attacker's
  identity. Tendermint's guard `(contains? verified-by (:from msg))` compared
  two fields the same party controlled.

  No test could express impersonation, either -- the simulator constructs
  `verified-by` from its own routing table, which is ground truth, so a
  simulated Byzantine node cannot lie about who it is however hard it tries.
  That is why the hole survived a full Byzantine test suite and six reference
  audits of the algorithms."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.auth :as auth]
            [urd.consensus.store :as store]
            [clojure.edn :as edn]
            [clojure.core.async :refer [<!! chan close!]]))

(def ctx
  "What the transport is about to do with a message. Both fields are SIGNED --
  see `auth/digest` -- so a test that does not care still has to supply them."
  {:topic :test-topic :to nil})

(defn- keypair [] (<!! (auth/generate-keypair)))

(defn- cluster
  "An authenticator per peer, all sharing a chain id and each other's keys."
  [chain ids]
  (let [kps (into {} (map (fn [id] [id (keypair)])) ids)
        pubs (into {} (map (fn [[id kp]] [id (:public kp)])) kps)]
    {:keys kps
     :auth (into {} (map (fn [[id kp]]
                           [id (auth/authenticator {:chain chain :peer-id id
                                                    :private-key (:private kp)
                                                    :public-keys pubs}
                                                   id)]))
                 kps)}))

(deftest a-signed-message-verifies-and-names-its-author
  (let [{:keys [auth]} (cluster :test [:a :b])
        env (<!! (auth/seal (:a auth) {:kind :vote :height 3} ctx))
        opened (<!! (auth/unseal (:b auth) env))]
    (is (= :a (:from opened)))
    (is (= {:kind :vote :height 3} (:msg opened)))
    (is (= #{:a} (:verified-by opened))
        "and `verified-by` now means what node.cljc says it means")))

(deftest a-peer-cannot-speak-as-another
  (testing "THE hole. Any host able to reach the port could set `:sender` to a
            validator's id and be believed, because `verified-by` was built
            from that field."
    (let [{:keys [auth]} (cluster :test [:a :b :c])
          ;; :c signs honestly, then rewrites the envelope to claim it is :a.
          honest (<!! (auth/seal (:c auth) {:kind :vote :height 3} ctx))
          forged (assoc honest :from :a)]
      (is (nil? (<!! (auth/unseal (:b auth) forged)))
          "a signature over :c's identity does not authenticate :a"))))

(deftest a-sealed-envelope-survives-the-wire
  (testing "every other test here hands the envelope straight from `seal` to
            `unseal` inside one process, where a raw byte array is a perfectly
            good value. On the wire it is not: kabel serialises to EDN, and a
            `byte[]` prints as `#object[[B 0x...]`, which no reader reads back.
            The first authenticated websocket run died with `No reader function
            for tag object` and no peer assembled -- eight green unit tests and
            a completely broken transport."
    (let [{:keys [auth]} (cluster :test [:a :b])
          env (<!! (auth/seal (:a auth) {:kind :vote :height 3} ctx))
          on-the-wire (pr-str env)
          received (edn/read-string on-the-wire)]
      (is (not (re-find #"#object" on-the-wire))
          "nothing in the envelope is opaque to the printer")
      (is (= #{:a} (:verified-by (<!! (auth/unseal (:b auth) received))))
          "and it still verifies after a full round trip"))))

(deftest a-malformed-signature-is-refused-not-thrown
  (testing "anyone who can reach the port can put arbitrary bytes in this
            field, so garbage is an expected input. If decoding threw, the
            receive loop would die and the node would go deaf -- a remote kill
            switch dressed as a parse error."
    (let [{:keys [auth]} (cluster :test [:a :b])
          env (<!! (auth/seal (:a auth) {:kind :vote} ctx))]
      (is (nil? (<!! (auth/unseal (:b auth) (assoc env :sig "not base64 @@@@")))))
      (is (nil? (<!! (auth/unseal (:b auth) (assoc env :sig "")))))
      (is (nil? (<!! (auth/unseal (:b auth) (assoc env :sig 42))))))))

(deftest a-tampered-payload-is-refused
  (let [{:keys [auth]} (cluster :test [:a :b])
        env (<!! (auth/seal (:a auth) {:kind :vote :height 3} ctx))]
    (is (nil? (<!! (auth/unseal (:b auth) (assoc-in env [:msg :height] 4))))
        "the signature covers the payload, not just the author")))

(deftest an-unknown-author-is-refused-before-any-crypto-runs
  (let [{:keys [auth]} (cluster :test [:a :b])
        outsider (keypair)
        stranger (auth/authenticator {:chain :test :peer-id :zz
                                      :private-key (:private outsider)
                                      :public-keys {:zz (:public outsider)}} :zz)
        env (<!! (auth/seal stranger {:kind :vote :height 3} ctx))]
    (is (nil? (<!! (auth/unseal (:b auth) env)))
        "a perfectly valid signature from a non-member is still not a member")))

(deftest a-signature-does-not-cross-deployments
  (testing "domain separation. Without a chain in the signed bytes, a vote
            captured on a testnet replays into mainnet, and two deployments
            that can reach each other cross-contaminate. The audit found no
            domain separation anywhere in the codebase."
    (let [kp (keypair)
          pubs {:a (:public kp)}
          on-test (auth/authenticator {:chain :testnet :peer-id :a
                                       :private-key (:private kp) :public-keys pubs} :a)
          on-main (auth/authenticator {:chain :mainnet :peer-id :a
                                       :private-key (:private kp) :public-keys pubs} :a)
          env (<!! (auth/seal on-test {:kind :vote :height 3} ctx))]
      (is (some? (<!! (auth/unseal on-test env))) "valid on its own chain")
      (is (nil? (<!! (auth/unseal on-main env)))
          "and the identical bytes are worthless on another"))))

(deftest a-missing-signature-is-refused
  (let [{:keys [auth]} (cluster :test [:a :b])
        env (<!! (auth/seal (:a auth) {:kind :vote} ctx))]
    (is (nil? (<!! (auth/unseal (:b auth) (dissoc env :sig)))))
    (is (nil? (<!! (auth/unseal (:b auth) (assoc env :sig nil)))))))

(deftest unauthenticated-mode-verifies-nobody-and-says-so
  (testing "`:none` yields an EMPTY `verified-by`, not `#{from}`. An algorithm
            that checks it -- Tendermint and Bullshark do -- therefore rejects
            every message rather than being quietly satisfied by a forgeable
            claim. Opting out has to be visible in behaviour, not just in
            config."
    (let [a (auth/authenticator :none :a)
          env (<!! (auth/seal a {:kind :vote} ctx))
          opened (<!! (auth/unseal a env))]
      (is (= #{} (:verified-by opened)))
      (is (= {:kind :vote} (:msg opened))))))

(deftest a-partial-configuration-refuses-to-start
  (testing "a node that cannot verify its peers should refuse to start, not
            start and trust them"
    (is (thrown? clojure.lang.ExceptionInfo
                 (auth/authenticator {:peer-id :a :private-key (byte-array 32)} :a)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (auth/authenticator {:chain :c :peer-id :a :public-keys {}} :a)))
    (is (thrown? clojure.lang.ExceptionInfo (auth/authenticator nil :a)))))

;; ============================================================
;; Replay, redirection, and re-topicking
;; ============================================================

(deftest a-captured-message-cannot-be-replayed
  (testing "nothing in the signed bytes was fresh

           No nonce, no sequence, no timestamp. So any peer -- including one
           holding no key of its own -- could capture a signed message and
           re-present it, unboundedly often, at any later time. Most consensus
           messages are self-limiting by CONTENT (a prevote for height 5 is
           dropped at height 500), so this is not a forgery primitive; what it
           buys is unbounded verification work from an attacker with no
           credentials, and the stale-across-restart hazards that `raft.cljc`
           and `tendermint.cljc` each document as real.

           `:seq` is on the ENVELOPE rather than in the payload, which is what
           makes it compatible with retransmission: `do-broadcast` re-seals on
           every send, so a gossip re-broadcast already carries a new signature
           and simply gets a new number too. It touches no double-sign guard,
           because that protects vote CONTENT."
    (let [{:keys [auth]} (cluster :test [:a :b])
          env (<!! (auth/seal (:a auth) {:kind :vote :height 3} ctx))]
      (is (some? (<!! (auth/unseal (:b auth) env))) "accepted once")
      (is (nil? (<!! (auth/unseal (:b auth) env))) "and never again")
      (is (nil? (<!! (auth/unseal (:b auth) env))) "however many times it is tried"))))

(deftest retransmission-still-works-because-every-send-is-freshly-sealed
  (testing "the constraint that shaped the design. urd DELIBERATELY re-sends
            signed messages -- Tendermint's `gossip` re-broadcasts its own
            votes, and without that a single dropped prevote wedges a height
            forever. A naive reject-what-you-have-seen would have broken
            liveness under loss, which is a worse bug than the replay it stops."
    (let [{:keys [auth]} (cluster :test [:a :b])
          msg {:kind :vote :height 3}
          first-send  (<!! (auth/seal (:a auth) msg ctx))
          second-send (<!! (auth/seal (:a auth) msg ctx))]
      (is (not= (:seq first-send) (:seq second-send))
          "the same payload sealed twice gets two sequence numbers")
      (is (some? (<!! (auth/unseal (:b auth) first-send))))
      (is (some? (<!! (auth/unseal (:b auth) second-send)))
          "so an honest retransmission of the same message is still accepted"))))

(deftest messages-may-arrive-out-of-order
  (testing "a strict `>` would be simpler and would drop honest traffic: the
            simulator reorders deliberately and pubsub can too. The window is
            required, not an optimisation."
    (let [{:keys [auth]} (cluster :test [:a :b])
          envs (doall (for [i (range 5)]
                        (<!! (auth/seal (:a auth) {:kind :vote :n i} ctx))))]
      ;; Delivered newest-first.
      (doseq [e (reverse envs)]
        (is (some? (<!! (auth/unseal (:b auth) e)))
            "every one is accepted despite arriving backwards"))
      ;; And none of them a second time.
      (is (every? nil? (map #(<!! (auth/unseal (:b auth) %)) envs))))))

(deftest a-message-cannot-be-moved-to-another-topic-or-another-recipient
  (testing "`:to` rides on the envelope by design, so the transport can filter
            it -- and it was therefore not signed, along with the topic. A
            captured message could be re-delivered on a topic its author never
            used, or have `:to` rewritten to another peer, or stripped so that
            a message directed at one peer was accepted by every peer on the
            topic."
    (let [{:keys [auth]} (cluster :test [:a :b])
          env (<!! (auth/seal (:a auth) {:kind :catchup}
                              {:topic :recovery :to :b}))]
      (is (nil? (<!! (auth/unseal (:b auth) (assoc env :topic :consensus))))
          "another topic is another message")
      (is (nil? (<!! (auth/unseal (:b auth) (assoc env :to :c))))
          "and so is another recipient")
      (is (nil? (<!! (auth/unseal (:b auth) (dissoc env :to))))
          "including no recipient at all")
      (is (some? (<!! (auth/unseal (:b auth) env)))
          "while the envelope as sent is fine"))))

(deftest a-forged-sequence-number-cannot-lock-a-peer-out
  (testing "the window advances only on a VERIFIED message

           If `remember` ran before the signature check, anyone could send
           `{:from :a :seq 1000000}` and push :a's window so far forward that
           :a's own subsequent messages fell outside it -- silencing a
           validator with one unsigned packet, which is a denial of service
           dressed as replay protection."
    (let [{:keys [auth]} (cluster :test [:a :b])
          forged {:msg {:kind :vote} :from :a :topic :test-topic :to nil
                  :seq 1000000 :sig "not a signature"}]
      (is (nil? (<!! (auth/unseal (:b auth) forged))))
      (let [honest (<!! (auth/seal (:a auth) {:kind :vote} ctx))]
        (is (some? (<!! (auth/unseal (:b auth) honest)))
            "and :a can still be heard afterwards")))))

(deftest replay-registers-survive-restart-and-claim-once
  (let [kp (keypair)
        backend (store/memory-store)
        make-auth #(auth/authenticator {:chain :test :private-key (:private kp)
                                        :public-keys {:a (:public kp)}} % backend)
        first-env (<!! (auth/seal (make-auth :a) {:n 1} ctx))
        b (make-auth :b)
        claims (mapv (fn [_] (auth/unseal b first-env)) (range 8))]
    (is (= 1 (count (keep <!! claims))))
    (let [restarted (make-auth :b)
          second-env (<!! (auth/seal (make-auth :a) {:n 2} ctx))]
      (is (< (:seq first-env) (:seq second-env)))
      (is (nil? (<!! (auth/unseal restarted first-env))))
      (is (= {:n 2} (:msg (<!! (auth/unseal restarted second-env))))))))

(deftest missing-register-acknowledgement-prevents-delivery
  (let [{:keys [auth keys]} (cluster :test [:a :b])
        broken (reify store/ReplayStore
                 (update-replay! [_ _ _] (doto (chan) close!)))
        receiver (auth/authenticator {:chain :test :private-key (:private (:b keys))
                                      :public-keys {:a (:public (:a keys))}}
                                     :b broken)
        env (<!! (auth/seal (:a auth) {} ctx))]
    (is (::auth/store-error (ex-data (<!! (auth/unseal receiver env)))))))
