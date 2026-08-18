(ns urd.auth-probe
  "Does a signature over urd's digest actually work on ClojureScript?

  `urd.consensus.auth/digest` builds the signed bytes as

      #?(:clj (byte-array (hasch/edn-hash payload))
         :cljs (into-array (hasch/edn-hash payload)))

  and nothing in the suite has ever run that cljs branch: the runner covers
  five portability namespaces and none of them signs anything. kabel's
  `identity.cljc` carries a helper written specifically because a signature
  computed over these bytes has to verify on the other platform. This probe
  exists to find out whether urd needs the same care."
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])
            [hasch.core :as hasch]
            [urd.consensus.auth :as auth]
            [org.replikativ.geheimnis.sign :as sign]
            #?(:clj [clojure.core.async :refer [go <! <!!]]
               :cljs [cljs.core.async :refer [go <!]])
            #?(:cljs [cljs.core.async.interop :refer-macros [<p!]])))

(def payload {:chain :probe :from "peer" :topic "t" :to nil :seq 1 :msg {:v 42}})

(defn digest-bytes []
  #?(:clj (byte-array (hasch/edn-hash payload))
     :cljs (js/Uint8Array.from (into-array (hasch/edn-hash payload)))))

(deftest the-digest-is-unsigned-on-both-platforms
  (testing "hasch/edn-hash already maps negatives to 0-255, so the VALUES
            agree across platforms. What may not agree is the container."
    (let [h (hasch/edn-hash payload)]
      (is (every? #(and (>= % 0) (<= % 255)) h)
          "every element is an unsigned byte value")
      (is (= 64 (count h)) "sha-512"))))

#?(:clj
   (deftest a-signature-round-trips-on-this-platform
     (let [kp (<!! (sign/generate-keypair))
           d (digest-bytes)
           sig (<!! (sign/sign (:private kp) d))]
       (is (true? (<!! (sign/verify (:public kp) d sig)))))))

#?(:cljs
   (deftest ^:async a-signature-round-trips-under-clojurescript
     (testing "THE untested path. `into-array` yields a JS Array, not a
               Uint8Array, and geheimnis's cljs signer goes to Web Crypto or
               noble — both of which are particular about buffer types. If this
               fails, every signed urd message is JVM-only and the portability
               claim stops at the crypto."
       (async done
              (go
                (let [kp (<! (sign/generate-keypair))
                      d (digest-bytes)
                      sig (<! (sign/sign (:private kp) d))
                      ok (<! (sign/verify (:public kp) d sig))]
                  (is (true? ok) (str "verify returned " (pr-str ok)))
                  (done)))))))

#?(:cljs
   (deftest ^:async sealing-and-unsealing-round-trips-under-clojurescript
     (testing "the REAL api, not a copy of its digest. `seal` and `unseal` are
               what every message on the wire goes through, and until now
               nothing had ever run them on this platform."
       (async done
              (go
                (let [kp (<! (sign/generate-keypair))
                      me :peer-a
                      a (auth/authenticator {:chain :probe :peer-id me
                                             :private-key (:private kp)
                                             :public-keys {me (:public kp)}}
                                            me)
                      env (<! (auth/seal a {:v 42} {:topic "t" :to nil}))
                      got (<! (auth/unseal a env))]
                  (is (some? got) "a sealed envelope must unseal")
                  (is (= {:v 42} (:msg got)))
                  (is (= #{me} (:verified-by got))
                      "and the sender must be vouched for, not merely claimed")
                  (done)))))))
