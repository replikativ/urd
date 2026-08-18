(ns urd.consensus.attest
  "Real vote attestations, and the commit certificates built from them.

  Every algorithm here takes its attestation scheme as configuration -- a
  `{:sign-vote :verify-vote}` pair -- and each one ships a `test-attestations`
  that is a hash of the voter and the payload. Those are labelled NOT
  CRYPTOGRAPHY in capitals and they mean it: anyone who can read the namespace
  can mint a vote for any validator. They exist to give tests the SHAPE, and
  `round-robin`'s `init` refuses to start without a scheme precisely so the
  stub cannot be reached by accident. This namespace is the thing `init` is
  waiting for.

  ## What an attestation is, and why it is not message authentication

  `urd.consensus.auth` already signs every message on the wire, and it is not
  enough. It proves who SENT a message; an attestation must prove who VOTED,
  and those separate the moment a vote is relayed. `answer-want-votes` exists
  to hand one peer another peer's votes, and `record-vote`'s docstring records
  what happened when votes were bare names: `:vote-bundle` and `:catchup`
  amounted to \"here are the validators I say voted\", and one peer could hand
  us a quorum it invented. An attestation is what makes a vote transferable
  through a party nobody trusts.

  ## The seam is `(voter payload)`, and the payload must bind the height

  Tendermint already took a payload -- `[height round value-id]` -- and its
  docstring gives the argument: without the height a signature replays at every
  later height, without the round it replays across rounds of the same height.
  Round-robin signed a bare `proposal-id`, which is NOT height-bound. That is
  safe only as long as a proposal id never repeats, and a proposal id may be a
  `snapshot-id` is a \"UUID or content-hash\" -- under the content-hash reading,
  proposing the same value at two heights yields the same id, and a vote cast
  at the first is a valid vote at the second. Round-robin now signs
  `[height proposal-id]`; Bullshark needs no change because `header-id` already
  digests the author and round along with the content.

  This namespace never looks inside a payload. It signs whatever the algorithm
  says a vote covers, which is what lets one implementation serve all three.

  ## Canonical CBOR, so a certificate is checkable off-platform

  An attestation covers `(wire/signing-bytes {:kind :urd/vote ...})` -- the same
  RFC 8949 encoding a transaction signature covers, for the same reason: a
  light client that wants to check that height H was really decided should not
  have to be written in Clojure to do it. `doc/interop/verify_certificate.py` verifies one.

  `:kind` is a discriminator. The vote payload and the transaction payload
  already have disjoint key sets, so their encodings could not collide anyway,
  but a security property that holds by accident of field naming is one field
  rename away from not holding.

  ## Signing is synchronous here, and that is checked rather than assumed

  `geheimnis` returns channels on both platforms because ClojureScript's Web
  Crypto is promise-based. The `sign-vote`/`verify-vote` seam is synchronous and
  sits inside pure state-machine transitions, so it cannot await anything.

  On the JVM this is a non-problem: `geheimnis` computes eagerly and puts the
  result on a buffered channel before returning it, so the value is already
  there. Rather than assume that, `now!` uses `poll!` -- which never parks --
  and throws if the channel is not ready. If geheimnis ever becomes genuinely
  asynchronous on the JVM, this fails loudly at the first vote instead of
  deadlocking a consensus round inside a go block.

  On ClojureScript there is no synchronous path at all: Web Crypto is
  promise-only and the `@noble/ed25519` fallback that `geheimnis/set-fallback!`
  takes is used through `verifyAsync`. So `attestations` refuses to build under
  ClojureScript rather than quietly returning something weaker. That is not a
  portability gap being papered over -- validators run on the JVM, and the part
  a browser or Node client actually needs is `verify-certificate`, which is
  asynchronous, portable, and tested under both runners.

  Making this seam portable means a synchronous Ed25519 verify for
  ClojureScript, which noble can do when handed a synchronous SHA-512. That is
  an upstream change to geheimnis and is recorded in the backlog."
  (:require [clojure.core.async :as a :refer [go <!]]
            [org.replikativ.geheimnis.sign :as sign]
            [urd.wire :as wire]))

;; ============================================================
;; What a vote covers
;; ============================================================

(defn vote-bytes
  "The bytes an attestation by `voter` over `payload` covers.

  `payload` is opaque and algorithm-defined: round-robin's `[height
  proposal-id]`, Tendermint's `[height round value-id]`, Bullshark's
  `header-id`. Whatever it is, it must already identify the vote uniquely --
  see the namespace docstring on what a payload that omits the height buys an
  attacker."
  [chain voter payload]
  (wire/signing-bytes {:kind :urd/vote :chain chain :voter voter :payload payload}))

;; ============================================================
;; The synchronous seam
;; ============================================================

#?(:clj
   (defn- now!
     "The value on `ch`, which must ALREADY be there.

     `poll!` rather than `<!!`: a blocking take inside a go block starves
     core.async's dispatch pool, and these run inside pure transitions that the
     runtime calls from exactly there. `poll!` cannot park, so the worst case is
     this exception rather than a consensus round that never returns.

     A nil poll means geheimnis stopped resolving eagerly on the JVM. That is a
     real possibility worth naming in the message, because the symptom
     otherwise -- votes that fail to sign, at one validator, under load -- is
     nothing like the cause."
     [ch what]
     (let [v (a/poll! ch)]
       (cond
         (nil? v)
         (throw (ex-info (str "geheimnis did not resolve " what " synchronously. "
                              "The attestation seam is synchronous because it runs "
                              "inside pure state-machine transitions; see "
                              "urd.consensus.attest.")
                         {:op what}))
         ;; superv's convention: a malformed key or signature is PUT on the
         ;; channel rather than thrown. `urd.consensus.auth/try-verify` records
         ;; what accepting a truthy exception costs -- every malformed
         ;; signature verifies, and `:sig ""` authenticates as anyone.
         (instance? #?(:clj Throwable :cljs js/Error) v)
         (throw (ex-info (str "geheimnis failed to " what) {:op what} v))

         :else v))))

(defn attestations
  "A real Ed25519 attestation scheme: `{:sign-vote :verify-vote}`.

  Config:

    :chain        this deployment's identifier. REQUIRED. Without it a vote
                  signed on a testnet is a valid vote on mainnet, which is the
                  same argument `urd.consensus.auth` makes about messages.
    :peer-id      who we are. We can only sign as ourselves.
    :private-key  32-byte Ed25519 seed
    :public-keys  `{voter 32-byte-public-key}` for every validator we will
                  believe a vote from

  Drop-in for any algorithm's `test-attestations`. Throws on a partial config
  -- a validator that cannot check its peers' votes should refuse to start
  rather than start and count them.

  `verify-vote` returns `true` or `false` and never throws: it is called on
  attacker-supplied bytes from inside a state machine, and a malformed
  signature is a vote to ignore, not a node to crash. An UNKNOWN voter is false
  for the same reason, though `record-vote` has already checked the validator
  set by the time this runs."
  [{:keys [chain peer-id private-key public-keys]}]
  #?(:cljs
     (throw (ex-info (str "urd.consensus.attest/attestations is JVM-only: the "
                          "sign/verify seam is synchronous and ClojureScript "
                          "has no synchronous Ed25519. Use verify-certificate, "
                          "which is asynchronous and portable.")
                     {:platform :cljs
                      :chain chain :peer-id peer-id}))
     :clj
     (do
       (when-not (and chain peer-id private-key (seq public-keys))
         (throw (ex-info (str "attestations needs :chain, :peer-id, :private-key "
                              "and :public-keys")
                         {:missing (remove #(get {:chain chain :peer-id peer-id
                                                  :private-key private-key
                                                  :public-keys public-keys} %)
                                           [:chain :peer-id :private-key :public-keys])})))
       {:sign-vote
        (fn sign-vote [voter payload]
          ;; We hold one private key. Being asked to sign as somebody else is a
          ;; caller bug, and a silent self-signature under their name would be
          ;; a vote that verifies against the wrong key and is dropped far from
          ;; here.
          (when-not (= voter peer-id)
            (throw (ex-info "cannot sign a vote as another validator"
                            {:asked-for voter :we-are peer-id})))
          (now! (sign/sign private-key (vote-bytes chain voter payload)) "sign"))

        :verify-vote
        (fn verify-vote [voter payload att]
          (boolean
           (when-let [pk (get public-keys voter)]
             (and (some? att)
                  (try
                    (true? (now! (sign/verify pk (vote-bytes chain voter payload) att)
                                 "verify"))
                    (catch Throwable _ false))))))})))

;; ============================================================
;; Commit certificates
;; ============================================================

(defn generate-keypair
  "A fresh Ed25519 keypair for a validator. Returns a channel of
  `{:public :private}`.

  Re-exported here so that configuring a validator's VOTE key does not require
  reaching into `urd.consensus.auth`, whose keypairs are for a different job --
  that one authenticates the peer on the wire, this one signs votes. They may
  be the same key in a deployment, and separating the two entry points is what
  leaves that a choice rather than an assumption baked into the imports."
  []
  (sign/generate-keypair))

(defn byzantine-quorum-size
  "floor(2n/3) + 1 -- the threshold a CERTIFICATE must meet.

  Deliberately NOT `round-robin/quorum-size`, which is a crash-fault majority
  of floor(n/2)+1. The two differ from n=5 on and are supposed to: round-robin
  is a CFT reference algorithm deciding locally among peers it assumes are
  merely slow, while a certificate is a claim made TO A STRANGER under an
  adversarial assumption, where the property that matters is that two quorums
  intersect in more than f members.

  `quorum-thresholds-are-intentionally-different` in the generative tests pins
  the distinction so that nobody 'fixes' one to match the other. That test used
  to compute this inline, because the previous home for it -- `urd.crypto` --
  was an uncalled certificate layer that was deleted."
  [n]
  (inc (quot (* 2 n) 3)))

(defn certificate
  "A portable, third-party-checkable proof that `payload` was decided.

  `votes` is `{voter attestation}`, exactly as an algorithm accumulates it --
  round-robin's `(get (:votes state) proposal-id)`, and what it already
  broadcasts on `:finalizations`.

  ## There is no `:height` field, on purpose

  The obvious shape carries `{:chain :height :payload :votes}`, and it is
  wrong. Only `:payload` is covered by the signatures, so a `:height` beside it
  is a number an attacker rewrites freely -- and a verifier that returned
  `:valid? true` next to an attacker's height would be worse than one that
  never mentioned the height at all, because a caller would read it.

  The height belongs INSIDE the payload, which is exactly why round-robin's
  payload is now `[height proposal-id]` rather than a bare id. A caller that
  wants the height reads it from there, where the validators signed it. `:chain`
  is carried because it is signed too -- `vote-bytes` covers it -- so the
  verifier can be handed nothing but the certificate and the validator set."
  [{:keys [chain payload votes]}]
  {:kind :urd/commit-certificate
   :chain chain
   :payload payload
   :votes votes})

(defn verify-certificate
  "Check a certificate against `public-keys`. Returns a CHANNEL.

  Asynchronous, and therefore portable: this is the half of the attestation
  story a browser or Node light client actually needs, and Web Crypto gives it
  no synchronous option. Validators do not call this -- they verify each vote
  as it arrives, synchronously, through `verify-vote`.

  Returns `{:valid? bool :voters #{...} :quorum n :of n}`, not a bare boolean:
  a certificate one signature short of quorum and a certificate signed by
  nobody are different situations, and a caller that can only see `false`
  cannot tell them apart.

  Counts DISTINCT voters that are in `public-keys` and whose attestation
  verifies over this certificate's own `:chain` and `:payload`. A voter outside
  the set contributes nothing however well-formed its signature, which is what
  stops an attacker who mints keys freely from manufacturing a quorum."
  [{:keys [chain payload votes]} public-keys
   & [{:keys [quorum-size] :or {quorum-size byzantine-quorum-size}}]]
  (go
    (let [n (count public-keys)
          needed (quorum-size n)
          valid (loop [pairs (seq votes) acc #{}]
                  (if-not pairs
                    acc
                    (let [[voter att] (first pairs)
                          pk (get public-keys voter)
                          ok? (and pk (some? att)
                                   (let [v (<! (sign/verify
                                                pk (vote-bytes chain voter payload) att))]
                                     ;; superv puts a malformed key or signature
                                     ;; ON the channel. An exception object is
                                     ;; truthy, so `true?` and not truthiness --
                                     ;; see `urd.consensus.auth/try-verify`,
                                     ;; where taking the obvious route made
                                     ;; every malformed signature verify.
                                     (true? v)))]
                      (recur (next pairs) (cond-> acc ok? (conj voter))))))]
      {:valid? (>= (count valid) needed)
       :voters valid
       :quorum needed
       :of n})))
