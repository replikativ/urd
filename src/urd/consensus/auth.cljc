(ns urd.consensus.auth
  "The verification edge: what makes `verified-by` mean something.

  ## What was here before

  Nothing. `node.cljc` states the contract -- \"`verified-by` is the set of
  peer-ids whose signature was checked at the edge; the state machine must
  never see an unverified signature\" -- and the edge did this:

      (let [sender (:sender msg)]
        (n/message-received sender msg #{sender}))

  `:sender` is a field the sending peer writes into its own message. So
  `verified-by` was the attacker's claim about who the attacker was, and
  Tendermint's identity guard `(contains? verified-by (:from msg))` was a
  tautology over two fields the same party controls. `urd.crypto` was required
  by four namespaces and called from none.

  Every Byzantine property this library proves was therefore conditional on an
  authenticated transport that did not exist. That is the hole this closes.

  ## Why it lives at the edge and not in the state machine

  Not a layering preference -- a constraint. ClojureScript's Web Crypto is
  promise-based, so Ed25519 verification returns a channel on that platform;
  `geheimnis` gives both platforms the same channel-returning contract so that
  one implementation works on each. A `step` is a pure function and cannot
  await a channel, so verification has to happen where there is already an
  async context: the network handler. The same reasoning puts konserve's async
  API at the store seam.

  This is why the protocol carries `verified-by` at all rather than passing
  signatures inward. The seam was right; only the implementation was missing.

  ## What is signed

  The canonical CBOR encoding of `{:chain :from :topic :to :seq :msg}` -- see
  `urd.wire` for why a signature covers RFC 8949 bytes rather than a
  Clojure-specific hash, and `digest` below for why each of those fields is in
  there.

  `:chain` is domain separation and is not optional. Without it a signature
  produced on a testnet verifies on mainnet, two deployments that can reach each
  other cross-contaminate, and a vote captured from one network replays into
  another. The audit found no domain separation anywhere in the codebase; this
  is where it goes, because this is the only place every message passes through.

  ## Why the signature is a string on the wire

  Ed25519 signatures are 64 raw bytes and `geheimnis` hands them over as a byte
  array. A byte array is not a wire format: kabel serialises messages as EDN,
  and a Java `byte[]` prints as `#object[[B 0x...]`, which no reader can read
  back. The first authenticated run over websockets died with \"No reader
  function for tag object\" and every peer silently failed to assemble.

  So `seal` base64-encodes and `unseal` decodes. The envelope is plain EDN --
  keywords, a uuid, a string -- which is the contract every other message in
  this library already meets.

  The unit tests did not catch this because they passed the envelope straight
  from `seal` to `unseal` in one process, where a byte array is a perfectly good
  value. `a-sealed-envelope-survives-the-wire` round-trips through the reader,
  because that is the thing that was actually broken.

  ## Refusing is a choice you have to make

  `authenticator` requires keys. Running without them requires passing
  `:none` explicitly. There is no permissive default, because a permissive
  default is precisely how the original hole survived: the machinery was
  described, the check was absent, and every test passed."
  (:require [org.replikativ.geheimnis.sign :as sign]
            [urd.crypto :as crypto]
            [urd.wire :as wire]
            [urd.consensus.store :as store]
            [superv.async :refer [go-try- <?-]]
            #?(:clj  [clojure.core.async :refer [go <!]]
               :cljs [clojure.core.async :refer [go <!]])))

(def window-size
  "How far out of order a message may arrive and still be accepted.

  A SET of recent sequence numbers per peer, not a bitmap. A 64-bit bitmap is
  the textbook implementation and is not portable here: ClojureScript's bit
  operations are 32-bit, and this project has already paid for that once --
  `rng.cljc` documents the day it lost to `(bit-and 0xFFFFFFFF 0xFFFFFFFF)`
  being -1 under cljs. A set of at most 33 small numbers per peer costs
  nothing and cannot be wrong on one platform only.

  A window at all, rather than a strict `>`, because messages legitimately
  arrive out of order: the simulator reorders deliberately and pubsub can too.
  A strict monotonic check would drop honest traffic, which is a worse failure
  than the replay it prevents."
  32)

(defn fresh?
  "Is `sq` a sequence number we have not already accepted from this peer?"
  [{:keys [highest seen] :or {highest -1 seen #{}}} sq]
  (and (integer? sq) (< 0 sq 9007199254740992)
       (> sq (- highest window-size))
       (not (contains? seen sq))))

(defn remember
  "Record `sq` as seen, discarding anything that has fallen out of the window."
  [{:keys [highest seen] :or {highest -1 seen #{}}} sq]
  (let [h     (max highest sq)
        floor (- h window-size)]
    {:highest h
     :seen    (into #{} (filter #(> % floor)) (conj seen sq))}))

(defn- digest
  "The bytes a signature covers. Deterministic across platforms.

  Covers the TOPIC and the RECIPIENT as well as the payload, and carries a
  per-sender SEQUENCE number, because none of those were signed and each is a
  thing an attacker could change on a captured message:

    :topic  re-deliver a message on a topic its author never used
    :to     re-address a directed message, or strip `:to` so a message meant
            for one peer is accepted by every peer on the topic
    :seq    replay the same message forever, from any peer, at any later time

  `:seq` lives on the ENVELOPE rather than in the payload, and that is what
  makes it compatible with retransmission. urd deliberately re-sends signed
  messages -- Tendermint's `gossip` re-broadcasts its own votes, and its
  docstring notes that re-sending an already-signed message is not a second
  signature. `do-broadcast` calls `seal` afresh on every send, so a
  retransmission already produces a new signature; giving it a new sequence
  number costs nothing and touches no double-sign guard, which protects vote
  CONTENT rather than envelopes."
  [chain from topic to sq msg]
  (let [payload {:chain chain :from from :topic topic :to to :seq sq :msg msg}]
    ;; Canonical CBOR, not `hasch/edn-hash`. Ed25519 takes an arbitrary-length
    ;; message, so there is nothing to pre-hash: the encoded bytes ARE what is
    ;; signed, and a client in any language reproduces them from a published
    ;; specification rather than from replikativ's value model.
    ;;
    ;; This also retires a platform bug worth remembering, because the shape of
    ;; it recurs. The cljs branch used to build the message with `into-array`,
    ;; which yields a plain JS Array, and Web Crypto refuses one:
    ;;
    ;;   TypeError: Failed to execute 'verify' on 'SubtleCrypto':
    ;;   3rd argument is not instance of ArrayBuffer, Buffer, TypedArray, or
    ;;   DataView
    ;;
    ;; So every signed message was JVM-only, in a library that advertises
    ;; clj+cljs and whose whole reason for verifying at the async edge is that
    ;; ClojureScript's Web Crypto is promise-based. It survived because the
    ;; cljs runner covered five portability namespaces and none of them signed.
    ;; `boring` returns the platform's own byte container on each side, so the
    ;; question does not arise again here -- but `urd.auth-probe` still signs
    ;; under cljs, and that test is the reason this stays honest.
    (wire/signing-bytes payload)))

(defn- try-verify
  "Verify. Anything that is not literally `true` is a failure.

  `true?` and not truthiness, and this is the whole point of the function.
  `geheimnis` follows the superv convention: a malformed key or signature does
  not throw, it puts the ExceptionInfo ON the channel. An exception object is
  truthy. So the obvious

      (when (<! (sign/verify pk bytes sig)) ...)

  accepts every malformed signature, and `:sig \"\"` -- three bytes on the wire,
  no key material, no work -- authenticates as any peer whose public key we
  hold. That is a total bypass of the thing this namespace exists to do, and it
  is reachable by anyone who can open a socket.

  The `try/catch` is the second layer, for base64 that fails to decode before
  the channel is ever involved."
  [pk bytes sig]
  (go (try
        (true? (<! (sign/verify pk bytes (crypto/base64->bytes sig))))
        (catch #?(:clj Exception :cljs :default) _ false))))

(defprotocol MessageAuth
  (seal [this msg ctx]
    "Attach this node's identity, a fresh sequence number, and a signature.

     `ctx` is `{:topic t :to peer-or-nil}` -- what the transport is about to do
     with this message. Both are SIGNED, so neither can be changed in flight.
     Returns a channel of the envelope to put on the wire.")
  (unseal [this envelope]
    "Check the envelope. Returns a channel of `{:from id :msg m :verified-by s}`
     when it is good, or of nil when it is not -- a message that fails is not an
     error to report, it is a packet that never happened.

     Three ways to fail: an unknown author, a signature that does not verify,
     and a sequence number this peer has already used. The last is STATEFUL, so
     an authenticator is not a value you can share between nodes."))

(defn- update-register! [registers key f]
  (go-try-
   (try
     (let [result (<?- (store/update-replay! registers key f))]
       (when-not (and (vector? result) (= 2 (count result))
                      (= (second result) (f (first result))))
         (throw (ex-info "Invalid replay register acknowledgement" {})))
       result)
     (catch #?(:clj Exception :cljs :default) e
       (throw (ex-info "Could not persist authentication state" {::store-error true} e))))))

(defrecord Ed25519Auth [chain peer-id private-key public-keys registers windows]
  MessageAuth

  (seal [_ msg {:keys [topic to]}]
    (go-try-
     (let [[_ sq] (<?- (update-register! registers [chain peer-id :send]
                                         (fnil inc 0)))
           _ (when (> sq 9007199254740991)
               (throw (ex-info "Envelope sequence exhausted" {:peer-id peer-id})))
           sig (<?- (sign/sign private-key (digest chain peer-id topic to sq msg)))]
       {:msg msg :from peer-id :topic topic :to to :seq sq
        :sig (crypto/bytes->base64 sig)})))

  (unseal [_ {:keys [msg from topic to sig] sq :seq}]
    (go-try-
     (when-let [pk (get public-keys from)]
       (when (and (string? sig) (integer? sq) (< 0 sq 9007199254740992)
                  (fresh? (get @windows from) sq)
                  (<! (try-verify pk (digest chain from topic to sq msg) sig)))
         (let [[before after] (<?- (update-register!
                                    registers [chain peer-id :receive from]
                                    (fn [window]
                                      (if (fresh? window sq) (remember window sq) window))))]
           (swap! windows assoc from after)
           (when (fresh? before sq)
             {:from from :msg msg :verified-by #{from}})))))))

(defrecord NoAuth [peer-id]
  MessageAuth
  ;; The claimed identity is still carried. Unauthenticated mode means we do
  ;; not VOUCH for it, not that we discard it -- an algorithm that reasons
  ;; about who sent a message still needs to know who says they did. Dropping
  ;; it made every message appear to come from the same placeholder peer, so
  ;; round-robin's proposer check compared a real id against a constant and no
  ;; proposal was ever valid.
  (seal [_ msg {:keys [topic to]}]
    (go {:msg msg :from peer-id :topic topic :to to :sig nil}))
  (unseal [_ {:keys [msg from]}]
    ;; `verified-by` is EMPTY, not `#{from}`. An algorithm that checks it -- as
    ;; Tendermint and Bullshark do -- therefore rejects every message rather
    ;; than being silently satisfied by a forgeable claim. Unauthenticated mode
    ;; is for a trusted in-process network, and it should visibly not work for
    ;; anything that depends on identity.
    (go {:from from :msg msg :verified-by #{}})))

(defn authenticator
  "Build the verification edge.

  `config` is either `:none` -- an explicit, deliberate opt-out for in-process
  and simulated networks -- or a map. `peer-id` is who we are, used when the
  config does not name us.

  The map form:

    :chain        an identifier for this deployment. REQUIRED; see the
                  namespace docstring on why a signature that does not name its
                  network is a replay waiting to happen.
    :peer-id      who we are
    :private-key  32-byte Ed25519 seed
    :public-keys  {peer-id 32-byte-public-key} for everyone we will believe

  Throws on a partial configuration. A node that cannot verify its peers should
  refuse to start, not start and trust them."
  ([config peer-id] (authenticator config peer-id (store/memory-store)))
  ([config peer-id backend]
   (cond
     (= :none config) (->NoAuth peer-id)

     (map? config)
     (let [{:keys [chain private-key public-keys]} config
           peer-id (or (:peer-id config) peer-id)]
       (when-not (and chain peer-id private-key (seq public-keys))
         (throw (ex-info (str "auth needs :chain, :peer-id, :private-key and "
                              ":public-keys -- or :none to opt out deliberately")
                         {:missing (remove #(get config %)
                                           [:chain :peer-id :private-key :public-keys])})))
      ;; The counter and the replay windows are STATE, so an authenticator
      ;; belongs to exactly one node. Sharing one between peers in a test would
      ;; make them share a sequence space and reject each other's traffic.
       (let [registers (or (:replay-store config) backend)]
         (when-not (satisfies? store/ReplayStore registers)
           (throw (ex-info "Ed25519 requires a ReplayStore via :store or :auth :replay-store" {})))
         (->Ed25519Auth chain peer-id private-key public-keys registers (atom {}))))

     :else
     (throw (ex-info "auth must be a config map or :none" {:got config})))))

(defn generate-keypair
  "A fresh Ed25519 keypair. Returns a channel of `{:public :private}`.

  Here rather than in `urd.crypto` because that namespace's ClojureScript
  branch throws \"not yet implemented\" for every primitive, which makes it
  unusable for the one platform this seam exists to support."
  []
  (sign/generate-keypair))
