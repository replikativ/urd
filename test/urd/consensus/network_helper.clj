(ns urd.consensus.network-helper
  "Helper functions for creating test networks of validators."
  (:require [clojure.core.async :refer [<! <!! alts! timeout]]
            [superv.async :refer [S <?? <?- go-try-]]
            [urd.consensus.network :as net]
            [urd.consensus.auth :as auth]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.validator :as validator]))

(defn create-test-validator-set
  "Create a test validator set with N validators."
  [n]
  (into {}
        (map (fn [i]
               [(java.util.UUID/randomUUID) (str "pubkey-" i)])
             (range n))))

(defn create-test-proposal
  "Create a test proposal for consensus."
  [validator-id counter]
  {:snapshot-id (java.util.UUID/randomUUID)
   :data (str "Proposal-" validator-id "-" counter)
   :timestamp (System/currentTimeMillis)})

(defn start-kabel-network!
  "Helper to start a network of validators using Kabel P2P.

  Args:
    n - Number of validators
    opts - Options map:
      :base-port - Starting port (default 47300)
      :on-propose - (fn [validator-id]) -> proposal (required)
      :on-finalize - (fn [validator-id proposal height]) (optional)

  Returns:
    Channel yielding map with:
      :validators - Vector of Validator instances
      :validator-set - The validator set used
      :validator-ids - Vector of validator IDs"
  [n opts]
  ;; REAL Ed25519 keys, not `:auth :none`. These validators talk over
  ;; websockets, which is exactly the setting where `verified-by` used to be
  ;; the sender's own claim about itself, so this is the only place the
  ;; authenticated path is exercised end to end.
  ;;
  ;; Generated OUTSIDE the go block, with a blocking take. `<!` inside a
  ;; `(fn [id] ...)` nested in a `go` does not park -- the macro only rewrites
  ;; its own body, not nested functions -- so it silently produced nils, every
  ;; auth config was invalid, and the network came up with no validators at
  ;; all. The symptom was three assertions quietly not running and an
  ;; ArityException from `(apply = [])` forty lines later.
  (let [validator-set (create-test-validator-set n)
        validator-ids (vec (keys validator-set))
        keys-by-id (into {} (map (fn [id] [id (<!! (auth/generate-keypair))]))
                         validator-ids)
        public-keys (into {} (map (fn [[id kp]] [id (:public kp)])) keys-by-id)
        auth-for (fn [id] {:chain :urd-test
                           :peer-id id
                           :private-key (:private (get keys-by-id id))
                           :public-keys public-keys})]
    (go-try-
     (let [base-port (or (:base-port opts) 47300)
           server-url (str "ws://localhost:" base-port)
           on-propose (:on-propose opts)
                 ;; `(fn [validator-id validator-set] node)`, so a caller can
                 ;; wrap each validator's node -- with `trace/tracing`, for
                 ;; instance. The SET is passed because a node needs it and the
                 ;; runtime config does not carry it: building `(rr/create)`
                 ;; with no validator set gives an empty one, and the first
                 ;; timer tick then divides by zero deep inside
                 ;; `get-proposer-id`, killing the event loop. That cost real
                 ;; time -- it looked exactly like the tracing wrapper hanging
                 ;; every node.
           node-fn (:node-fn opts)
           on-finalize (:on-finalize opts)

          ;; Start server validator
           server-id (nth validator-ids 0)
                 ;; round-robin refuses to start without a vote verifier. Its
                 ;; `:vote-bundle` and `:catchup` messages RELAY other nodes'
                 ;; votes, so the peer handing one over is usually not its
                 ;; author and a bare name is the relayer's claim rather than
                 ;; evidence about the voter.
           atts (rr/test-attestations)

           server-config {:peer-id server-id
                          :auth (auth-for server-id)
                          :sign-vote (:sign-vote atts)
                          :verify-vote (:verify-vote atts)
                          :validator-set validator-set
                          :network-type :kabel
                          :port base-port
                          :node (when node-fn (node-fn server-id validator-set))
                          :on-propose (fn [] (on-propose server-id))
                          :on-finalize (when on-finalize
                                         (fn [p h] (on-finalize server-id p h)))}

           server (<?- (validator/start-validator! server-config))

          ;; Wait for server to be ready
           _ (<! (timeout 1000))

          ;; Start client validators
           clients (loop [i 1, cs []]
                     (if (< i n)
                       (let [vid (nth validator-ids i)
                             client-config {:peer-id vid
                                            :auth (auth-for vid)
                                            :sign-vote (:sign-vote atts)
                                            :verify-vote (:verify-vote atts)
                                            :validator-set validator-set
                                            :network-type :kabel
                                            :connect-to server-url
                                            :node (when node-fn (node-fn vid validator-set))
                                            :on-propose (fn [] (on-propose vid))
                                            :on-finalize (when on-finalize
                                                           (fn [p h] (on-finalize vid p h)))}
                             client (<?- (validator/start-validator! client-config))
                             _ (<! (timeout 500))]
                         (recur (inc i) (conj cs client)))
                       cs))]

      ;; Wait until the SERVER can see every client, rather than sleeping and
      ;; hoping. `get-peer-count` now reports the pubsub subscriber count -- it
      ;; used to be a stub returning 1, i.e. a readiness predicate that always
      ;; said "ready" -- so this is a condition and no longer a guess.
      ;;
      ;; The failure it prevents is silent: a client that has not finished
      ;; connecting simply is not in the network, and because a majority of the
      ;; remainder is still a quorum the others reach consensus without it. That
      ;; looks like a consensus bug and is not one.
       (let [deadline (+ (System/currentTimeMillis) 30000)]
         (loop []
           (let [seen (<?- (net/get-peer-count (:network @(:state server))))]
             (cond
               (>= seen n) true
               (> (System/currentTimeMillis) deadline)
               (throw (ex-info "kabel network did not assemble"
                               {:type :network-incomplete :expected n :seen seen}))
               :else (do (<! (timeout 100)) (recur))))))

       {:validators (into [server] clients)
        :validator-set validator-set
        :validator-ids validator-ids}))))

(defn stop-network!
  "Stop all validators in a network.

  Each validator's shutdown is BOUNDED. The hang that motivated this has since
  been found and fixed -- `close-network!` was sending a pubsub unsubscribe
  before stopping the peer, and that is a parking put on a channel whose
  consumer the server's earlier shutdown had already taken away -- so this
  bound should now never fire.

  It stays anyway, because of what an unbounded hang costs: no test result at
  all. The suite is killed from outside and reports nothing, which is how a
  passing run and a broken one become indistinguishable, and it is why that
  bug survived as long as it did. A bound turns a future hang into a failure
  with a name attached.

  Returns a channel yielding true, or a vector of the validators that would not
  stop.

  Args:
    network - Map returned from start-kabel-network!"
  [network]
  (go-try-
   (let [stuck (loop [vs (:validators network), stuck []]
                 (if-let [v (first vs)]
                   (let [done (validator/stop-validator! v)
                         [_ port] (alts! [done (timeout 10000)])]
                     (recur (rest vs)
                            (if (= port done) stuck (conj stuck (:peer-id v)))))
                   stuck))]
     (when (seq stuck)
       (println "WARNING: validators would not stop within 10s:" stuck))
     (if (seq stuck) stuck true))))

(defn start-all-consensus!
  "Start consensus on all validators in a network.

  Args:
    network - Map returned from start-kabel-network!"
  [network]
  (doseq [v (:validators network)]
    (validator/send-event! v {:type :start-round})))

(defn get-all-finalized
  "Get finalized heights from all validators.

  Returns:
    Vector of maps with :validator-id and :finalized"
  [network]
  (mapv (fn [v]
          {:validator-id (:peer-id v)
           :finalized (validator/get-finalized v)})
        (:validators network)))
