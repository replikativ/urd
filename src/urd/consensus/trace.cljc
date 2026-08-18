(ns urd.consensus.trace
  "A tracing wrapper for any `urd.consensus.node/Node`.

  ## Why a wrapper and not instrumentation

  avalanchego does exactly this: `chains/manager.go` builds its consensus and
  then wraps it -- `smcon.Trace(consensus, tracer)` -- so tracing is a decorator
  around the interface rather than calls scattered through the algorithm. The
  same shape works here and buys three things:

  - **No algorithm changes.** All seven implementations are traceable without
    touching one of them.
  - **It works under BOTH interpreters.** The simulator and the kabel runtime
    take a `Node`, so they take a traced `Node`. That matters more than it
    sounds: the simulator already had a `:trace` and the real runtime had
    nothing, so every problem in the network layer had to be debugged by
    starting a network, sleeping, and inspecting state -- which is guessing with
    extra steps. A debugging affordance that exists in only one interpreter is
    one you cannot use where the bugs are.
  - **It composes with capabilities.** A wrapper reports what it wraps, exactly
    as the test adversaries do.

  ## What it records

  One entry per `step`, with the input's type, the KINDS of effects that came
  out, and a sequence number:

      {:seq 41 :peer :b :in :message-received :out [:broadcast :set-timer]}

  Kinds rather than whole effects, deliberately: a full effect log is enormous
  and unreadable, and the question a trace has to answer first is always
  \"is this node receiving anything at all, and does it react?\". Pass
  `:detail? true` for the whole event and effect vector when the answer to that
  is yes and the next question is why.

  ## Backends

  The entries go to an in-memory ring buffer, and optionally to `:sink`, a
  function of one entry. Two different jobs:

  - the ring buffer is for TEST ASSERTIONS and post-hoc inspection -- the
    simulator's own `:trace` is already used that way, and Bullshark's
    `revert-mismatch` assertions depend on it;
  - the sink is for watching a live run. `replikativ.logging` is the natural
    one, since it is a trove facade taking a namespaced keyword id for
    structured filtering and is already the house style:

        (trace/tracing node {:sink #(rlog/trace :urd.consensus/step %)})

  It is not a dependency here. The trace should not require a logging backend
  to be useful, and which backend to depend on is a project decision rather than
  this namespace's.

  ## A false alarm, recorded because the shape recurs

  This namespace carried a do-not-use-over-kabel warning for one commit. It
  was wrong. Traced over kabel, five validators produce 67 to 97 events each,
  receive messages, fire timers and commit -- the wrapper is transparent under
  both interpreters, as a decorator has to be.

  What actually happened: the diagnostic built its nodes as `(rr/create)` with
  NO validator set, and the runtime config carries neither `:validator-set` nor
  `:validators` through to `init`, so every node came up with an empty set. The
  first timer tick then reached `get-proposer-id`, which computes
  `(mod height (count validator-ids))` and divided by zero, and the exception
  killed the event loop inside a go block where nothing surfaced it. Every node
  showed exactly one traced event and then silence -- which reads precisely like
  a wrapper that hangs.

  Two lessons, and the second is the one worth keeping. An exception inside a
  core.async loop is invisible unless something reports it. And a tool built to
  diagnose a problem is itself untested code: the first output of a new
  instrument says as much about the instrument as about the system, and should
  be treated that way until it has been checked against a known-good control."
  (:require [urd.consensus.node :as n]))

(def default-limit
  "Entries kept per node. A ring buffer rather than an unbounded vector: a live
  node runs for hours, and the interesting part of a trace is nearly always the
  end."
  512)

(defn- record! [{:keys [entries limit sink]} entry]
  (swap! entries (fn [v] (let [v (conj v entry)]
                           (if (> (count v) limit) (subvec v (- (count v) limit)) v))))
  (when sink (sink entry))
  entry)

(defrecord Tracing [inner state]
  n/Node

  ;; What it wraps. This wrapper OBSERVES rather than rewrites, so reporting the
  ;; inner declaration is correct -- unlike an adversary that turns a broadcast
  ;; into per-peer sends and therefore has its own surface.
  (capabilities [_] (n/capabilities inner))

  (init [_ config]
    ;; `effects` only -- destructuring `state` here would SHADOW the record's
    ;; own `state` field, which is the tracing buffer, and the recording would
    ;; silently write into the node's consensus state instead.
    (let [{:keys [effects] :as r} (n/init inner config)]
      (record! state {:seq (swap! (:counter state) inc)
                      :peer (:peer-id config)
                      :in :init
                      :out (mapv n/effect-kind effects)})
      r))

  (step [_ st input]
    (let [{:keys [effects] :as r} (n/step inner st input)
          entry (cond-> {:seq (swap! (:counter state) inc)
                         :peer (:peer-id st)
                         :in (:type input)
                         :out (mapv n/effect-kind effects)}
                  (:detail? state) (assoc :input input :effects effects))]
      (record! state entry)
      r)))

(defn tracing
  "Wrap `node` so every transition is recorded.

  Options: `:limit` entries kept, `:sink` a function of one entry, `:detail?`
  to record whole inputs and effects rather than their kinds."
  ([node] (tracing node {}))
  ([node {:keys [limit sink detail?] :or {limit default-limit}}]
   (->Tracing node {:entries (atom []) :counter (atom 0)
                    :limit limit :sink sink :detail? detail?})))

(defn entries
  "Everything recorded, oldest first."
  [tracing-node]
  @(:entries (:state tracing-node)))

(defn summary
  "How many of each input type this node saw, and how many of each effect kind
  it produced. The first thing to look at, and usually enough: a node that has
  seen nothing has an empty `:in`, which distinguishes 'not receiving' from
  'receiving and not acting' -- the two possibilities that state inspection
  alone cannot tell apart."
  [tracing-node]
  (let [es (entries tracing-node)]
    {:n (count es)
     :in (frequencies (map :in es))
     :out (frequencies (mapcat :out es))}))
