(ns urd.consensus.runtime
  "A real-network runtime for `urd.consensus.node`.

  The simulator interprets a node's effects against logical time and an
  in-memory network; this interprets the SAME effects against core.async, a
  wall clock and a `ConsensusNetwork`. One algorithm, two interpreters, and the
  algorithm cannot tell them apart -- which is the point, and is what makes a
  schedule that fails in the simulator meaningful about a deployment.

  ## Ported from the legacy `ConsensusAlgorithm` protocol

  This used to drive `urd.consensus.state-machine`, an earlier version of
  `node`. Three things changed, and each was a layering fault rather than a
  translation:

  1. **The effect vocabulary was one algorithm's, generalised by accident.**
     A supposedly generic runtime knew `request-missing-proposal`,
     `request-state-sync`, `request-votes`, `broadcast-finalization`,
     `add-own-vote` and `trigger-next-round` by name -- every one of them
     round-robin's. They are ordinary messages, a vote, and a timer; the
     algorithm spells them that way now and this interprets the thirteen
     effects the protocol actually defines.

  2. **`add-own-vote` meant a node's own vote lived in the runtime's log
     rather than in the node's state.** A vote outside the state machine is a
     vote the state machine cannot count.

  3. **Timers were wall-clock milliseconds.** A node now asks for TICKS and
     `:tick-ms` converts. That keeps the algorithm's contract identical under
     both interpreters: logical time is what makes a failing schedule
     reproducible, and an algorithm whose timeouts are milliseconds cannot be
     replayed at all.

  ## Unicast over a broadcast transport

  `ConsensusNetwork` is topic pubsub with no unicast, so `send-to` is carried on
  a `:direct` topic with a `:to` field and filtered on receipt. That is honest
  rather than clever: the message reaches every peer and all but one drop it, so
  `send-to` here costs what a broadcast costs. Kabel's pubsub is the constraint;
  a transport with real unicast should override this."
  (:require [urd.consensus.node :as n]
            [urd.consensus.network :as net]
            [urd.consensus.store :as store]
            [urd.consensus.auth :as auth]
            [urd.consensus.rng :as rng]
            #?(:clj [clojure.core.async :refer [chan promise-chan timeout alt! close! >! <! <!! go put! take!]]
               :cljs [clojure.core.async :refer [chan promise-chan timeout alt! close! >! <! put! take! go]])
            [superv.async :refer [go-try- <?-]])
  ;; `go` is referred in BOTH branches. It was in the `:clj` one only, while
  ;; `do-persist-then` calls it unconditionally, so this namespace did not
  ;; compile under ClojureScript at all -- and nothing noticed, because the
  ;; cljs test runner loads the algorithms and the simulator and never loads
  ;; the runtime. urd's portability claim was therefore true of the half that
  ;; was tested and false of the half that was not.
  ;;
  ;; Not `:require-macros`: modern core.async self-requires its macros, and
  ;; asking for them separately collides with the automatic
  ;; clojure.core.async -> cljs.core.async alias ("`:as` alias must be
  ;; unique"). datahike's note in `datahike.audit` describes the same failure
  ;; on an older setup; the cure here is simply to refer it on both sides.
  )

(def default-tick-ms
  "How long one logical tick lasts in the real world.

  The algorithms' timeouts are in ticks -- round-robin's proposal timeout is 8 --
  so this is the single knob that turns a simulated schedule into a real one."
  100)

(def direct-topic
  "Where `send-to` is emulated. See the namespace docstring: this transport has
  no unicast, so a directed message rides a topic with a `:to` field and is
  filtered on receipt."
  :direct)

(defrecord ConsensusRuntime
           [peer-id
            node                 ; a `urd.consensus.node/Node`
            auth                 ; the verification edge; see urd.consensus.auth
            emits                ; declared capability set, enforced below
            topics               ; declared broadcast topics; what we subscribe to
            network
            store                ; a `urd.consensus.store/DurableStore`
            validators           ; peer ids, the pool `:sample` draws from
            node-state           ; Atom<Map>
            timers               ; Atom<Map<timer-id -> cancel-fn>>
            rng                  ; Atom<rng value>, threaded for `:sample`
            committed            ; Atom<{:tail [vertex] :trimmed n}>, see do-revert
            tail-limit
            write-seq            ; Atom<long>, fallback persist token
            tick-ms
            on-propose           ; (fn [context]) -> value
            on-finalize          ; (fn [vertices])
            on-revert            ; (fn [to-vertex dropped])
            on-resync            ; (fn [vertices])
            on-equivocation      ; (fn [peer evidence])
            on-error             ; (fn [exception])
            error                ; Atom<exception|nil>, what halted the loop
            dropped              ; Atom<long>, messages `step` could not process
            running?
            event-ch
            control-ch])

;; ============================================================
;; Effects
;; ============================================================

(declare handle-loop-error! stop-runtime!)

(defn- emit-event! [runtime event]
  (put! (:event-ch runtime) event))

(defn- update-network-jobs! [runtime f]
  (let [jobs (swap! (:network-jobs runtime) f)]
    (when (and (:closed? jobs) (zero? (:active jobs)))
      (close! (:network-drained runtime)))))

(def ^:private max-envelope-jobs 128)

(defn- network-job! [runtime kind work]
  ;; Admission and close share one atom. Each direction gets its own capacity,
  ;; so slow receipt writes leave room to send. Archive reads carry an awaited
  ;; local completion and must run even when the transport is saturated.
  (let [available? (fn [jobs] (or (= kind :archive)
                                  (< (get jobs kind 0) max-envelope-jobs)))
        [previous current] (swap-vals! (:network-jobs runtime)
                                       (fn [jobs]
                                         (if (or (:closed? jobs) (not (available? jobs)))
                                           jobs
                                           (-> jobs (update :active inc)
                                               (update kind (fnil inc 0))))))]
    (cond
      (:closed? previous) nil
      (= (:active previous) (:active current)) (swap! (:dropped runtime) inc)
      :else
      (let [finish (fn [_] (update-network-jobs! runtime #(-> % (update :active dec)
                                                              (update kind dec))))]
        (try
          (if @(:running? runtime)
            (take! (work) finish)
            (finish nil))
          (catch #?(:clj Exception :cljs :default) e
            (finish nil)
            (throw e)))))))

(defn- do-broadcast
  "Sign, then send.

  The envelope carries the signature; `:sender` is kept alongside it only so
  the transport can drop our own broadcast on the way back. It is NOT what
  identifies the author any more -- `auth/unseal` decides that, from bytes the
  sender could not have forged."
  ([runtime topic msg] (do-broadcast runtime topic msg nil))
  ([runtime topic msg to]
   (network-job!
    runtime :send
    (fn []
      (go-try-
       (when-let [envelope (try
                             (<?- (auth/seal (:auth runtime) msg {:topic topic :to to}))
                             (catch #?(:clj Exception :cljs :default) e
                               (handle-loop-error! runtime e)
                               nil))]
         (when @(:running? runtime)
           (<?- (net/broadcast! (:network runtime) topic
                                (assoc envelope :sender (:peer-id runtime)))))))))))

(defn- do-send-to
  "Unicast, emulated over broadcast; see the namespace docstring.

  `:to` rides on the ENVELOPE, outside the signed payload. Putting it inside
  looks tidier and breaks the filter: the receive handler tests
  `(:to envelope)`, so a `:to` buried in `:msg` left every node concluding the
  message was not addressed to anyone in particular and accepting it. Measured
  -- round-robin's directed `:catchup` and `:vote-bundle` reached every peer
  and the cluster diverged at committed position 67.

  It is also the right layer for it. `:to` is routing rather than content: it
  says nothing a forger could profit from, and a peer that rewrites it can only
  redirect a message whose signature still names its true author."
  [runtime to msg]
  (do-broadcast runtime direct-topic msg to))

(defn- unix-seconds []
  (quot #?(:clj (System/currentTimeMillis) :cljs (.now js/Date)) 1000))

(defn- do-set-timer
  "Arm `timer-id`, replacing any live arming of the same id.

  ## Registration is SYNCHRONOUS, and removal is conditional

  Both were neither, and the combination made `cancel-timer` unreliable.

  The whole body used to run inside the `go-try-`, so the entry appeared in the
  map some time after the effect was interpreted; and both `alt!` branches
  ended in an unconditional `(swap! timers dissoc timer-id)` with no check that
  the entry was still THEIRS. Re-arming an armed timer therefore went:

    - arming 2 reads arming 1's cancel-fn, cancels it, installs its own;
    - arming 1 wakes on its cancel channel and dissocs the id -- deleting
      arming 2's entry, while arming 2's timeout is still live.

  The map is now empty and a timer is still running. The next `cancel-timer`
  finds nothing and cancels nothing; the next `set-timer` finds nothing to
  replace and arms a SECOND live timer. Orphans accumulate.

  Measured before the fix: arm `:x`, arm `:x` again, cancel `:x` -- the map is
  empty, and `:x` fires anyway.

  It matters most where timers are re-armed constantly. Raft re-arms
  `:election` on every heartbeat, so a follower accumulated orphaned election
  timers that fired at random: spurious elections, term inflation, leader
  churn. Round-robin's `:proposal-timeout`, Nakamoto's `:clock` and Snowman's
  `:poll` are all re-armed the same way.

  The simulator has none of this -- `set-timer` is `assoc-in` and
  `cancel-timer` is `dissoc`, both exact and synchronous -- so this is the
  sim-passes/production-fails class in its purest form.

  Now: the swap happens on the caller's thread, so an effect vector of
  `[(set-timer :t) (cancel-timer :t)]` behaves the way it reads; and each
  arming removes only its OWN entry, checked by identity."
  [runtime timer-id after-ticks]
  (let [timers    (:timers runtime)
        cancel-ch (chan)
        cancel-fn (fn [] (put! cancel-ch true))
        [prev _]  (swap-vals! timers assoc timer-id cancel-fn)]
    ;; Replace-then-cancel, not cancel-then-replace: by the time the old
    ;; arming wakes, the entry is already ours, so its conditional removal
    ;; correctly declines to touch it.
    (when-let [old (get prev timer-id)] (old))
    (let [timeout-ch (timeout (* after-ticks (:tick-ms runtime)))
          forget!    (fn []
                       (swap! timers (fn [m]
                                       (if (identical? (get m timer-id) cancel-fn)
                                         (dissoc m timer-id)
                                         m))))]
      (go-try-
       (alt!
         timeout-ch ([_]
                     ;; Not armed again after shutdown: `stop-runtime!` has
                     ;; already cancelled the live set, and re-arming timeouts
                     ;; would otherwise install one nothing cancels. Guarding at
                     ;; DELIVERY rather than at arming -- an earlier attempt
                     ;; wrapped the arming itself and no timer ever fired again,
                     ;; which the trace showed at once: every node had seen only
                     ;; `:init`.
                     (when @(:running? runtime)
                       (emit-event! runtime (cond-> (n/timer-fired timer-id)
                                              (= :clock timer-id) (assoc :unix-time (unix-seconds)))))
                     (forget!))
         cancel-ch ([_] (forget!)))))))

(defn- do-cancel-timer [runtime timer-id]
  (when-let [cancel-fn (get @(:timers runtime) timer-id)] (cancel-fn)))

(defn- legacy-callback?
  "Recognize ordinary fixed-arity legacy callbacks once, before invocation."
  [f arity]
  (and f
       #?(:clj
          (let [f (if (var? f) @f f)
                fixed (into #{} (comp (filter #(= "invoke" (.getName ^java.lang.reflect.Method %)))
                                      (map #(.getParameterCount ^java.lang.reflect.Method %)))
                            (.getDeclaredMethods (class f)))
                accepts? (fn [n] (or (contains? fixed n)
                                     (and (instance? clojure.lang.RestFn f)
                                          (<= (.getRequiredArity ^clojure.lang.RestFn f) n))))]
            (and (accepts? arity) (not (accepts? 1))))
          :cljs
          (let [accepts? (fn [n]
                           (or (some? (aget f (str "cljs$core$IFn$_invoke$arity$" n)))
                               (if (.-cljs$lang$applyTo f)
                                 (<= (.-cljs$lang$maxFixedArity f) n)
                                 (= n (.-length f)))))]
            (and (fn? f) (accepts? arity) (not (accepts? 1)))))))

(defn- do-request-value [runtime context]
  (when-let [f (:on-propose runtime)]
    (go (try
          (emit-event! runtime (n/value-ready (f context) context))
          (catch #?(:clj Throwable :cljs :default) e
            (handle-loop-error! runtime e))))))

(defn- warn! [runtime & parts]
  (println "[" (:peer-id runtime) "] warn -" (apply str (interpose " " parts))))

(defn- do-read-durable [runtime {ks :keys token :token}]
  (network-job!
   runtime :archive
   (fn []
     (go
       (let [values (try
                      (<?- (store/fold (:store runtime)
                                       (fn [found record]
                                         (reduce-kv (fn [m k v]
                                                      (if (contains? ks k) (assoc m k v) m))
                                                    found (:writes record)))
                                       {}))
                      (catch #?(:clj Throwable :cljs :default) e
                        (warn! runtime "durable lookup failed" (ex-message e))
                        {}))]
         (when @(:running? runtime)
           (emit-event! runtime (n/durable-values token (or values {})))))))))

(def persist-complete
  "Marks the internal event that carries a landed write back to the loop.

  `persist-then` cannot be finished where it is issued. The simulator steps the
  node with `persisted` and only THEN releases the gated effects, in that order,
  on one thread. Here the completion arrives on a go block while the event loop
  is elsewhere, so releasing `:then` inline would put this node's binding
  messages on the wire BEFORE it had processed its own write landing -- the one
  ordering the barrier exists to impose. Routing the completion through the
  event channel puts both steps back on the loop, in the simulator's order."
  ::persist-complete)

(defn- await-durable-writes! [runtime]
  ;; Storage acknowledgements can wake different dispatch threads. Deliver the
  ;; corresponding state transitions and application callbacks in issue order.
  (go
    (loop []
      (when-let [[landed completion] (<! (:durable-queue runtime))]
        (alt!
          (:control-ch runtime) ([_] nil)
          landed ([result]
                  (when @(:running? runtime)
                    (if (true? result)
                      (do (emit-event! runtime completion) (recur))
                      (handle-loop-error!
                       runtime
                       (ex-info "durable write failed -- the barrier cannot be honoured"
                                {:peer-id (:peer-id runtime) :token (:token completion)}
                                (when (instance? #?(:clj Throwable :cljs js/Error) result)
                                  result)))))))))))

(defn- do-persist-then [runtime params]
  (let [{:keys [writes durable? epoch then truncate-from checkpoint]} params
        ;; Caller-supplied token when present; we only invent one as a
        ;; fallback, because a node that cannot name its own write cannot
        ;; correlate the completion with it.
        token (or (:token params) (swap! (:write-seq runtime) inc))
        record (cond-> {:writes writes :durable? durable?}
                 truncate-from (assoc :truncate-from truncate-from))
        ;; A checkpoint REPLACES the log; a write extends it. Both are gated by
        ;; the same barrier below, which is the point of putting the flag here:
        ;; dropping the old log before the new one is durable is the crash that
        ;; loses everything, and the barrier is already the code that waits.
        landed (if checkpoint
                 (store/checkpoint! (:store runtime) checkpoint)
                 (store/write! (:store runtime) record))
        completion {:type persist-complete :token token :epoch epoch
                    :then (or then [])}]
    (if durable?
      (put! (:durable-queue runtime) [landed completion])
      ;; Buffered: the node is told immediately and the write proceeds behind
      ;; it. The result is still read -- a failure that no one looks at is a
      ;; write the node believes it made.
      (do (emit-event! runtime completion)
          (go (let [r (<! landed)]
                (when (instance? #?(:clj Throwable :cljs js/Error) r)
                  (warn! runtime "buffered write failed:" (ex-message r)))))))))

#?(:clj (defonce ^:private secure-random (java.security.SecureRandom.)))

(defn- secure-word
  "A 32-bit word from the HOST's cryptographic source."
  []
  #?(:clj  (bit-and (.nextInt ^java.security.SecureRandom secure-random) 0xFFFFFFFF)
     :cljs (aget (js/crypto.getRandomValues (js/Uint32Array. 1)) 0)))

(defn- draw-sample!
  "Draw `k` peers.

  Two modes, and the difference is the whole security of Snowman's sampling.

  With an explicit `:seed` the runtime threads `urd.consensus.rng`, so a run is
  reproducible -- that is what the simulator and the tests need, and the
  compare-and-set loop is there because the draw and the generator's advance
  have to come from the same value (`swap!`'s function may be retried, handing
  back a bag drawn from a state that was then discarded).

  With NO seed every draw comes from a freshly seeded generator, seeded from
  the host's cryptographic source. `urd.consensus.rng` is xorshift32 and says
  in its own docstring that it is emphatically not cryptographic; worse than
  that, `next-word` returns `[x {:state x}]`, so the word it emits IS its next
  state. One observed output reveals the entire future stream.

  And the outputs are observable. A sample is a set of queries, `send-to` is
  emulated over a broadcast carrying `:to`, so every peer on the topic sees
  exactly whom we asked. An adversary watches one round, recovers the state,
  predicts every subsequent draw, and positions itself to be sampled -- which
  is precisely the attack that sampling at random exists to prevent. Seeding
  unpredictably, as `default-seed` did, does not help at all once a single
  output has been seen.

  Reseeding per draw rather than keeping a CSPRNG object threaded through the
  record keeps `rng`'s pure `[value next-rng]` contract intact; the cost is one
  host call per sample, against `k` network round trips."
  [rng-atom candidates weight-fn k]
  (if rng-atom
    (loop []
      (let [r @rng-atom
            [bag r'] (rng/sample-weighted-bag r candidates weight-fn k)]
        (if (compare-and-set! rng-atom r r') bag (recur))))
    (first (rng/sample-weighted-bag (rng/make (secure-word))
                                    candidates weight-fn k))))

(defn- do-sample [runtime {:keys [request-id k from powers]}]
  (let [validators (if powers (sort-by str (keys powers)) (vec (sort (:validators runtime))))
        candidates (if (= from :validators)
                     validators
                     (vec (remove #{(:peer-id runtime)} validators)))]
    (if (empty? candidates)
      ;; Loud rather than silent. A node that asked for a sample and never
      ;; receives `sampled` simply stops, and a Snowman that stops looks
      ;; exactly like a Snowman that has not decided yet.
      (warn! runtime "sample requested with no candidates -- is :validators set?")
      (emit-event! runtime (n/sampled request-id (draw-sample! (:rng runtime) candidates (or powers (constantly 1)) k))))))

(defn- do-commit
  "Hand the newly committed vertices to the application, IN ORDER.

  Synchronous, on the event loop, and that is the whole of it. This used to run
  the handler inside a `go-try-`, so two commits emitted in quick succession
  spawned two go blocks whose handler calls raced -- and the application saw
  the committed prefix out of order.

  Measured on Tendermint over this runtime: at position 486 one node had
  entries 488 and 489 transposed relative to its peers. Identical SET, wrong
  ORDER, and no error anywhere. `commit`'s contract is that these vertices go
  on the END of the committed prefix, so order is the entire content of the
  effect -- a consumer that applies them as transactions, which is exactly what
  the datahike ledger does, would have written the database in the wrong order
  and had no way to notice.

  The cost of being synchronous is that a slow handler blocks the event loop.
  That is correct: it is backpressure on a node that is committing faster than
  its application can absorb, and it is what the simulator already does, which
  is the property the two interpreters exist to share."
  [runtime vertices]
  ;; The committed tail is tracked so `:revert` can be CHECKED rather than
  ;; trusted; see `do-revert`.
  (let [[previous _] (swap-vals! (:committed runtime)
                                 (fn [{:keys [tail trimmed]}]
                                   (let [t (into tail vertices)
                                         over (max 0 (- (count t) (:tail-limit runtime)))]
                                     {:tail (if (or (zero? (:tail-limit runtime))
                                                    (and (pos? over)
                                                         (not= (quot trimmed (:tail-limit runtime))
                                                               (quot (+ trimmed over) (:tail-limit runtime)))))
                                              (into [] (subvec t over))
                                              (subvec t over))
                                      :trimmed (+ trimmed over)})))]
    (when-let [f (:on-finalize runtime)]
      (if (:legacy-finalize? runtime)
        (let [base (+ (:trimmed previous) (count (:tail previous)))]
          (doseq [[i v] (map-indexed vector vertices)]
            (f v (+ base i))))
        (f vertices)))))

(defn- do-revert
  "Roll the committed prefix back, having first checked that we agree about
  what is being dropped.

  `node/revert` says an interpreter SHOULD reject a revert whose `:dropped`
  does not match the tail it holds, and the simulator throws. So does this. The
  check is the whole safety of the effect: without it a `to-vertex` that was
  never committed is indistinguishable from a mistyped one, and both mean
  discard everything.

  One case the simulator does not have. A long-running node cannot keep every
  committed vertex in memory, so only the last `:tail-limit` are retained. If
  the target is absent AND we have trimmed, absence no longer proves the vertex
  was never committed -- it may simply be older than what we kept. Truncating
  to nothing there would wipe good history on a deep reorg, so it is refused
  and named. Raise `:tail-limit` above the deepest reorg you intend to
  tolerate."
  [runtime {:keys [to-vertex dropped]}]
  (let [{:keys [tail trimmed]} @(:committed runtime)
        claimed (vec dropped)
        at (last (keep-indexed (fn [i v] (when (= v to-vertex) i)) tail))
        keep-n (if at (inc at) 0)
        actual (subvec tail keep-n)]
    (when (and (nil? at) (pos? trimmed))
      (throw (ex-info "revert target is older than the retained committed tail"
                      {:peer (:peer-id runtime) :to to-vertex
                       :retained (count tail) :trimmed trimmed})))
    (when (not= claimed actual)
      (throw (ex-info "revert :dropped does not match the committed tail"
                      {:peer (:peer-id runtime) :to to-vertex
                       :claimed claimed :actual actual})))
    (swap! (:committed runtime) assoc :tail (into [] (subvec tail 0 keep-n)))
    (if-let [f (:on-revert runtime)]
      (f to-vertex actual)
      (warn! runtime "reverted" (count actual) "vertices with no :on-revert handler"))))

(defn- do-resync [runtime vertices]
  (let [v (vec vertices)
        limit (:tail-limit runtime)
        over (max 0 (- (count v) limit))]
    (reset! (:committed runtime) {:tail (into [] (subvec v over)) :trimmed over})
    (when-let [f (:on-resync runtime)] (f v))))

(defn- do-report-equivocation [runtime {:keys [peer evidence]}]
  (if-let [f (:on-equivocation runtime)]
    (f peer evidence)
    ;; Provable misbehaviour is not a debug line, and dropping it on the floor
    ;; is how a slashable offence becomes invisible.
    (warn! runtime "equivocation by" peer "-- no :on-equivocation handler; evidence dropped")))

(defn interpret-effect
  "Interpret one effect. Every branch is an effect `node` defines; there are no
  algorithm-specific ones left."
  [runtime effect]
  (let [kind (n/effect-kind effect)
        params (n/effect-params effect)]
    ;; The declaration is checked on every effect, exactly as the simulator
    ;; checks it -- a capability set that only one interpreter enforces is not
    ;; enforced.
    (when-not (contains? (:emits runtime) kind)
      (throw (ex-info "node emitted an effect it did not declare"
                      {:peer (:peer-id runtime) :effect kind
                       :declared (:emits runtime)})))
    (case kind
      :broadcast
      ;; Refused if undeclared, exactly as an undeclared EFFECT is. The
      ;; declaration is what the subscription list is built from, so a
      ;; broadcast to a topic outside it is a message that provably cannot be
      ;; received -- and the whole cost of the bug this replaces was that such
      ;; a send looked identical to a successful one.
      (let [topic (:topic params)]
        (when-not (or (contains? (:topics runtime) topic) (= direct-topic topic))
          (throw (ex-info "node broadcast to a topic it did not declare"
                          {:peer (:peer-id runtime) :topic topic
                           :declared (:topics runtime)})))
        (do-broadcast runtime topic (:msg params)))
      :send (do-send-to runtime (:to params) (:msg params))
      :set-timer (do-set-timer runtime (:timer-id params) (:after-ticks params))
      :cancel-timer (do-cancel-timer runtime (:timer-id params))
      :request-value (do-request-value runtime (:context params))
      :read-durable (do-read-durable runtime params)
      :commit (do-commit runtime (:vertices params))
      :log (when (#{:info :warn :error} (:level params))
             (println "[" (:peer-id runtime) "]" (name (:level params)) "-" (:message params)))
      :deliver-self (emit-event! runtime (:input params))
      :persist-then (do-persist-then runtime params)
      :sample (do-sample runtime params)
      :revert (do-revert runtime params)
      :resync (do-resync runtime (:vertices params))
      :report-equivocation (do-report-equivocation runtime params)
      (throw (ex-info "unknown effect" {:peer (:peer-id runtime) :effect kind})))))

(defn interpret-effects [runtime effects]
  (doseq [e effects :while @(:running? runtime)] (interpret-effect runtime e)))

;; ============================================================
;; The loop
;; ============================================================

(defn- remote?
  "Did this input come off the wire?

  A `:message-received` is the only input a stranger chooses. Timers, our own
  `deliver-self`, `persisted` and `value-ready` all originate here."
  [input]
  (= :message-received (:type input)))

(defn- step-and-interpret [runtime input]
  (let [{:keys [state effects]}
        (if (remote? input)
          ;; A `step` that THROWS on a message is a message the algorithm could
          ;; not handle. That is a dropped packet, not a fault of ours.
          ;;
          ;; This is not defensive programming, it is the difference between a
          ;; bug and a remote kill switch. `handle-loop-error!` halts the node
          ;; permanently and never restarts it -- correct for an invariant
          ;; violation, catastrophic when a stranger picks the moment. Verified
          ;; before this existed: ONE broadcast of
          ;;
          ;;     {:kind :finalized :proposal nil :height "boom"}
          ;;
          ;; makes round-robin evaluate `(> "boom" height)`, throw
          ;; ClassCastException, and halt every node that receives it, from
          ;; height 0, forever. Sixty bytes for the cluster. Tendermint and
          ;; Nakamoto validate their message fields; round-robin, Bullshark and
          ;; SCP do not, and this closes the class rather than the instance.
          ;;
          ;; Dropping is SAFE because `step` is pure: it either returns a new
          ;; state or it does not, and a throw leaves us on the state we had.
          ;; There is no half-applied input to reconcile.
          ;;
          ;; The effects are deliberately NOT covered. An effect that throws --
          ;; `do-revert` finding its `:dropped` disagrees with our committed
          ;; tail -- is this node discovering it is wrong about history, which
          ;; is exactly what fail-stop is for, whatever input led there.
          (try
            (n/step (:node runtime) @(:node-state runtime) input)
            (catch #?(:clj Throwable :cljs js/Error) e
              (swap! (:dropped runtime) inc)
              (warn! runtime "dropped a message the node could not process:"
                     (ex-message e))
              {:state @(:node-state runtime) :effects []}))
          (n/step (:node runtime) @(:node-state runtime) input))]
    (reset! (:node-state runtime) state)
    (interpret-effects runtime effects)))

(defn process-event [runtime event]
  (if (= persist-complete (:type event))
    (do (step-and-interpret runtime (n/persisted (:token event) (:epoch event)))
        ;; ...and only THEN the gated effects go out. This is the whole point
        ;; of the barrier, and the order the simulator uses.
        (interpret-effects runtime (:then event)))
    (step-and-interpret runtime event)))

(defn- handle-loop-error!
  "Report an exception out of the event loop, and HALT.

  Both halves matter and neither was here before.

  Reporting, because `go-loop-try-` conveys the exception on a channel that
  nothing reads, so a throw simply ended the loop. The node then sat there
  holding its state, answering `get-state`, and doing nothing -- which is
  indistinguishable from a node waiting for a message that has not arrived. One
  such exception (a division by zero on an empty validator set) was diagnosed
  as a hang in the tracing wrapper, and cost a day.

  Halting, because the exceptions this can raise are invariant violations --
  `do-revert` throwing on a `:dropped` mismatch is a node discovering that its
  committed history disagrees with the interpreter's. Carrying on past that
  produces a node that is wrong rather than one that is stopped, and fail-stop
  is the only one of those a consensus system can tolerate."
  [runtime e]
  (when (and @(:running? runtime) (compare-and-set! (:error runtime) nil e))
    (stop-runtime! runtime)
    ;; An error callback may await shutdown. It cannot run on the event loop
    ;; or network job that shutdown is draining.
    (go
      (if-let [f (:on-error runtime)]
        (f e)
        (println "[" (:peer-id runtime) "] FATAL - consensus event loop halted:"
                 (ex-message e) (pr-str (ex-data e)))))))

(defn run-event-loop
  "The event loop.

  `(go-try- (loop ...))` rather than `go-loop-try-`, and that is not a style
  preference. superv.async 0.3.50 defines

      (defmacro go-loop-try- [bindings & body]
        `(go-try- ~S (loop ~bindings ~@body)))

  and `~S` unquotes the supervisor VALUE into the expansion. `S` holds
  channels, so the macro emits a literal channel: harmless on the JVM, where it
  is an object reference, and fatal under ClojureScript, which refuses to
  compile the namespace, reporting that a ManyToManyChannel is not a valid
  ClojureScript constant. It is also passing `S` as a discarded first body form
  to a macro whose whole point is that it runs WITHOUT supervision, so nothing
  is lost by expanding it by hand.

  That single macro use is why `urd.consensus.runtime` did not compile under
  cljs. Worth reporting upstream -- see the note in the plan."
  [runtime]
  (let [{:keys [event-ch control-ch running?]} runtime]
    (go-try-
     (loop []
       (if @running?
         (alt!
           event-ch ([event]
                     (when (and event @running?)
                       (try (process-event runtime event)
                            (catch #?(:clj Throwable :cljs js/Error) e
                              (handle-loop-error! runtime e)))
                       (recur)))
           control-ch ([_] nil))
         nil)))))

;; ============================================================
;; Network
;; ============================================================

(defn- unsubscribe-handlers! [runtime]
  (go-try-
   (loop [entries (seq @(:subscriptions runtime)), failure nil]
     (if-let [[topic handle] (first entries)]
       (let [error (try
                     (<?- (net/unsubscribe! (:network runtime) topic handle))
                     (swap! (:subscriptions runtime) dissoc topic)
                     nil
                     (catch #?(:clj Exception :cljs :default) e e))]
         (recur (next entries) (or failure error)))
       (when failure (throw failure))))))

(defn setup-network-handlers
  "Subscribe to exactly the topics the node DECLARED, plus `:direct`.

  This list used to be hardcoded as `[:proposals :votes :finalizations
  :recovery :direct]` -- round-robin's vocabulary, in a runtime that called
  itself generic. Every other algorithm broadcasts somewhere else entirely:
  Tendermint on `:consensus`, SCP on `:scp`, Bullshark on `:bullshark`,
  Nakamoto on `:headers`. Their messages were accepted, sent, and delivered to
  nobody.

  It failed silently, which is the part worth remembering. Tendermint on this
  runtime started cleanly, reported no error, and sat at height 0 forever --
  four nodes each waiting for votes that had gone nowhere. Nothing in the
  system could tell the difference between a message nobody had subscribed to
  and a message nobody had sent."
  [runtime]
  (go-try-
   (doseq [topic (conj (:topics runtime) direct-topic)]
     (let [handler (fn [envelope]
                     (when (and @(:running? runtime)
                                (= topic (:topic envelope))
                                (not= (:sender envelope) (:peer-id runtime))
                                (if (= direct-topic topic)
                                  (= (:peer-id runtime) (:to envelope))
                                  (nil? (:to envelope))))
                       (network-job!
                        runtime :receive
                        (fn []
                          (go-try-
                           (when-let [{:keys [from msg verified-by]}
                                      (try
                                        (<?- (auth/unseal (:auth runtime) (dissoc envelope :sender)))
                                        (catch #?(:clj Exception :cljs :default) e
                                          (if (::auth/store-error (ex-data e))
                                            (handle-loop-error! runtime e)
                                            (swap! (:dropped runtime) inc))
                                          nil))]
                             (when @(:running? runtime)
                               (emit-event! runtime (n/message-received from msg verified-by)))))))))
           handle (<?- (net/subscribe! (:network runtime) topic handler))]
       (swap! (:subscriptions runtime) assoc topic handle)))))

;; ============================================================
;; Public API
;; ============================================================

(def default-tail-limit
  "How many committed vertices are retained so `:revert` can be verified.

  The simulator keeps every committed vertex and can therefore always check a
  revert's `:dropped`. A node that runs for a month cannot. This is the depth
  of reorg that stays checkable; past it `do-revert` refuses rather than
  guesses."
  4096)

;; `default-seed` is gone. It mixed `nanoTime` with the peer id to make the
;; STARTING state hard to guess, which sounds like the right idea and is not
;; worth anything here: xorshift32's emitted word is its own next state, so one
;; observed sample gives an adversary the whole future sequence no matter how
;; well the generator was seeded. An unseeded runtime now draws each sample
;; from a generator freshly seeded by the host CSPRNG -- see `draw-sample!`.

(defn start-runtime!
  "Start a runtime driving `node`.

  Config:
    :peer-id :node :network :validators
    :store       a `urd.consensus.store/DurableStore`; in-memory by default,
                 which is durable across a node restart and not across a
                 process one
    :on-propose  (fn [context]) -> value
    :on-finalize (fn [vertices])
    :on-revert   (fn [to-vertex dropped])
    :on-resync   (fn [vertices])
    :delivered-through  how many committed vertices the consumer has ALREADY
                 applied -- a number or a 0-arg fn. etcd's `Config.Applied`.
                 Without it a restarting node has to guess, and both guesses
                 are wrong in some case: re-announcing the whole prefix is
                 impossible once the log is compacted, and announcing nothing
                 drops entries that were committed but never delivered.
    :on-equivocation (fn [peer evidence])
    :tick-ms     wall-clock duration of one logical tick
    :tail-limit  committed vertices retained for revert checking
    :seed        make sampling REPRODUCIBLE, for simulation and tests. Without
                 it every sample is drawn from the host's cryptographic source,
                 which is what Snowman's security actually requires.

  Accepts `:state-machine` as an alias for `:node`, so callers written against
  the legacy runtime keep working."
  [{:keys [peer-id node state-machine network store validators
           on-propose on-finalize on-revert on-resync on-equivocation
           tick-ms tail-limit seed auth]
    :as config}]
  (go-try-
   (let [node (or node state-machine)
         ;; REQUIRED, and deliberately not defaulted. `verified-by` used to be
         ;; built from the message's own `:sender` field, so it carried the
         ;; attacker's claim about the attacker's identity, and every Byzantine
         ;; property in this library rested on it. A default would let that
         ;; return silently; `:none` is available and has to be typed.
         store (or store (store/memory-store))
         authenticator (auth/authenticator
                        (or auth (throw (ex-info (str "start-runtime! needs :auth -- a config map, "
                                                      "or :none to run unauthenticated on purpose")
                                                 {:peer-id peer-id})))
                        peer-id store)
         emits (n/check-capabilities node)
         topics (n/check-topics node)
         ;; What landed before this node died, in the two views `sim/restart`
         ;; supplies. Passed unconditionally: every algorithm reads it through
         ;; a nil-safe path and replaying an empty log is a no-op, so a fresh
         ;; node and a restarted one take the same code path here.
         restored (<?- (store/restore store))
         ;; What the CONSUMER has already applied, resolved before `init` so
         ;; the node can start from it. A number or a 0-arg fn: the datahike
         ;; ledger derives it from its own database (`(count @marks)`), and
         ;; that is the point -- the consumer's durable state is the authority
         ;; on what the consumer has, and a node that guesses either
         ;; re-delivers or loses the tail.
         delivered (let [d (:delivered-through config)]
                     (if (fn? d) (d) d))
         {:keys [state effects]} (n/init node (assoc config
                                                     :restored restored
                                                     :unix-time (unix-seconds)
                                                     :delivered-through delivered))
         runtime (map->ConsensusRuntime
                  {:peer-id peer-id
                   :node node
                   :auth authenticator
                   :emits emits
                   :topics topics
                   :network network
                   :store store
                   :validators (or validators [])
                   :node-state (atom state)
                   :timers (atom {})
                   ;; nil means "no reproducible generator": every sample is
                   ;; drawn from the host's cryptographic source instead. An
                   ;; explicit `:seed` is what buys reproducibility, and it
                   ;; costs unpredictability -- which is the right trade for a
                   ;; simulation and the wrong one for a deployment.
                   :rng (when seed (atom (rng/make seed)))
                   ;; Seeded from the consumer, so `:trimmed` counts what was
                   ;; delivered BEFORE this process existed. Starting at 0
                   ;; would make a restarted runtime believe the committed
                   ;; prefix began at its own boot.
                   :committed (atom {:tail [] :trimmed (or delivered 0)})
                   :tail-limit (or tail-limit default-tail-limit)
                   :write-seq (atom 0)
                   :tick-ms (or tick-ms default-tick-ms)
                   :on-propose (if (legacy-callback? on-propose 0) (fn [_] (on-propose)) on-propose)
                   :legacy-finalize? (legacy-callback? on-finalize 2)
                   :on-finalize on-finalize
                   :on-revert on-revert
                   :on-resync on-resync
                   :on-equivocation on-equivocation
                   :on-error (:on-error config)
                   :error (atom nil)
                   :dropped (atom 0)
                   :running? (atom true)
                   :event-ch (chan 100)
                   :control-ch (chan)
                   :startup-done (chan)
                   :loop-done (chan)
                   :subscriptions (atom {})
                   :network-jobs (atom {:active 0 :closed? false})
                   :network-drained (chan)
                   :shutdown (atom nil)
                   :durable-queue (chan 64)})]
     ;; All callbacks share these gates, including ones installed before init
     ;; finishes. No incoming event can overtake the initial effects.
     (go (<! (:startup-done runtime))
         (<! (run-event-loop runtime))
         (close! (:loop-done runtime)))
     (try
       (<?- (setup-network-handlers runtime))
       (await-durable-writes! runtime)
       (interpret-effects runtime effects)
       (when-let [e @(:error runtime)] (throw e))
       (close! (:startup-done runtime))
       runtime
       (catch #?(:clj Exception :cljs :default) e
         (close! (:startup-done runtime))
         (<?- (stop-runtime! runtime))
         (throw e))))))

(defn stop-runtime! [runtime]
  ;; Concurrent stop callers share a completion. A failed unsubscribe keeps
  ;; its handle and clears this completion so the next stop can retry it.
  (let [done (promise-chan)
        [existing _] (swap-vals! (:shutdown runtime) #(or % done))]
    (if existing
      existing
      (do
        (reset! (:running? runtime) false)
        (update-network-jobs! runtime #(assoc % :closed? true))
        (close! (:control-ch runtime))
        (close! (:durable-queue runtime))
        (close! (:event-ch runtime))
        (go
          (try
            (when-let [loop-done (:loop-done runtime)] (<?- loop-done))
            ;; Once the event loop has returned it cannot arm another timer.
            (doseq [[_ cancel-fn] @(:timers runtime)] (cancel-fn))
            (<! (:network-drained runtime))
            (<?- (unsubscribe-handlers! runtime))
            (catch #?(:clj Exception :cljs :default) e
              (compare-and-set! (:shutdown runtime) done nil)
              (>! done e))
            (finally (close! done))))
        done))))

(defn send-event!
  "Inject an event. `{:type :start-round}` from the legacy API is translated, so
  existing callers keep working."
  [runtime event]
  (put! (:event-ch runtime)
        (if (= :start-round (:type event))
          (n/timer-fired :next-round)
          event)))

(defn get-state [runtime] @(:node-state runtime))

(defn last-error
  "The exception that halted this runtime's event loop, or nil.

  A stopped runtime and a quiet one look identical from `get-state`; this is
  how a caller tells them apart."
  [runtime]
  @(:error runtime))

(defn dropped-messages
  "Number of malformed messages discarded and incoming or outgoing envelopes
  dropped because the runtime reached its network concurrency limit."
  [runtime]
  @(:dropped runtime))

(defn committed-tail
  "The committed vertices this runtime still retains, for assertions and for
  the revert check. See `default-tail-limit`."
  [runtime]
  (:tail @(:committed runtime)))
