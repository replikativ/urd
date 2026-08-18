(ns urd.consensus.runtime-effects-test
  "The five effects the real runtime could not interpret.

  Until these landed, `persist-then`, `sample`, `revert`, `resync` and
  `report-equivocation` threw `effect not implemented by this runtime`, which
  meant six of the seven algorithms could run only in the simulator: every one
  of them except round-robin writes something durable, and threw on its first
  write. The port had made them PORTABLE to this runtime, not RUNNABLE on it,
  and the difference is these tests.

  Each guard here has been watched to fail. Where the check is subtle the
  mutation that breaks it is named in a comment, because a guard nobody has
  seen fail is a guard nobody knows is connected."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.runtime :as rt]
            [urd.consensus.node :as n]
            [urd.consensus.rng :as rng]
            [urd.consensus.store :as store]
            [urd.consensus.stores.konserve :as kstore]
            [urd.consensus.networks.simulation :as sim-net]
            [konserve.memory :refer [new-mem-store]]
            [clojure.core.async :refer [<!! chan close! timeout go]]))

;; ============================================================
;; Probes
;; ============================================================

(defrecord ProbeNode [emits on-init on-step]
  n/Node
  (capabilities [_] {:emits emits})
  (init [_ config] (on-init config))
  (step [_ st input] (on-step st input)))

(defn echo-node
  "A node that records every input and emits whatever effects the input
  carries in `:fx`.

  Driving the effects from the TEST rather than from an algorithm is what
  makes these tests about the runtime. An algorithm would also have to be
  coaxed into the state that produces the effect, and then a failure would not
  say which of the two was wrong."
  ([emits] (echo-node emits []))
  ([emits init-effects]
   (->ProbeNode emits
                (fn [_config] {:state {:inputs []} :effects init-effects})
                (fn [st input] (n/result (update st :inputs conj input) (:fx input []))))))

(defn- input-types [runtime]
  (mapv :type (:inputs (rt/get-state runtime))))

(defrecord GateStore [gate landed]
  store/DurableStore
  (write! [_ record] (swap! landed conj record) gate)
  (restore [_] (go {:durable {} :writes []}))
  (close-store! [_] (go true)))

(defn start!
  "Start a runtime on an in-process network."
  [opts]
  (let [peer-id (or (:peer-id opts) :p1)
        router (sim-net/create-router)]
    (<!! (rt/start-runtime! (merge {:peer-id peer-id
                                    ;; In-process probe network: no identities
                                    ;; to forge, so the opt-out is honest here.
                                    :auth :none
                                    :network (sim-net/create-simulation-network peer-id router)
                                    :tick-ms 10}
                                   opts)))))

(defn- settle! [] (<!! (timeout 120)))

;; ============================================================
;; persist-then -- the barrier
;; ============================================================

(deftest durable-write-gates-its-then-effects
  (testing "nothing gated escapes before the store says the write survives"
    (let [gate (chan)
          landed (atom [])
          node (echo-node #{:persist-then :deliver-self}
                          [(n/persist-then {:writes {:hard-state {:term 1}}
                                            :durable? true :epoch 1 :token :t1
                                            :then [(n/deliver-self {:type :gated})]})])
          runtime (start! {:node node :store (->GateStore gate landed)})]
      (settle!)
      ;; The mutation: release `:then` without awaiting `landed` in
      ;; `do-persist-then` and this is [:persisted :gated] already.
      (is (= [] (input-types runtime))
          "no input at all while the write is in flight")
      (is (= 1 (count @landed)) "the write was issued, it is only unfinished")
      (is (= {:hard-state {:term 1}} (:writes (first @landed))))

      (close! gate)
      (settle!)
      (is (= [:persisted :gated] (input-types runtime))
          "the node learns the write landed BEFORE its gated messages go out")
      (<!! (rt/stop-runtime! runtime)))))

(deftest persisted-echoes-the-callers-token-and-epoch
  (let [node (echo-node #{:persist-then}
                        [(n/persist-then {:writes {:a 1} :durable? true
                                          :epoch 9 :token :mine})])
        runtime (start! {:node node})]
    (settle!)
    (let [ev (first (:inputs (rt/get-state runtime)))]
      ;; Correlation is the caller's, not the interpreter's: an algorithm with
      ;; two writes in flight cannot assume completion order.
      (is (= :mine (:token ev)))
      (is (= 9 (:epoch ev))))
    (<!! (rt/stop-runtime! runtime))))

(deftest buffered-write-does-not-wait-for-the-store
  (testing "durable? false releases immediately, even if the store never finishes"
    (let [never (chan)                  ; deliberately never closed
          node (echo-node #{:persist-then :deliver-self}
                          [(n/persist-then {:writes {:commit 4} :durable? false
                                            :epoch 1 :token :t
                                            :then [(n/deliver-self {:type :ungated})]})])
          runtime (start! {:node node :store (->GateStore never (atom []))})]
      (settle!)
      (is (= [:persisted :ungated] (input-types runtime))
          "a commit-index write is recoverable by replay and must not block")
      (<!! (rt/stop-runtime! runtime)))))

;; ============================================================
;; sample
;; ============================================================

(deftest sample-draws-a-weighted-bag-from-the-peers
  (let [validators [:p1 :p2 :p3 :p4 :p5]
        node (echo-node #{:sample} [(n/sample :req-1 3 :peers)])
        runtime (start! {:node node :validators validators :seed 42})]
    (settle!)
    (let [ev (first (:inputs (rt/get-state runtime)))
          bag (:peers ev)]
      (is (= :sampled (:type ev)))
      (is (= :req-1 (:request-id ev)))
      (is (= 3 (reduce + (vals bag))) "k units of weight, counted with multiplicity")
      (is (every? #{:p2 :p3 :p4 :p5} (keys bag))
          ":peers excludes self; only :validators includes it"))
    (<!! (rt/stop-runtime! runtime))))

(deftest sample-from-validators-includes-self
  (let [node (echo-node #{:sample} [(n/sample :r 5 :validators)])
        runtime (start! {:node node :validators [:p1 :p2] :seed 7})]
    (settle!)
    (let [bag (:peers (first (:inputs (rt/get-state runtime))))]
      (is (= 2 (reduce + (vals bag)))
          "without replacement: two candidates cannot yield five units")
      (is (= #{:p1 :p2} (set (keys bag)))))
    (<!! (rt/stop-runtime! runtime))))

(deftest sample-is-reproducible-from-a-seed-and-varies-without-one
  (let [draw (fn [seed]
               (let [node (echo-node #{:sample} [(n/sample :r 2 :peers)])
                     runtime (start! (cond-> {:node node :validators [:p1 :p2 :p3 :p4 :p5 :p6]}
                                       seed (assoc :seed seed)))]
                 (settle!)
                 (let [bag (:peers (first (:inputs (rt/get-state runtime))))]
                   (<!! (rt/stop-runtime! runtime))
                   bag)))]
    (is (= (draw 123) (draw 123)) "a fixed seed replays")
    ;; Necessary but nowhere near sufficient -- see the test below, which is
    ;; the one that matters. The old code passed this assertion and was still
    ;; fully predictable.
    (is (< 1 (count (set (repeatedly 10 #(draw nil)))))
        "with no seed the draw is not a constant")))

(deftest an-unseeded-runtime-does-not-thread-a-guessable-generator
  (testing "why varying between runs is not enough

           `urd.consensus.rng` is xorshift32, and its `next-word` returns
           `[x {:state x}]` -- the word it emits IS its next state. A threaded
           generator therefore hands an observer the entire future stream from
           a single output, however unpredictably it was seeded. And the
           outputs ARE observable: a sample is a set of queries, `send-to` is
           emulated over a broadcast carrying `:to`, so every peer on the topic
           sees whom we asked. Watch one round, predict every round after it,
           and place yourself in the sample -- which is the exact attack that
           sampling at random exists to prevent.

           `default-seed` mixed `nanoTime` with the peer id, which made the
           starting state hard to guess and bought nothing once one word had
           been seen. The fix is not a better seed, it is not keeping a
           guessable generator at all: an unseeded runtime draws each sample
           from a generator freshly seeded by the host CSPRNG.

           Structural rather than statistical. There is no honest way to assert
           'an adversary cannot predict this' from a handful of draws, so this
           pins the design decision that makes prediction impossible, and fails
           the moment a threaded weak generator comes back."
    (let [node (echo-node #{:sample} [(n/sample :r 2 :peers)])
          seeded (start! {:node node :validators [:p1 :p2 :p3] :seed 5})
          unseeded (start! {:node node :validators [:p1 :p2 :p3]})]
      (is (some? (:rng seeded))
          "an explicit seed buys reproducibility, and is meant to")
      (is (nil? (:rng unseeded))
          "and no seed means NO reproducible generator to recover -- not a
           well-hidden one")
      (<!! (rt/stop-runtime! seeded))
      (<!! (rt/stop-runtime! unseeded)))))

(deftest the-simulators-generator-leaks-its-whole-future-in-one-word
  (testing "the property that makes threading it into a live runtime unsafe

           Recorded here rather than assumed, because `rng`'s docstring says
           only 'emphatically NOT cryptographic' -- true, and much weaker than
           the reality. This is not a generator with a short period or a
           statistical bias; the output IS the state. Nothing is left to break."
    (let [r (rng/make 12345)
          [w r'] (rng/next-word r)]
      (is (= w (:state r'))
          "one observed word IS the generator")
      (is (= (rng/next-word r') (rng/next-word (rng/make w)))
          "so an observer reproduces every draw that follows it"))))

;; ============================================================
;; revert -- and the check that makes it safe
;; ============================================================

(defn- commit! [runtime vertices]
  (rt/send-event! runtime {:type :go :fx [(n/commit vertices)]})
  (settle!))

(deftest revert-truncates-the-committed-prefix
  (let [reverted (atom nil)
        runtime (start! {:node (echo-node #{:commit :revert})
                         :on-revert (fn [to dropped] (reset! reverted [to dropped]))})]
    (commit! runtime [:a :b :c])
    (is (= [:a :b :c] (rt/committed-tail runtime)))
    (rt/send-event! runtime {:type :go :fx [(n/revert :a [:b :c])]})
    (settle!)
    (is (nil? (rt/last-error runtime)) "a well-formed revert is not an error")
    (is (= [:a] (rt/committed-tail runtime)))
    (is (= [:a [:b :c]] @reverted) "the handler is told what was taken back")
    (<!! (rt/stop-runtime! runtime))))

(deftest revert-with-a-mismatched-dropped-set-halts-the-node
  (testing "the interpreter verifies rather than trusts"
    (let [runtime (start! {:node (echo-node #{:commit :revert})
                           :on-error (fn [_])})]
      (commit! runtime [:a :b :c])
      ;; Claims to drop [:c] when the tail after :a is [:b :c]. Without the
      ;; check this silently truncates and the node's history diverges from
      ;; the interpreter's with nothing reported.
      (rt/send-event! runtime {:type :go :fx [(n/revert :a [:c])]})
      (settle!)
      (let [e (rt/last-error runtime)]
        (is (some? e) "the loop reports rather than dying quietly")
        (is (= "revert :dropped does not match the committed tail" (ex-message e)))
        (is (= [:c] (:claimed (ex-data e))))
        (is (= [:b :c] (:actual (ex-data e)))))
      (is (= [:a :b :c] (rt/committed-tail runtime))
          "and nothing was truncated on the way to failing"))))

(deftest revert-to-a-never-committed-vertex-discards-everything
  (testing "genesis: the case that made :dropped mandatory"
    (let [runtime (start! {:node (echo-node #{:commit :revert}) :on-revert (fn [_ _])})]
      (commit! runtime [:a :b])
      (rt/send-event! runtime {:type :go :fx [(n/revert ::genesis [:a :b])]})
      (settle!)
      (is (nil? (rt/last-error runtime)))
      (is (= [] (rt/committed-tail runtime)))
      (<!! (rt/stop-runtime! runtime)))))

(deftest revert-deeper-than-the-retained-tail-is-refused
  (testing "a bound the simulator does not have, and must not silently wipe history"
    (let [runtime (start! {:node (echo-node #{:commit :revert})
                           :tail-limit 2
                           :on-error (fn [_])})]
      (commit! runtime [:a :b :c :d])
      (is (= [:c :d] (rt/committed-tail runtime)) "only the last two are kept")
      ;; :a is gone from the tail. Absence no longer proves it was never
      ;; committed, so truncating to nothing -- which is what the sim's rule
      ;; would do -- would wipe good history on a deep reorg.
      (rt/send-event! runtime {:type :go :fx [(n/revert :a [:b :c :d])]})
      (settle!)
      (is (some? (rt/last-error runtime)))
      (is (= "revert target is older than the retained committed tail"
             (ex-message (rt/last-error runtime)))))))

;; ============================================================
;; resync
;; ============================================================

(deftest resync-replaces-the-prefix-wholesale
  (testing "a restarting node announcing what it holds, which is not a revocation"
    (let [got (atom nil)
          runtime (start! {:node (echo-node #{:commit :resync})
                           :on-resync (fn [vs] (reset! got vs))})]
      (commit! runtime [:a :b])
      (rt/send-event! runtime {:type :go :fx [(n/resync [:x :y :z])]})
      (settle!)
      (is (= [:x :y :z] (rt/committed-tail runtime)))
      (is (= [:x :y :z] @got))
      (is (nil? (rt/last-error runtime))
          "no :dropped check applies -- there is no tail to check against")
      (<!! (rt/stop-runtime! runtime)))))

(deftest resync-then-revert-checks-against-the-resynced-prefix
  (let [runtime (start! {:node (echo-node #{:resync :revert}) :on-revert (fn [_ _])})]
    (rt/send-event! runtime {:type :go :fx [(n/resync [:x :y])]})
    (settle!)
    (rt/send-event! runtime {:type :go :fx [(n/revert :x [:y])]})
    (settle!)
    (is (nil? (rt/last-error runtime)))
    (is (= [:x] (rt/committed-tail runtime)))
    (<!! (rt/stop-runtime! runtime))))

;; ============================================================
;; report-equivocation
;; ============================================================

(deftest equivocation-reaches-the-handler
  (let [seen (atom [])
        runtime (start! {:node (echo-node #{:report-equivocation})
                         :on-equivocation (fn [peer ev] (swap! seen conj [peer ev]))})]
    (rt/send-event! runtime {:type :go
                             :fx [(n/report-equivocation :bad {:votes [:v1 :v2]})]})
    (settle!)
    (is (= [[:bad {:votes [:v1 :v2]}]] @seen))
    (<!! (rt/stop-runtime! runtime))))

;; ============================================================
;; The store, and the restart path
;; ============================================================

(deftest memory-store-round-trips-both-views
  (let [s (store/memory-store)]
    (<!! (store/write! s {:writes {:hard-state {:term 1}} :durable? true}))
    (<!! (store/write! s {:writes {:hard-state {:term 2} :entries [:e]} :durable? true}))
    (let [{:keys [durable writes]} (<!! (store/restore s))]
      (is (= {:term 2} (:hard-state durable)) "merged view is last-write-wins")
      (is (= [:e] (:entries durable)))
      (is (= 2 (count writes)) "and the ordered log is intact alongside it"))))

(deftest konserve-store-round-trips-and-keeps-issue-order
  (let [s (kstore/konserve-store (<!! (new-mem-store)))]
    ;; Issued without awaiting, which is what the runtime does for buffered
    ;; writes. `append` is a read-modify-write on the list pointer, so without
    ;; the writer go-loop serializing them these interleave and records go
    ;; missing while `write!` still reports success.
    (let [chans (mapv #(store/write! s {:writes {:n %} :durable? false}) (range 40))]
      (doseq [c chans] (<!! c))
      (let [{:keys [writes durable]} (<!! (store/restore s))]
        (is (= 40 (count writes)) "no record lost")
        (is (= (range 40) (map #(get-in % [:writes :n]) writes)) "log order is issue order")
        (is (= {:n 39} durable))))
    (<!! (store/close-store! s))))

(deftest truncate-from-survives-the-round-trip
  (testing "replay metadata, carried rather than acted on"
    (let [s (kstore/konserve-store (<!! (new-mem-store)))]
      (<!! (store/write! s {:writes {:entries [:a :b]} :durable? true :truncate-from 4}))
      (let [r (first (:writes (<!! (store/restore s))))]
        ;; A store that dropped this would leave a restarting Raft unable to
        ;; tell an append from an overwrite-at-a-lower-index.
        (is (= 4 (:truncate-from r))))
      (<!! (store/close-store! s)))))

(deftest a-restarted-runtime-is-handed-what-landed
  (testing "init sees :restored, in the two views sim/restart supplies"
    (let [s (store/memory-store)
          captured (atom nil)
          node (->ProbeNode #{}
                            (fn [config] (reset! captured (:restored config))
                              {:state {} :effects []})
                            (fn [st _] (n/result st [])))]
      (<!! (store/write! s {:writes {:hard-state {:term 7}} :durable? true}))
      (<!! (store/write! s {:writes {:last-signed {:height 3}} :durable? true}))
      (let [runtime (start! {:node node :store s})]
        (is (= {:term 7} (get-in @captured [:durable :hard-state])))
        (is (= {:height 3} (get-in @captured [:durable :last-signed])))
        (is (= 2 (count (:writes @captured))))
        (<!! (rt/stop-runtime! runtime))))))

(deftest a-fresh-runtime-is-handed-empty-views-not-nil
  (testing "so a fresh node and a restarted one take the same code path"
    (let [captured (atom :unset)
          node (->ProbeNode #{}
                            (fn [config] (reset! captured (:restored config))
                              {:state {} :effects []})
                            (fn [st _] (n/result st [])))
          runtime (start! {:node node})]
      (is (= {:durable {} :writes []} @captured))
      (<!! (rt/stop-runtime! runtime)))))

;; ============================================================
;; The loop reports rather than dying quietly
;; ============================================================

(deftest an-undeclared-effect-halts-and-is-reported
  (let [runtime (start! {:node (echo-node #{:commit}) :on-error (fn [_])})]
    (rt/send-event! runtime {:type :go :fx [(n/resync [:x])]})
    (settle!)
    (let [e (rt/last-error runtime)]
      (is (some? e))
      (is (= "node emitted an effect it did not declare" (ex-message e)))
      (is (= :resync (:effect (ex-data e)))))))

(deftest the-error-handler-sees-the-exception
  (let [seen (atom nil)
        runtime (start! {:node (echo-node #{:commit :revert})
                         :on-error (fn [e] (reset! seen e))})]
    (commit! runtime [:a])
    (rt/send-event! runtime {:type :go :fx [(n/revert :a [:nope])]})
    (settle!)
    (is (some? @seen))
    (is (identical? @seen (rt/last-error runtime)))))

;; ============================================================
;; A malformed message is a dropped packet, not a kill switch
;; ============================================================

(defrecord ThrowingNode [emits on-remote?]
  n/Node
  (capabilities [_] {:emits emits :topics #{:t}})
  (init [_ _] {:state {} :effects []})
  (step [_ st input]
    (if (and on-remote? (= :message-received (:type input)))
      (throw (ClassCastException. "class java.lang.String cannot be cast to Number"))
      (n/result st (:fx input [])))))

(deftest a-message-the-node-cannot-process-is-dropped-not-fatal
  (testing "`handle-loop-error!` halts the event loop permanently and never
            restarts it. That is correct for an invariant violation and
            catastrophic when a stranger picks the moment.

            Verified against the real algorithms before this guard existed: one
            broadcast of `{:kind :finalized :proposal nil :height \"boom\"}`
            makes round-robin evaluate `(> \"boom\" height)`, throw
            ClassCastException, and halt every node that receives it, from
            height 0, permanently. Sixty bytes for the whole cluster.
            Tendermint and Nakamoto validate their message fields; round-robin,
            Bullshark and SCP do not.

            Dropping is safe because `step` is pure -- a throw leaves us on the
            state we had, with no half-applied input to reconcile."
    (let [runtime (start! {:node (->ThrowingNode #{:log} true) :validators [:p1 :p2]})]
      (dotimes [_ 5]
        (rt/send-event! runtime {:type :message-received :from :p2
                                 :verified-by #{:p2} :msg {:kind :junk}}))
      (settle!)
      (is (nil? (rt/last-error runtime)) "the node is not in an error state")
      (is (true? @(:running? runtime)) "and its event loop is still running")
      (is (= 5 (rt/dropped-messages runtime))
          "with the drops COUNTED -- a drop nobody can count is
           indistinguishable from a quiet network")
      (<!! (rt/stop-runtime! runtime)))))

(deftest an-invariant-violation-still-halts-the-node
  (testing "the distinction this rests on. A `step` that throws on a MESSAGE is
            a message the algorithm could not handle. An EFFECT that throws is
            this node discovering it is wrong about its own history -- which is
            exactly what fail-stop is for, whatever input led there.

            Without this, the containment above would have quietly converted
            every invariant violation into a shrug."
    (let [runtime (start! {:node (echo-node #{:commit :revert}) :validators [:p1]})]
      (commit! runtime [:a :b :c])
      ;; :dropped disagrees with the committed tail -- an invariant violation,
      ;; and it arrives here on an ordinary event.
      (rt/send-event! runtime {:type :go :fx [(n/revert :a [:x :y])]})
      (settle!)
      (is (some? (rt/last-error runtime)) "still fatal")
      (is (false? @(:running? runtime)) "and still fail-stop")
      (is (zero? (rt/dropped-messages runtime))
          "and not miscounted as a dropped message")
      (<!! (rt/stop-runtime! runtime)))))

;; ============================================================
;; Timers: re-arming must not orphan the previous arming
;; ============================================================

(defrecord TimerProbe [fired]
  n/Node
  (capabilities [_] {:emits #{:set-timer :cancel-timer} :topics #{:t}})
  (init [_ _] {:state {} :effects []})
  (step [_ st input]
    (when (= :timer-fired (:type input))
      (swap! fired conj (:timer-id input)))
    (n/result st (:fx input []))))

(deftest re-arming-a-timer-does-not-leave-the-old-one-running
  (testing "`cancel-timer` was unreliable, and the map lied about it

           Registration happened inside the `go-try-`, so it landed some time
           after the effect was interpreted; and both `alt!` branches ended in
           an unconditional `dissoc` with no check that the entry was theirs.
           So re-arming went: arming 2 cancels arming 1 and installs itself;
           arming 1 then wakes on its cancel channel and deletes arming 2's
           entry, while arming 2's timeout is still live. The map is empty and
           a timer is still running, so the next `cancel-timer` cancels
           nothing.

           Measured before the fix, and this is exactly it: arm, arm, cancel --
           the map is empty and the timer fires anyway.

           It bites hardest where timers are re-armed constantly. Raft re-arms
           `:election` on every heartbeat, so a follower accumulated orphaned
           election timers firing at random: spurious elections, term
           inflation, leader churn. The simulator cannot see any of it --
           `set-timer` there is `assoc-in` and `cancel-timer` is `dissoc`, both
           synchronous and exact."
    (let [fired (atom [])
          runtime (start! {:node (->TimerProbe fired) :validators [:p1] :tick-ms 50})]
      (rt/send-event! runtime {:type :go :fx [(n/set-timer :x 2)]})
      (rt/send-event! runtime {:type :go :fx [(n/set-timer :x 2)]})
      (<!! (timeout 30))
      (rt/send-event! runtime {:type :go :fx [(n/cancel-timer :x)]})
      (<!! (timeout 500))
      (is (empty? @fired)
          "a cancelled timer does not fire, however many times it was armed")
      (is (empty? @(:timers runtime))
          "and the map agrees, rather than being empty because an arming
           deleted somebody else's entry")
      (<!! (rt/stop-runtime! runtime)))))

(deftest a-re-armed-timer-still-fires-once
  (testing "the other direction: the fix must not cancel everything. Arming
            twice and NOT cancelling should still produce exactly one firing --
            the second arming replaces the first rather than adding to it."
    (let [fired (atom [])
          runtime (start! {:node (->TimerProbe fired) :validators [:p1] :tick-ms 50})]
      (rt/send-event! runtime {:type :go :fx [(n/set-timer :x 2)]})
      (rt/send-event! runtime {:type :go :fx [(n/set-timer :x 2)]})
      (<!! (timeout 500))
      (is (= [:x] @fired) "exactly one firing, not two and not none")
      (<!! (rt/stop-runtime! runtime)))))

;; ============================================================
;; Storage faults
;; ============================================================

(defrecord FailingStore [failures]
  store/DurableStore
  (write! [_ _] (swap! failures inc) (go (ex-info "disk on fire" {:simulated true})))
  (restore [_] (go {:durable {} :writes []}))
  (close-store! [_] (go true)))

(deftest a-failed-durable-write-is-fatal-and-loud
  (testing "it used to be silent, which is worse than fatal

           `<?-` throws, `go-try-` puts the exception on the channel it
           returns, and `interpret-effects` discards that channel. So the node
           never received `persisted`, its `:then` never fired, `last-error`
           stayed nil and `running?` stayed true.

           Tendermint, Bullshark and SCP all put `commit` in that `:then`.
           Measured before the fix: a store failing every write produced a node
           that committed nothing, reported no error, and was
           indistinguishable from a node on a quiet network.

           Fail-stop rather than retry: the algorithm is waiting on a promise
           the store could not keep, and continuing without the write is the
           safety violation the barrier exists to prevent. A deployment wanting
           retries supplies a retrying `DurableStore`, which is the layer where
           'how many times' can be answered.

           Note the asymmetry this removed. The BUFFERED branch already read
           its result and warned -- its comment says 'a failure that no one
           looks at is a write the node believes it made'. The durable branch
           is the one that matters more and was the one not looking."
    (let [failures (atom 0)
          committed (atom [])
          errors (atom [])
          runtime (start! {:node (echo-node #{:persist-then :commit})
                           :validators [:p1]
                           :store (->FailingStore failures)
                           :on-error (fn [e] (swap! errors conj e))
                           :on-finalize (fn [vs] (swap! committed into vs))})]
      (rt/send-event! runtime {:type :go
                               :fx [(n/persist-then {:writes {:k 1} :durable? true
                                                     :then [(n/commit [:v1])]})]})
      (settle!)
      (is (pos? @failures) "the store really was asked to write")
      (is (empty? @committed)
          "nothing gated may escape a barrier that was not honoured")
      (is (some? (rt/last-error runtime)) "and the failure is RECORDED")
      (is (false? @(:running? runtime)) "fail-stop, not a silent stall")
      (is (seq @errors) "and the application's :on-error hook is told")
      (<!! (rt/stop-runtime! runtime)))))

(deftest a-failed-buffered-write-is-not-fatal
  (testing "the other half of the asymmetry. `:durable? false` means the write
            MAY be lost -- the node was deliberately told before the store
            confirmed -- so losing it is the contract being met, not broken. It
            warns; it does not halt."
    (let [runtime (start! {:node (echo-node #{:persist-then})
                           :validators [:p1]
                           :store (->FailingStore (atom 0))})]
      (rt/send-event! runtime {:type :go
                               :fx [(n/persist-then {:writes {:k 1} :durable? false})]})
      (settle!)
      (is (nil? (rt/last-error runtime)))
      (is (true? @(:running? runtime))
          "a lost buffered write is not a reason to stop the node")
      (<!! (rt/stop-runtime! runtime)))))
