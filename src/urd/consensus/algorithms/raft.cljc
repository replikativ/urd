(ns urd.consensus.algorithms.raft
  "Raft as a pure state machine on `urd.consensus.node`.

  Ported from `etcd-io/raft` (read at Aug 2026). Scope: leader election with
  PreVote, log replication with per-peer progress, durable hard state and log
  entries, and log truncation on a conflicting suffix. Out of scope: snapshots,
  configuration changes, leadership transfer, read-index/lease reads,
  CheckQuorum, and inflight-based flow control.

  ## The durability barrier

  `raft.go:546` routes exactly {MsgAppResp, MsgVoteResp, MsgPreVoteResp} into
  `msgsAfterAppend`; everything else is sent immediately. Those three are the
  node's binding commitments: acknowledging an append or publishing a vote is a
  promise that survives a restart. Here they go into `:then` of a `persist-then`
  and everything else is a bare `:send`.

  `durable?` follows `MustSync` (`rawnode.go:191-198`): fsync iff entries are
  non-empty, or the vote changed, or the term changed. A commit-index change
  alone is recoverable by replay, so it is a buffered write.

  ## The self-addressed message, and why we do not use one

  etcd-raft models the leader's own durability as a `MsgAppResp` from itself to
  itself, delayed by the fsync (`raft.go:845`), and the candidate's self-vote as
  a `MsgVoteResp` from itself to itself (`raft.go:1059`). That removes the
  leader/follower asymmetry from commit advancement: the leader's own entry
  counts toward the quorum only once durable, exactly like everyone else's.

  We keep the *semantics* but not the mechanism. urd has no effect for
  \"deliver this event to myself\", and routing a self-addressed message through
  `[:send ...]` would send it over the simulated network, where it can be
  delayed, duplicated, or dropped -- a self-ack that the drop-rate can lose is a
  liveness bug. Instead the node arms `:self-ack` / `:self-vote` on its own
  state and consumes them when the matching `persisted` event arrives. The
  ordering guarantee is identical (the ack lands after the write is durable,
  before the gated messages go out), and it stays inside the state machine.

  ## The ABA hazard

  `rawnode.go:266-363` explains it at length: a persist completion must be
  dropped if the term changed while it was in flight, or a stale completion
  marks entries durable that a newer append has since overwritten. urd's
  `persist-then` carries `:epoch` and the `persisted` event echoes it, so we set
  `:epoch` to the term at issue time and treat a mismatch as a no-op.

  There is a wrinkle: `persisted` carries a `token` the *interpreter* chose, and
  the node never saw it, so a completion cannot be correlated with the write
  that produced it. We therefore keep `:pending-writes` as a FIFO queue and pop
  the front on each completion, which is correct only because interpreters
  complete writes in issue order. See the friction notes in the PR.

  ## Truncation

  `log.go:109-131` (`maybeAppend`) plus `log_unstable.go:191-213`
  (`truncateAndAppend`). etcd-raft leaves the truncation implicit -- storage has
  to infer it from an append at a lower index. We set `:truncate-from` on the
  `persist-then` instead. Note that a conflict at or below the commit index is a
  Raft invariant violation; etcd-raft panics, and so do we.

  ## Portability

  Everything here is `.cljc` with no host interop except one character-code
  helper. Time is logical (`set-timer`, in ticks) and the randomized election
  timeout is derived from a portable hash of (peer-id, term) rather than from a
  host PRNG -- urd has no effect that yields a random *number*, only one that
  yields random *peers*."
  (:require [urd.consensus.node :as node]
            [urd.consensus.rng :as rng]))

;; ============================================================
;; Portable pseudo-randomness for the election timeout
;; ============================================================

(defn- char-code [^String s i]
  #?(:clj (int (.charAt s i))
     :cljs (.charCodeAt s i)))

(def ^:private hash-modulus
  "The largest prime below 2^32. Keeping the accumulator under it bounds the
  multiply below, which is the whole point -- see `string-hash`."
  4294967291)

(defn- string-hash
  "A portable djb2-style hash: h = (33h + c) mod (2^32 - 5).

  The arithmetic is chosen so that BOTH platforms compute it exactly. Clojure
  would throw on 64-bit overflow; ClojureScript, whose numbers are doubles,
  would silently lose the low bits above 2^53 and diverge -- which is far worse,
  because the result still looks like a number. The largest intermediate here is
  33 * (2^32 - 6) + 65535, about 1.4e11, comfortably below 2^53. A 32-bit FNV-1a
  would NOT be safe: its multiply reaches 7.2e16."
  [s]
  (loop [h 5381, i 0]
    (if (>= i (count s))
      h
      (recur (mod (+ (* h 33) (char-code s i)) hash-modulus) (inc i)))))

(defn randomized-election-timeout
  "A timeout in [et, 2*et), deterministic in (peer-id, term).

  etcd-raft draws this from `globalRand` (`raft.go`,
  `resetRandomizedElectionTimeout`). We cannot: a state machine may not draw a
  random number, and urd's `:sample` effect returns random PEERS, not a random
  number. Deriving it from (id, term) instead keeps runs replayable and still
  breaks split votes, because two nodes campaigning in the same term get
  different offsets -- while a node that re-campaigns gets a different offset
  each term, which is what actually resolves a repeated split."
  [id term et]
  (let [[w _] (rng/next-word (rng/make (string-hash (str id "@" term))))]
    (+ et (mod w (max 1 et)))))

;; ============================================================
;; The log
;;
;; No snapshots, so the first index is always 1 and entry i sits at position
;; (dec i). An entry is {:index i :term t :data d}.
;; ============================================================

(defn last-index [st] (count (:log st)))

(defn entry-at
  "The entry at `i`, or nil if out of range."
  [st i]
  (when (and (pos? i) (<= i (count (:log st))))
    (nth (:log st) (dec i))))

(defn term-at
  "The term at index `i`, or nil if unknown.

  Index 0 is the sentinel before the log with term 0, which is what makes an
  append anchored at (index 0, term 0) match an empty log."
  [st i]
  (cond
    (zero? i) 0
    (<= i (count (:log st))) (:term (nth (:log st) (dec i)))
    :else nil))

(defn last-term [st] (or (term-at st (last-index st)) 0))

(defn- match-term? [st i t]
  (= t (term-at st i)))

(defn up-to-date?
  "Raft 5.4.1: is (last-term, last-index) at least as up to date as ours?"
  [st cand-term cand-index]
  (let [lt (last-term st)
        li (last-index st)]
    (or (> cand-term lt)
        (and (= cand-term lt) (>= cand-index li)))))

(defn find-conflict
  "`log.go:154-167`. The index of the first entry whose term disagrees with
  ours, or the first index past our log, or 0 if the entries are all already
  present."
  [st entries]
  (loop [es (seq entries)]
    (if-not es
      0
      (let [e (first es)]
        (if (match-term? st (:index e) (:term e))
          (recur (next es))
          (:index e))))))

(defn find-conflict-by-term
  "`log.go:182-194`. The max guess <= `index` with term(guess) <= `term`, or
  where our term is unknown. Returns [index term].

  Used on BOTH sides of a rejection: the follower computes the hint, the leader
  consumes it to skip a whole term at a time instead of decrementing by one."
  [st index term]
  (loop [i index]
    (if (zero? i)
      [0 0]
      (let [ours (term-at st i)]
        (cond
          (nil? ours) [i 0]
          (<= ours term) [i ours]
          :else (recur (dec i)))))))

(defn- truncate-log
  "Drop every entry at or above `from`."
  [st from]
  (update st :log #(vec (take (dec from) %))))

;; ============================================================
;; Quorum arithmetic
;;
;; Ported from etcd-raft's `quorum` package so the conformance corpus there can
;; be replayed byte-for-byte. `nil` in `acked` is etcd's "no information", which
;; is deliberately distinct from index 0.
;; ============================================================

(def max-index
  "The committed index of an EMPTY config.

  etcd uses math.MaxUint64 (rendered `∞`) so that a half-populated joint config
  behaves like the populated half under `min`. We use `##Inf`, which is the same
  identity element for `min` and is portable -- a 64-bit unsigned literal is
  not, since ClojureScript has no 64-bit integers."
  ##Inf)

(defn committed-index
  "`quorum/majority.go:120-162`. The largest index acked by a majority of `ids`.

  Voters with no information contribute 0, which is why the slice is filled from
  the right before sorting -- the unfilled slots are the zeroes that end up on
  the left. The answer is the element at position n - (n/2 + 1)."
  [ids acked]
  (let [n (count ids)]
    (if (zero? n)
      max-index
      (let [present (->> ids (keep #(get acked %)) sort vec)
            missing (- n (count present))
            srt (into (vec (repeat missing 0)) present)]
        (nth srt (- n (inc (quot n 2))))))))

(defn vote-result
  "`quorum/majority.go:165-198`. :won, :lost, or :pending.

  Tri-state, and that matters: a candidate that has merely not-yet-won must keep
  waiting, while one that has lost must step down immediately."
  [ids votes]
  (if (zero? (count ids))
    :won
    (let [q (inc (quot (count ids) 2))
          granted (count (filter #(true? (get votes %)) ids))
          missing (count (remove #(contains? votes %) ids))]
      (cond
        (>= granted q) :won
        (>= (+ granted missing) q) :pending
        :else :lost))))

(defn joint-committed-index
  "`quorum/joint.go:47-56`. Committed in both halves."
  [ids0 ids1 acked]
  (min (committed-index ids0 acked) (committed-index ids1 acked)))

(defn joint-vote-result
  "`quorum/joint.go:58-75`. Both halves must agree; either losing loses."
  [ids0 ids1 votes]
  (let [r1 (vote-result ids0 votes)
        r2 (vote-result ids1 votes)]
    (cond
      (= r1 r2) r1
      (or (= r1 :lost) (= r2 :lost)) :lost
      :else :pending)))

;; ============================================================
;; Per-peer progress (etcd-raft `tracker.Progress`, minus Inflights)
;;
;; Flow control by inflight count/bytes is out of scope, so a peer in
;; :replicate is never throttled and `paused?` reduces to "a probe is
;; outstanding".
;; ============================================================

(defn- new-progress [next-idx]
  {:match 0 :next next-idx :state :probe :flow-paused? false :sent-commit 0})

(defn- paused? [pr]
  (and (= :probe (:state pr)) (:flow-paused? pr)))

(defn- become-probe [pr]
  (assoc pr :state :probe :flow-paused? false
         :next (inc (:match pr))
         :sent-commit (min (:sent-commit pr) (:match pr))))

(defn- become-replicate [pr]
  (assoc pr :state :replicate :flow-paused? false :next (inc (:match pr))))

(defn- maybe-update
  "Progress on an accepted MsgAppResp. Returns [pr' changed?]."
  [pr n]
  (if (<= n (:match pr))
    [pr false]
    [(assoc pr :match n :next (max (:next pr) (inc n)) :flow-paused? false) true]))

(defn- maybe-decr-to
  "`tracker/progress.go:225-254`. Returns [pr' changed?].

  A rejection whose index does not line up with what we probed is stale -- a
  reordered or duplicated message -- and must not move the progress."
  [pr rejected match-hint]
  (if (= :replicate (:state pr))
    (if (<= rejected (:match pr))
      [pr false]
      (let [nxt (inc (:match pr))]
        [(assoc pr :next nxt :sent-commit (min (:sent-commit pr) (dec nxt))) true]))
    (if (not= (dec (:next pr)) rejected)
      [pr false]
      (let [nxt (max (min rejected (inc match-hint)) (inc (:match pr)))]
        [(assoc pr :next nxt :flow-paused? false
                :sent-commit (min (:sent-commit pr) (dec nxt))) true]))))

(defn- sent-entries [pr n]
  (case (:state pr)
    :replicate (if (pos? n) (update pr :next + n) pr)
    :probe (if (pos? n) (assoc pr :flow-paused? true) pr)
    pr))

(defn- can-bump-commit? [pr index]
  (and (> index (:sent-commit pr)) (< (:sent-commit pr) (dec (:next pr)))))

;; ============================================================
;; Effect accumulation
;;
;; Helpers thread the node state and stash pending effects under :fx, which is
;; stripped before the state is returned. `step` is still a pure function of
;; (state, input); :fx just spares every helper an explicit accumulator.
;; ============================================================

(defn- fresh-fx [st]
  (assoc st :fx {:msgs []                       ; sent immediately
                 :after []                      ; gated behind the durability barrier
                 :logs []                       ; diagnostics
                 :commits []                    ; entries to hand to the application
                 :truncate-from nil
                 :appended? false
                 :hs0 {:term (:term st) :vote (:vote st) :commit (:commit st)}}))

(defn- emit [st effect] (update-in st [:fx :msgs] conj effect))
(defn- emit-after [st effect] (update-in st [:fx :after] conj effect))
(defn- log-line [st level msg] (update-in st [:fx :logs] conj (node/log-effect level msg)))

(def ^:private gated-types
  "raft.go:546 -- exactly the messages that constitute a binding commitment."
  #{:app-resp :vote-resp :pre-vote-resp})

(defn- send-msg
  "Route a message: gated behind the barrier, or straight out."
  [st to msg]
  (let [msg (assoc msg :from (:id st))
        e (node/send-to to msg)]
    (if (gated-types (:type msg))
      (emit-after st e)
      (emit st e))))

;; ============================================================
;; Timers
;; ============================================================

(defn- arm-election-timer [st]
  (emit st (node/set-timer :election
                           (randomized-election-timeout (:id st) (:term st)
                                                        (:election-timeout st)))))

(defn- arm-heartbeat-timer [st]
  (emit st (node/set-timer :heartbeat (:heartbeat-timeout st))))

(defn- arm-propose-timer [st]
  (if-let [n (:propose-interval st)]
    (emit st (node/set-timer :propose n))
    st))

;; ============================================================
;; Commit
;; ============================================================

(defn- commit-to
  "Advance the commit index, never backwards. `log.go:322-331` panics if asked to
  commit past the end of the log; so do we, because that means the log was
  truncated or lost."
  [st to]
  (if (<= to (:commit st))
    st
    (do
      (when (< (last-index st) to)
        (throw (ex-info "commit index past the end of the log"
                        {:to to :last-index (last-index st) :id (:id st)})))
      (assoc st :commit to))))

(defn- flush-commits
  "Hand every newly committed entry to the application, in order.

  Raft never reverts a *committed* entry -- a conflicting suffix is by
  construction above the commit index -- so this algorithm emits `:commit` and
  never `:revert`."
  [st]
  (let [applied (:applied st)
        commit (:commit st)]
    (if (<= commit applied)
      st
      (let [ents (subvec (:log st) applied commit)]
        (-> st
            (assoc :applied commit)
            (update-in [:fx :commits] conj (node/commit ents commit)))))))

;; ============================================================
;; Sending appends
;; ============================================================

(declare maybe-send-append)

(defn- send-append
  "Unconditionally try to append to `to`, discarding whether anything went."
  [st to]
  (first (maybe-send-append st to true)))

(defn- maybe-send-append
  "`raft.go:618-662`. Returns [st sent?].

  `send-if-empty?` distinguishes a probe or commit-index carrier (which must go
  even with no entries) from batch replication (which must not spin sending
  empty messages)."
  [st to send-if-empty?]
  (let [pr (get-in st [:progress to])]
    (if (or (nil? pr) (paused? pr))
      [st false]
      (let [prev-index (dec (:next pr))
            prev-term (term-at st prev-index)]
        (if (nil? prev-term)
          ;; Would need a snapshot; out of scope for this PR.
          [(log-line st :warn (str "cannot append to " to
                                   ": log does not reach index " prev-index
                                   " (snapshot required, unimplemented)"))
           false]
          (let [ents (vec (subvec (:log st) prev-index))]
            (if (and (empty? ents) (not send-if-empty?))
              [st false]
              [(-> st
                   (send-msg to {:type :app
                                 :term (:term st)
                                 :prev-index prev-index
                                 :prev-term prev-term
                                 :entries ents
                                 :commit (:commit st)})
                   (update-in [:progress to]
                              #(-> % (sent-entries (count ents))
                                   (assoc :sent-commit (:commit st)))))
               true])))))))

(defn- bcast-append [st]
  (reduce (fn [s to] (if (= to (:id s)) s (send-append s to)))
          st (:validators st)))

(defn- send-heartbeat [st to]
  (let [pr (get-in st [:progress to])
        c (min (:match pr) (:commit st))]
    (-> st
        (send-msg to {:type :heartbeat :term (:term st) :commit c})
        (assoc-in [:progress to :sent-commit] c))))

(defn- bcast-heartbeat [st]
  (reduce (fn [s to] (if (= to (:id s)) s (send-heartbeat s to)))
          st (:validators st)))

;; ============================================================
;; Role transitions
;; ============================================================

(defn- reset-state
  "`raft.go:781-810`. Clears per-term state and re-seeds every peer's progress
  at the end of our log."
  [st term]
  (let [st (if (not= (:term st) term) (assoc st :term term :vote nil) st)
        li (last-index st)]
    (-> st
        (assoc :lead nil
               :votes {}
               :self-vote nil
               :self-ack nil
               :progress (into {} (map (fn [p]
                                         [p (cond-> (new-progress (inc li))
                                              (= p (:id st)) (assoc :match li))]))
                               (:validators st))))))

(defn- become-follower [st term lead]
  (-> st
      (reset-state term)
      (assoc :role :follower :lead lead)
      (log-line :info (str (:id st) " became follower at term " term))
      arm-election-timer
      (emit (node/cancel-timer :heartbeat))
      (emit (node/cancel-timer :propose))))

(defn- become-candidate [st]
  (let [term (inc (:term st))]
    (-> st
        (reset-state term)
        (assoc :role :candidate :vote (:id st))
        (log-line :info (str (:id st) " became candidate at term " term))
        arm-election-timer)))

(defn- become-pre-candidate
  "`raft.go:917-931`. Changes role and clears votes but does NOT bump the term or
  record a vote -- that is the entire point of PreVote: a partitioned node that
  rejoins does not disrupt the cluster by arriving with an inflated term."
  [st]
  (-> st
      (assoc :role :pre-candidate :votes {} :lead nil :self-vote nil)
      (log-line :info (str (:id st) " became pre-candidate at term " (:term st)))
      arm-election-timer))

(declare append-entries)

(defn- become-leader [st]
  (let [st (-> st
               (reset-state (:term st))
               (assoc :role :leader :lead (:id st))
               (update-in [:progress (:id st)] become-replicate)
               (log-line :info (str (:id st) " became leader at term " (:term st)))
               (emit (node/cancel-timer :election))
               arm-heartbeat-timer
               arm-propose-timer)]
    ;; A new leader appends an empty entry at its own term. Raft 5.4.2: it may
    ;; not commit an entry from an earlier term by counting replicas, so it
    ;; needs one of its own to commit before the earlier ones follow.
    (append-entries st [nil])))

;; ============================================================
;; Appending
;; ============================================================

(defn- append-entries
  "Append `payloads` at the leader's current term, then arm the self-ack.

  The self-ack stands in for etcd-raft's self-addressed MsgAppResp
  (`raft.go:845`): the leader's own entry counts toward the commit quorum only
  once the write is durable."
  [st payloads]
  (let [li (last-index st)
        ents (vec (map-indexed (fn [i d] {:index (+ li 1 i) :term (:term st) :data d})
                               payloads))]
    (-> st
        (update :log into ents)
        (assoc-in [:fx :appended?] true)
        (assoc :self-ack (+ li (count ents))))))

;; ============================================================
;; Vote handling
;; ============================================================

(defn- record-vote [st from granted?]
  (assoc-in st [:votes from] granted?))

(defn- poll
  "Record a vote and re-tally. Returns [st result]."
  [st from granted? kind]
  (let [st (-> st
               (record-vote from granted?)
               (log-line :info (str (:id st) " received " kind
                                    (if granted? " from " " rejection from ")
                                    from " at term " (:term st))))
        res (vote-result (:validators st) (:votes st))]
    [(log-line st :info (str (:id st) " has received "
                             (count (filter true? (vals (:votes st)))) " " kind
                             " votes and "
                             (count (filter false? (vals (:votes st)))) " vote rejections"))
     res]))

(declare campaign)

(defn- win-election [st]
  (if (= :pre-candidate (:role st))
    (campaign st :election)
    (bcast-append (become-leader st))))

(defn- campaign
  "`raft.go:1025-1073`. `kind` is :pre-election or :election."
  [st kind]
  (let [pre? (= :pre-election kind)
        st (if pre? (become-pre-candidate st) (become-candidate st))
        term (if pre? (inc (:term st)) (:term st))
        msg-type (if pre? :pre-vote :vote)
        st (assoc st :self-vote {:term term :kind msg-type})]
    (reduce (fn [s to]
              (if (= to (:id s))
                s
                (-> s
                    (log-line :info (str (:id s) " [logterm: " (last-term s)
                                         ", index: " (last-index s) "] sent "
                                         (name msg-type) " request to " to
                                         " at term " (:term s)))
                    (send-msg to {:type msg-type
                                  :term term
                                  :index (last-index s)
                                  :log-term (last-term s)}))))
            st
            (:validators st))))

(defn- hup [st]
  (cond
    (= :leader (:role st))
    (log-line st :debug (str (:id st) " ignoring election tick because already leader"))

    (not (contains? (set (:validators st)) (:id st)))
    (log-line st :warn (str (:id st) " is not a voter and cannot campaign"))

    :else
    (-> st
        (log-line :info (str (:id st) " is starting a new election at term " (:term st)))
        (campaign (if (:pre-vote? st) :pre-election :election)))))

;; ============================================================
;; AppendEntries
;; ============================================================

(defn- handle-append-entries
  "`raft.go:1791-1833` plus `log.go:109-131`.

  Three outcomes: the append is entirely below our commit index (ack the commit
  index and move on), the append matches and is absorbed, or it conflicts and we
  return a hint that lets the leader skip a whole term."
  [st from {:keys [prev-index prev-term entries commit]}]
  (cond
    (< prev-index (:commit st))
    (send-msg st from {:type :app-resp :term (:term st) :index (:commit st)})

    (match-term? st prev-index prev-term)
    (let [last-new (+ prev-index (count entries))
          ci (find-conflict st entries)
          st (cond
               (zero? ci) st

               (<= ci (:commit st))
               ;; etcd-raft panics here (log.go:121) and it is right to: a
               ;; conflict at or below the commit index means two leaders
               ;; committed different entries at the same index, which is a
               ;; violated safety property, not a recoverable condition.
               (throw (ex-info "conflicting entry at or below the commit index"
                               {:id (:id st) :conflict ci :commit (:commit st)}))

               :else
               (let [offset (inc prev-index)
                     new-ents (vec (drop (- ci offset) entries))
                     truncating? (<= ci (last-index st))]
                 (cond-> st
                   truncating?
                   (-> (log-line :info (str "found conflict at index " ci
                                            " [existing term: " (or (term-at st ci) 0)
                                            ", conflicting term: "
                                            (:term (nth entries (- ci offset))) "]"))
                       (truncate-log ci)
                       (assoc-in [:fx :truncate-from] ci)
                       ;; Anything we already handed to storage above the
                       ;; truncation point is no longer ours to claim.
                       (update :issued min (dec ci))
                       (update :stable min (dec ci)))

                   true
                   (-> (update :log into new-ents)
                       (assoc-in [:fx :appended?] true)))))]
      (-> st
          (commit-to (min commit last-new))
          flush-commits
          (send-msg from {:type :app-resp :term (:term st) :index last-new})))

    :else
    (let [hint-index (min prev-index (last-index st))
          [hi ht] (find-conflict-by-term st hint-index prev-term)]
      (-> st
          (log-line :debug (str (:id st) " [logterm: " (or (term-at st prev-index) 0)
                                ", index: " prev-index "] rejected app [logterm: "
                                prev-term ", index: " prev-index "] from " from))
          (send-msg from {:type :app-resp :term (:term st) :index prev-index
                          :reject? true :reject-hint hi :log-term ht})))))

(defn- handle-heartbeat [st from {:keys [commit]}]
  (-> st
      (commit-to commit)
      flush-commits
      (send-msg from {:type :heartbeat-resp :term (:term st)})))

;; ============================================================
;; Leader: commit advancement
;; ============================================================

(defn- maybe-commit
  "`raft.go:775-779`. Returns [st advanced?].

  Raft 5.4.2 is the subtle part: the leader may only advance the commit index to
  an entry from its OWN term. Counting replicas of an entry from an earlier term
  is exactly the Figure-8 bug."
  [st]
  (let [acked (into {} (map (fn [[p pr]] [p (:match pr)])) (:progress st))
        mci (committed-index (:validators st) acked)]
    (if (and (> mci (:commit st))
             (= (:term st) (term-at st mci)))
      [(flush-commits (commit-to st mci)) true]
      [st false])))

(defn- handle-app-resp
  "`raft.go:1384-1578`."
  [st from {:keys [index reject? reject-hint log-term]}]
  (let [pr (get-in st [:progress from])]
    (if (nil? pr)
      (log-line st :debug (str (:id st) " no progress available for " from))
      (if reject?
        (let [;; The leader-side half of the term-skipping optimisation: given
              ;; the follower is at `log-term` at `reject-hint`, every index
              ;; where our term exceeds `log-term` must fail too, so jump past
              ;; them in one go instead of decrementing.
              next-probe (if (and log-term (pos? log-term))
                           (first (find-conflict-by-term st reject-hint log-term))
                           reject-hint)
              [pr' changed?] (maybe-decr-to pr index next-probe)
              st (log-line st :debug
                           (str (:id st) " received app-resp(rejected, hint: (index "
                                reject-hint ", term " log-term ")) from " from
                                " for index " index))]
          (if-not changed?
            st
            (let [pr' (if (= :replicate (:state pr')) (become-probe pr') pr')
                  st (assoc-in st [:progress from] pr')]
              (-> st
                  (log-line :debug (str (:id st) " decreased progress of " from
                                        " to [" (:state pr') " match=" (:match pr')
                                        " next=" (:next pr') "]"))
                  (send-append from)))))
        (let [[pr' changed?] (maybe-update pr index)]
          (if-not (or changed?
                      (and (= (:match pr) index) (= :probe (:state pr))))
            st
            (let [pr' (if (= :probe (:state pr')) (become-replicate pr') pr')
                  st (assoc-in st [:progress from] pr')
                  [st advanced?] (maybe-commit st)]
              (cond-> st
                advanced? bcast-append

                (and (not advanced?) (not= from (:id st))
                     (can-bump-commit? (get-in st [:progress from]) (:commit st)))
                (send-append from)

                ;; Drain whatever else we have for this peer, without sending
                ;; empty messages just to say nothing.
                (not= from (:id st))
                (as-> s (loop [s s, guard 0]
                          (let [[s' sent?] (maybe-send-append s from false)]
                            (if (and sent? (< guard 1000)) (recur s' (inc guard)) s'))))))))))))

(defn- handle-heartbeat-resp
  "`raft.go:1579-1598`.

  Clearing `flow-paused?` here is the whole recovery path, and it is easy to
  miss: a probe sent into a partition sets the pause and no response ever
  arrives to clear it, so without this the peer is throttled forever. This is
  what `heartbeat_resp_recovers_from_probing.txt` exists to catch."
  [st from]
  (let [pr (get-in st [:progress from])]
    (if (nil? pr)
      st
      (let [st (assoc-in st [:progress from :flow-paused?] false)]
        (if (or (< (:match pr) (last-index st)) (= :probe (:state pr)))
          (send-append st from)
          st)))))

;; ============================================================
;; Term handling and dispatch
;; ============================================================

(defn- vote-resp-type [t] (if (= t :pre-vote) :pre-vote-resp :vote-resp))

(defn- handle-vote-request
  "`raft.go:1212-1262`. One predicate decides it: we may vote if this repeats a
  vote we already cast, or we have neither voted nor seen a leader this term, or
  it is a PreVote for a future term (which binds nothing) -- AND the candidate's
  log is at least as up to date as ours."
  [st from {:keys [type term index log-term]}]
  (let [can-vote? (or (= (:vote st) from)
                      (and (nil? (:vote st)) (nil? (:lead st)))
                      (and (= type :pre-vote) (> term (:term st))))]
    (if (and can-vote? (up-to-date? st log-term index))
      (-> st
          (log-line :info (str (:id st) " [logterm: " (last-term st) ", index: "
                               (last-index st) ", vote: " (:vote st) "] cast "
                               (name type) " for " from " [logterm: " log-term
                               ", index: " index "] at term " (:term st)))
          ;; The response carries the term FROM THE MESSAGE, not ours: a PreVote
          ;; does not move our term, and answering with our (lower) term would
          ;; make the pre-candidate discard the grant as out of date.
          (send-msg from {:type (vote-resp-type type) :term term})
          (cond-> (= type :vote) (assoc :vote from))
          (cond-> (= type :vote) arm-election-timer))
      (-> st
          (log-line :info (str (:id st) " [logterm: " (last-term st) ", index: "
                               (last-index st) ", vote: " (:vote st) "] rejected "
                               (name type) " from " from " [logterm: " log-term
                               ", index: " index "] at term " (:term st)))
          (send-msg from {:type (vote-resp-type type) :term (:term st) :reject? true})))))

(defn- step-leader [st from msg]
  (case (:type msg)
    :app-resp (handle-app-resp st from msg)
    :heartbeat-resp (handle-heartbeat-resp st from)
    st))

(defn- step-candidate [st from msg]
  (let [my-resp (if (= :pre-candidate (:role st)) :pre-vote-resp :vote-resp)]
    (cond
      (= (:type msg) :app)
      (-> st (become-follower (:term msg) from) (handle-append-entries from msg))

      (= (:type msg) :heartbeat)
      (-> st (become-follower (:term msg) from) (handle-heartbeat from msg))

      (= (:type msg) my-resp)
      (let [[st res] (poll st from (not (:reject? msg)) (name my-resp))]
        (case res
          :won (win-election st)
          :lost (become-follower st (:term st) nil)
          st))

      :else st)))

(defn- step-follower [st from msg]
  (case (:type msg)
    :app (-> st
             arm-election-timer
             (assoc :lead from)
             (handle-append-entries from msg))
    :heartbeat (-> st
                   arm-election-timer
                   (assoc :lead from)
                   (handle-heartbeat from msg))
    st))

(defn- step-by-role [st from msg]
  (case (:role st)
    :leader (step-leader st from msg)
    (:candidate :pre-candidate) (step-candidate st from msg)
    :follower (step-follower st from msg)))

(defn- step-message
  "`raft.go:1089-1271`: term handling first, then role dispatch.

  Messages from an older term are filtered out before this is reached."
  [st from msg]
  (let [mt (:term msg)
        st (if (> mt (:term st))
             ;; PreVote and a *granted* PreVoteResp are the two exceptions that
             ;; must NOT move our term. A pre-vote binds nothing, so answering
             ;; one at our own term is what stops a rejoining partitioned node
             ;; from dragging the whole cluster's term up behind it.
             (cond
               (= (:type msg) :pre-vote) st
               (and (= (:type msg) :pre-vote-resp) (not (:reject? msg))) st
               :else
               (let [st (log-line st :info
                                  (str (:id st) " [term: " (:term st) "] received a "
                                       (name (:type msg)) " message with higher term from "
                                       from " [term: " mt "]"))]
                 (if (#{:app :heartbeat} (:type msg))
                   (become-follower st mt from)
                   (become-follower st mt nil))))
             st)]
    (case (:type msg)
      (:vote :pre-vote) (handle-vote-request st from msg)
      (step-by-role st from msg))))

;; ============================================================
;; Durability barrier
;; ============================================================

(defn- consume-self-ack
  "The leader's own entries became durable. `raft.go:838-846`."
  [st through]
  (if (and (= :leader (:role st)) (:self-ack st) (>= through (:self-ack st)))
    (-> st
        (assoc :self-ack nil)
        (handle-app-resp (:id st) {:index through}))
    st))

(defn- consume-self-vote
  "Our own vote became durable, so it may now be counted. `raft.go:1052-1060`."
  [st]
  (let [sv (:self-vote st)]
    (if (and sv
             (#{:candidate :pre-candidate} (:role st))
             (= (:kind sv) (if (= :pre-candidate (:role st)) :pre-vote :vote)))
      (let [st (assoc st :self-vote nil)
            [st res] (poll st (:id st) true (name (vote-resp-type (:kind sv))))]
        (case res
          :won (win-election st)
          :lost (become-follower st (:term st) nil)
          st))
      st)))

(defn- handle-persisted
  "A `persist-then` landed.

  Two things happen here, and the ABA guard governs both: a completion whose
  epoch no longer matches our term is dropped, because the entries it covered
  may since have been overwritten by a newer leader's append that is still in
  flight (`rawnode.go:266-363`)."
  [st epoch]
  (let [q (:pending-writes st)]
    (if (empty? q)
      st
      (let [w (first q)
            st (assoc st :pending-writes (vec (rest q)))]
        (if (not= epoch (:term st))
          (log-line st :debug
                    (str (:id st) " dropping stale persist completion from epoch "
                         epoch " at term " (:term st)))
          (-> st
              (update :stable max (:last-index w))
              (consume-self-ack (:last-index w))
              consume-self-vote))))))

(defn- finish
  "Turn the accumulated :fx into the effect vector, wrapping the gated messages
  in the durability barrier."
  [st]
  (let [{:keys [msgs after logs commits truncate-from appended? hs0]} (:fx st)
        hs {:term (:term st) :vote (:vote st) :commit (:commit st)}
        hs-changed? (not= hs hs0)
        li (last-index st)
        new-ents (if (< (:issued st) li) (vec (subvec (:log st) (:issued st))) [])
        arm-self? (or (:self-ack st) (:self-vote st))
        need? (or appended? hs-changed? (seq after) truncate-from arm-self?)
        ;; MustSync (rawnode.go:191-198): entries, vote, or term. A commit-index
        ;; change alone is recoverable by replaying the log, so it is buffered.
        sync? (boolean (or (seq new-ents) truncate-from
                           (not= (:term hs) (:term hs0))
                           (not= (:vote hs) (:vote hs0))))
        st (-> st
               (assoc :issued (max (:issued st) li))
               (dissoc :fx))
        st (if need?
             (update st :pending-writes (fnil conj []) {:epoch (:term st) :last-index li})
             st)
        effects (vec (concat logs
                             msgs
                             commits
                             (when need?
                               [(node/persist-then
                                 (cond-> {:writes (cond-> {:hard-state hs}
                                                    (seq new-ents) (assoc :entries new-ents))
                                          :durable? sync?
                                          :epoch (:term st)
                                          :then after}
                                   truncate-from (assoc :truncate-from truncate-from)))])
                             ;; Nothing to persist, so nothing to gate on: the
                             ;; barrier would be a no-op round trip.
                             (when-not need? after)))]
    (node/result st effects)))

;; ============================================================
;; Restart: replaying the durable write log
;; ============================================================

(defn- replay
  "Rebuild state by replaying the ordered log of writes that actually completed,
  starting from whatever was already on disk when the node first came up.

  This is WAL replay, and it is the whole point of the durability barrier: a
  node that kept its term in memory but not on disk loses it here, exactly as it
  would in production.

  Order matters and a merge cannot express it: one write appends indexes 4-8,
  a later one truncates from 4 and appends a different 4-6. Union the two
  `:entries` values and you get nonsense; fold them in order and you get the
  log."
  [base writes]
  (reduce (fn [acc {:keys [writes truncate-from]}]
            (let [acc (if truncate-from
                        (update acc :log #(vec (take (dec truncate-from) %)))
                        acc)
                  acc (if-let [hs (:hard-state writes)]
                        (assoc acc :hard-state hs)
                        acc)]
              (if-let [es (:entries writes)]
                (update acc :log
                        (fn [l]
                          ;; Entries carry their own index, so an append that
                          ;; starts below the end is itself a truncation.
                          (let [from (:index (first es))]
                            (into (vec (take (dec from) l)) es))))
                acc)))
          base
          writes))

;; ============================================================
;; The Node implementation
;; ============================================================

(def default-config
  {:election-timeout 10
   :heartbeat-timeout 1
   :pre-vote? true
   :propose-interval nil})

(defrecord Raft []
  node/Node

  (init [_ config]
    (let [cfg (merge default-config config)
          restored (:restored config)
          ;; `:initial-log` is what was on disk before this process ever ran --
          ;; the equivalent of etcd's bootstrap snapshot. Replay starts there,
          ;; not from an empty log, or a restart would forget everything the
          ;; node was created with.
          {:keys [log hard-state]}
          (replay {:log (vec (:initial-log cfg))
                   :hard-state {:term (or (:initial-term cfg) 0)
                                :vote nil
                                :commit (or (:initial-commit cfg) 0)}}
                  (:writes restored))
          li (count log)
          commit (min (or (:commit hard-state) 0) li)
          st {:id (:peer-id cfg)
              :validators (vec (sort (:validators cfg)))
              :role :follower
              :term (or (:term hard-state) 0)
              :vote (:vote hard-state)
              :lead nil
              :log (vec log)
              :commit commit
              ;; `applied` starts at `commit`: entries that were already
              ;; committed before the crash were already handed to the
              ;; application, and re-emitting them would double-apply.
              :applied commit
              :stable li
              :issued li
              :pending-writes []
              :self-ack nil
              :self-vote nil
              :votes {}
              :progress {}
              :election-timeout (:election-timeout cfg)
              :heartbeat-timeout (:heartbeat-timeout cfg)
              :propose-interval (:propose-interval cfg)
              :pre-vote? (:pre-vote? cfg)}
          st (fresh-fx st)
          st (-> st
                 (reset-state (:term st))
                 (assoc :role :follower)
                 (log-line :info (str "raft " (:peer-id cfg) " [peers: " (:validators st)
                                      ", term: " (:term st) ", commit: " commit
                                      ", lastindex: " li ", lastterm: "
                                      (or (term-at st li) 0) "]"))
                 arm-election-timer)]
      ;; Nothing has changed relative to what is on disk, so `finish` must not
      ;; manufacture a write here.
      (finish (assoc-in st [:fx :hs0] {:term (:term st) :vote (:vote st) :commit (:commit st)}))))

  (step [_ state input]
    (let [st (fresh-fx state)]
      (case (:type input)
        :message-received
        (let [from (:from input)
              msg (:msg input)]
          (finish
           (cond
             ;; A message from an older term. Answering an old leader's append
             ;; with a bare app-resp at our term is how it learns it is stale;
             ;; with PreVote enabled nothing else will tell it.
             (< (:term msg) (:term st))
             (cond
               (#{:app :heartbeat} (:type msg))
               (send-msg st from {:type :app-resp :term (:term st)
                                  :index (:commit st)})

               (= :pre-vote (:type msg))
               (-> st
                   (log-line :info (str (:id st) " rejected pre-vote from " from
                                        " at term " (:term st)))
                   (send-msg from {:type :pre-vote-resp :term (:term st) :reject? true}))

               :else
               (log-line st :info (str (:id st) " [term: " (:term st) "] ignored a "
                                       (name (:type msg)) " message with lower term from "
                                       from " [term: " (:term msg) "]")))

             :else
             (step-message st from msg))))

        :timer-fired
        (finish
         (case (:timer-id input)
           :election (if (= :leader (:role st)) st (hup st))
           :heartbeat (if (= :leader (:role st))
                        (-> st bcast-heartbeat arm-heartbeat-timer)
                        st)
           :propose (if (= :leader (:role st))
                      (-> st (emit (node/request-value {:term (:term st)}))
                          arm-propose-timer)
                      st)
           st))

        :persisted
        (finish (handle-persisted st (:epoch input)))

        ;; A proposal. Only a leader may append; a follower would have to
        ;; forward it, and urd has no effect for handing a value to a peer as
        ;; anything other than a consensus message, so we drop it.
        :value-ready
        (finish
         (let [v (:value input)]
           (if (and (= :leader (:role st))
                    (some? v)
                    (not= v {:payload :none}))
             (-> st (append-entries [v]) bcast-append)
             st)))

        ;; Ticks are not used: all timing goes through logical timers.
        (finish st)))))

(defn make
  "A Raft node. Per-node configuration is supplied through the simulator's
  `:node-config`, or merged into `init`'s config by a runtime."
  []
  (->Raft))
