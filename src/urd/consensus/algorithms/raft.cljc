(ns urd.consensus.algorithms.raft
  "Raft as a pure state machine on `urd.consensus.node`.

  Ported from `etcd-io/raft` (read at Aug 2026). Scope: leader election with
  PreVote, log replication with per-peer progress, durable hard state and log
  entries, log truncation on a conflicting suffix, and membership changes
  including joint consensus. Out of scope: snapshots, leadership transfer,
  read-index/lease reads, CheckQuorum, and inflight-based flow control.

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

  Completions are correlated by a CALLER-SUPPLIED token: we mint one per write,
  key `:pending-writes` by it, and match on the way back.

  This was originally a FIFO queue, popped from the front, on the assumption
  that interpreters complete writes in issue order. urd's own simulator does
  not: a non-durable write completes at the current tick while a durable one
  completes `persist-latency` ticks later (`sim.cljc:178`), so a LATER buffered
  write routinely lands before an EARLIER fsync. And because an outstanding
  self-ack forces a write on every subsequent step, that reordering was the
  default path rather than a rare race -- the leader counted its own entry as
  durable while the entry was still in flight, which is the exact loss this
  barrier exists to prevent.

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
            [urd.consensus.reconfig :as reconfig]
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
  "A timeout in [et, 2*et), deterministic in (peer-id, term, draw).

  etcd-raft draws this from `globalRand` (`raft.go`,
  `resetRandomizedElectionTimeout`) on every `reset`. We cannot: a state machine
  may not draw a random number, and urd's `:sample` effect returns random PEERS,
  not a random number. Deriving it instead keeps runs replayable and still
  breaks split votes, because two nodes campaigning at once get different
  offsets.

  `draw` is a per-node counter of how many times the election timer has been
  armed, and WITHOUT IT this function is a livelock. PreVote deliberately does
  not bump the term -- that is its whole point (`become-pre-candidate`) -- so a
  key of (id, term) alone is CONSTANT across repeated pre-vote rounds. Two nodes
  that split a pre-vote would re-campaign after exactly the same interval,
  split again, and do so forever, deterministically, with no term ever
  advancing to break the tie. etcd redraws on every reset and so has no such
  case; the term-keyed version resolved repeated splits only in the one
  configuration where the term moves.

  Seeded through `rng/from-key`, not `rng/make`. xorshift32 is GF(2)-linear, so
  one round does not decorrelate structured seeds: with plain `make`, five peers
  won 296/367/477/400/460 elections over 2000 terms against an expectation of
  400, about 5.8 sigma at the low end. Safety never depended on a fair lottery,
  but a skewed one makes the simulator explore a skewed space -- and the same
  composition made SCP's leader election degenerate completely."
  ([id term et] (randomized-election-timeout id term 0 et))
  ([id term draw et]
   (let [[w _] (rng/next-word (rng/from-key (string-hash (str id "@" term "#" draw))))]
     (+ et (mod w (max 1 et))))))

;; ============================================================
;; The log
;;
;; Entries are {:index i :term t :data d}, and indices are ABSOLUTE: `i` does
;; not move when the log is compacted. `:log-base` is the index BEFORE the
;; first entry we still hold, so entry `i` sits at vector position
;; `(- i :log-base 1)`. An uncompacted log has `:log-base` 0, which is the old
;; behaviour exactly.
;;
;; `:base-term` is the term of the entry AT `:log-base` -- the one we dropped.
;; Keeping it is not bookkeeping: `prevLogTerm` matching has to work across the
;; compaction boundary, so a follower asked to append at the boundary can still
;; answer. etcd keeps the same value for the same reason and calls it the dummy
;; `ents[0]`; its `Storage.Term(i)` is documented as valid on
;; `[FirstIndex()-1, LastIndex()]`, and `FirstIndex()-1` is exactly this.
;; ============================================================

(defn- log-pos
  "The vector position of absolute index `i`, which may be outside the vector.

  One function so the offset cannot be applied in some places and forgotten in
  others -- which is the entire risk of introducing it."
  [st i]
  (- i (:log-base st 0) 1))

(defn last-index [st] (+ (:log-base st 0) (count (:log st))))

(defn entry-at
  "The entry at `i`, or nil if out of range or compacted away."
  [st i]
  (let [p (log-pos st i)]
    (when (and (>= p 0) (< p (count (:log st))))
      (nth (:log st) p))))

(defn term-at
  "The term at index `i`, or nil if unknown.

  Index 0 is the sentinel before an uncompacted log with term 0, which is what
  makes an append anchored at (index 0, term 0) match an empty log. After
  compaction `:log-base` plays the same role and `:base-term` is its term, so
  an append anchored at the boundary still matches."
  [st i]
  (let [base (:log-base st 0)]
    (cond
      (zero? i) (if (zero? base) 0 nil)
      (= i base) (:base-term st 0)
      (< i base) nil                       ; compacted away; we cannot say
      :else (let [p (log-pos st i)]
              (when (< p (count (:log st)))
                (:term (nth (:log st) p)))))))

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

(def default-log-retention
  "How many applied entries to keep after compacting.

  etcd's `SnapshotCatchUpEntries` (5000 against a `SnapshotCount` of 10000),
  and its reason is worth restating because it is not obvious: compacting all
  the way to `applied` means any follower even ONE entry behind can no longer
  be served from the log and needs a snapshot instead -- and since sending one
  is slow, the leader compacts again while it is in flight. The cycle sustains
  itself. Retaining a tail is what breaks it."
  1000)

(defn compact
  "Drop applied entries below the retention window, keeping indices ABSOLUTE.

  Safe only up to `:applied`: an entry that has not been handed to the
  application cannot be reconstructed from anywhere, and an entry above the
  commit index may still be truncated by a future leader. So the window is
  measured back from `applied`, never from `last-index`.

  `:base-term` keeps the term of the entry at the new base, because
  `prevLogTerm` matching must still work across the boundary -- a follower
  asked to append there has to be able to answer. Compaction without it turns
  the boundary into a permanent mismatch.

  Returns the state unchanged when there is nothing worth dropping, so callers
  need not check."
  ([st] (compact st (or (:log-retention st default-log-retention)
                        default-log-retention)))
  ([st retain]
   (let [base (:log-base st 0)
         target (- (:applied st 0) retain)]
     (if (<= target base)
       st
       (let [term (term-at st target)]
         (-> st
             (update :log #(vec (drop (log-pos st (inc target)) %)))
             (assoc :log-base target
                    :base-term (or term (:base-term st 0)))))))))

(defn- checkpoint-due?
  "Has enough log accumulated above the boundary to be worth rewriting it?

  At `2 x retention`, so that each checkpoint drops one retention's worth. The
  threshold is amortisation, not taste: `compact` moves the boundary to
  `applied - retention`, so triggering at `retention` would rewrite the whole
  log to drop nothing, every time an entry applied. That is the self-reinforcing
  cycle etcd's `SnapshotCatchUpEntries` exists to break, arrived at from the
  other end -- there the cost is a snapshot sent to a follower, here it is a log
  rewritten on disk, and in both cases the fix is to let a gap build first.

  Measured against `:applied` and not `:commit`, because `compact` may only
  discard what has been handed to the application; see its docstring.

  `nil` retention means NEVER compact -- an archive node, which is how a
  cluster keeps anyone able to serve history that everybody else has thrown
  away. `(:log-retention st default)` returns nil rather than the default when
  the key is present and nil, so this used to reach `(* 2 nil)` and throw the
  first time `:applied` advanced. Configuring an archive node crashed it, and
  only once it had made progress. Tendermint's `:wal-retention` already read
  nil this way; this is the same contract."
  [st]
  (let [retain (:log-retention st default-log-retention)]
    (and (number? retain)
         (>= (- (:applied st 0) (:log-base st 0)) (* 2 retain)))))

(defn checkpoint-records
  "The durable log, rewritten as the shortest sequence that replays to `st`.

  `compact` bounds MEMORY; this is what bounds the durable log, and without it
  a node whose in-memory log is twenty entries still replays twenty thousand on
  restart -- the store is the history whatever the state machine has forgotten.

  Two records, and their order is the contract `replay` reads:

  1. the compacted boundary and the entries still held, written as one record
     so a `:log-base` can never arrive without the entries it rebases;
  2. the hard state, which is a merge and can follow.

  `store/checkpoint!` takes records precisely so this can live here, in the
  namespace that knows what a Raft write means, rather than in a store that
  would have to guess."
  [st]
  [{:writes {:log-base (:log-base st 0)
             :base-term (:base-term st 0)
             :entries (vec (:log st))}
    :durable? true}
   {:writes {:hard-state {:term (:term st) :vote (:vote st) :commit (:commit st)}}
    :durable? true}])

(defn- truncate-log
  "Drop every entry at or above `from`."
  [st from]
  (update st :log #(vec (take (max 0 (log-pos st from)) %))))

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

(defn- arm-election-timer
  "Arm the election timer, REDRAWING the offset each time.

  This is `resetRandomizedElectionTimeout`, and the redraw is the load-bearing
  part -- see `randomized-election-timeout`."
  [st]
  (let [st (update st :election-draw (fnil inc 0))]
    (emit st (node/set-timer :election
                             (randomized-election-timeout (:id st) (:term st)
                                                          (:election-draw st)
                                                          (:election-timeout st))))))

(defn- arm-heartbeat-timer [st]
  (emit st (node/set-timer :heartbeat (:heartbeat-timeout st))))

(defn- arm-propose-timer [st]
  (if-let [n (:propose-interval st)]
    (emit st (node/set-timer :propose n))
    st))

;; ============================================================
;; Commit
;; ============================================================

(defn config-entry?
  "Does this entry carry a validator set change?"
  [e]
  (boolean (seq (:validator-updates (:data e)))))

(defn- config-of
  "This node's set as a `reconfig` config.

  Powers are synthesised as 1 apiece, because Raft is UNWEIGHTED by
  construction -- `committed-index` and `vote-result` count validators, not
  power, and `node/validator-set` is a plain list. `reconfig` needs a power map
  because Tendermint is weighted, so this is the impedance match between the
  two, in the one place that knows Raft's answer.

  Passing `nil` here instead was a real bug and an instructive one: every
  update then collapsed to `:would-empty-the-validator-set`, because
  `(select-keys nil ...)` is `{}` and removing from nothing leaves nothing. The
  set change was refused, correctly per the data it was given, and the failure
  looked like a validation bug rather than a missing argument."
  [st]
  {:validators (:validators st)
   :powers (zipmap (:validators st) (repeat 1))})

(defn- activate-config
  "Apply the set change in `e`, if it has one and it is valid.

  ONE-AT-A-TIME is what makes this safe, and it is enforced at the point of
  APPEND (see `append-entry`) rather than here: a configuration differing by a
  single voter always has majorities that intersect the old one's, which is the
  Raft thesis's original argument (S4.1) and the reason etcd's `Changer.Simple`
  refuses a change of more than one voter.

  Activated at COMMIT. The thesis activates at ADD, etcd at APPLY, and all
  three are safe given one-at-a-time -- etcd says so directly: `equivalent in
  terms of safety, since the old and new configurations are guaranteed to
  overlap`. Commit is chosen here because `commit-to` is the single chokepoint
  through which both the leader and every follower advance, so every node
  activates at the same LOG POSITION even though they reach it at different
  moments. That is the property that matters; wall-clock agreement is neither
  available nor needed.

  It also avoids the hazard etcd carries: their active config is their APPLIED
  config, and applied trails committed by an unbounded, application-controlled
  amount, which is why their one-in-flight rule has to be measured against
  `applied` and why a fixed offset would be unsound for them. urd's state
  machine has no such lag -- `step` is pure and the state IS the applied state.

  An invalid update leaves the set alone. Deterministic, since validity is a
  function of the config and the updates only, so every node makes the same
  choice and the cluster stalls on the entry rather than splitting over it."
  [st e]
  (cond
    ;; LEAVING. The second of the two decisions, and it carries no updates --
    ;; the new set is already installed, this only drops the old half.
    (:leave-joint (:data e))
    (-> st
        (assoc :outgoing [])
        (update-in [:fx :logs] conj
                   (node/log-effect :info {:event :left-joint-config
                                           :at (:index e)
                                           :validators (:validators st)})))

    (not (config-entry? e)) st

    :else
    (let [result (reconfig/apply-updates (config-of st)
                                         (:validator-updates (:data e)))]
      (if (:error result)
        (update-in st [:fx :logs] conj
                   (node/log-effect
                    :error {:event :refused-validator-updates
                            :entry (:index e) :reason result}))
        (let [vs (:validators result)
              li (last-index st)
              ;; ENTERING JOINT, when this is not a single-voter change.
              ;;
              ;; `:outgoing` becomes the set we are leaving, and from here
              ;; every quorum needs a majority of BOTH halves. That is what
              ;; replaces the intersection argument a single-voter change gets
              ;; for free: an arbitrary change can move the majority anywhere,
              ;; so the two configurations are made to overlap by requiring
              ;; both rather than by limiting the change.
              ;;
              ;; The joint state is itself just a configuration -- one value in
              ;; the same lattice -- which is why entering needs no special
              ;; decision type. Leaving is a second decision, and where decide
              ;; == apply (urd's case; `step` is pure and its state IS the
              ;; applied state) the two are consecutive at a fixed offset. etcd
              ;; cannot do that: their active config is their APPLIED config
              ;; and applied trails commit unboundedly, so their leave has to
              ;; be gated on a local predicate instead.
              joint? (not (reconfig/single-voter-change?
                           (config-of st) (:validator-updates (:data e))))]
          (-> st
              ;; `:validators` only. Raft never reads a power, so storing one
              ;; would be state nothing consults -- and state nothing consults
              ;; is state that silently goes stale.
              (assoc :validators vs)
              (cond-> joint? (assoc :outgoing (:validators st)))
              ;; Progress for anyone new, and no Progress for anyone gone.
              ;; A stale entry for a removed peer would keep contributing its
              ;; `:match` to `committed-index`, so the commit index could be
              ;; advanced by a node that is no longer a validator.
              ;; Progress for the UNION while joint. An outgoing-only peer
              ;; still votes and still acks, and dropping it would make its
              ;; half of the quorum unreachable -- the leader would wait for
              ;; acks it can no longer receive.
              (as-> st'
                    (assoc st' :progress
                           (into {} (map (fn [p]
                                           [p (or (get-in st [:progress p])
                                                  (new-progress (inc li)))]))
                                 (distinct (concat vs (:outgoing st' []))))))
              (update-in [:fx :logs] conj
                         (node/log-effect
                          :info {:event :validator-set-changed
                                 :at (:index e) :validators vs}))))))))

(defn- commit-to
  "Advance the commit index, never backwards. `log.go:322-331` panics if asked to
  commit past the end of the log; so do we, because that means the log was
  truncated or lost.

  Newly committed entries carrying a set change activate here, in index order.
  See `activate-config`."
  [st to]
  (if (<= to (:commit st))
    st
    (do
      (when (< (last-index st) to)
        (throw (ex-info "commit index past the end of the log"
                        {:to to :last-index (last-index st) :id (:id st)})))
      (let [newly (keep #(entry-at st %) (range (inc (:commit st)) (inc to)))]
        (reduce activate-config (assoc st :commit to) newly)))))

(defn- flush-commits
  "Hand newly committed entries to the application, in order -- but only those
  that are also LOCALLY DURABLE.

  Raft never reverts a *committed* entry: a conflicting suffix is by
  construction above the commit index, so this algorithm emits `:commit` and
  never `:revert`. That is precisely why the durability gate matters. Once an
  entry is handed to the application there is no mechanism to take it back, so
  handing over an entry that is committed cluster-wide but not yet on OUR disk
  means a crash loses it with no way to signal the loss.

  etcd applies `min(committed, unstable.offset-1)` under async storage writes
  (`log.go:266-271`, via `applyUnstableEntries()` returning false at
  `rawnode.go:443`) -- i.e. only entries already on stable storage. `:stable` is
  urd's `unstable.offset-1`; it was maintained in three places and read in none,
  so the gate was computed and never installed. This is that gate."
  [st]
  (let [applied (:applied st)
        ;; The commit index says the cluster agreed; :stable says our own write
        ;; landed. Applying needs both.
        deliverable (min (:commit st) (:stable st 0))]
    (if (<= deliverable applied)
      st
      (let [ents (subvec (:log st) (log-pos st (inc applied)) (log-pos st (inc deliverable)))]
        (-> st
            (assoc :applied deliverable)
            (update-in [:fx :commits] conj (node/commit ents))
            ;; The only place `:applied` moves, so the only place the boundary
            ;; can become worth moving. `finish` does the rewrite -- this just
            ;; records that one is owed, because compacting here would pull the
            ;; log out from under the `new-ents` arithmetic in the same step.
            (as-> st' (cond-> st' (checkpoint-due? st')
                              (assoc :checkpoint-due? true))))))))

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
          (let [ents (vec (subvec (:log st) (log-pos st (inc prev-index))))]
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
        ;; `:through` is the index these entries reach; `:token` is stamped in
        ;; `finish` with the write that carries them. It used to be a bare
        ;; index, which is what let any later completion satisfy it.
        (assoc :self-ack {:through (+ li (count ents)) :token nil}))))

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
        ;; Through the JOINT helper always. A non-joint configuration is the
        ;; degenerate case with an empty outgoing half, and both helpers treat
        ;; an empty half neutrally by construction -- `vote-result` returns
        ;; `:won` and `committed-index` returns `max-index` for it. etcd relies
        ;; on exactly this ("This plays well with joint quorums"), and it means
        ;; there is ONE code path rather than a branch that could disagree with
        ;; itself.
        res (joint-vote-result (:validators st) (:outgoing st []) (:votes st))]
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

(defn- handle-heartbeat
  ;; A heartbeat claiming we hold more than we do is NOT acted on.
  ;;
  ;; `send-heartbeat` clamps to `(min (:match pr) (:commit st))`, so a current
  ;; leader can never ask us to commit past our own last index -- `match` is
  ;; only advanced by a successful `:app-resp`, which rides behind our
  ;; durability barrier. So this condition means the message is not current:
  ;; the simulator's duplication and delay let a heartbeat from BEFORE a crash
  ;; arrive after the restart, carrying a commit index that was correct for the
  ;; log we no longer have.
  ;;
  ;; etcd panics here (`log.go:322-331`, which `commit-to` mirrors) because it
  ;; assumes the transport cannot replay a message across a restart -- a TCP
  ;; connection dies with the process. That assumption is not in the algorithm,
  ;; and it is not true of every transport.
  ;;
  ;; CLAMPING to `(min commit (last-index st))` would be the tempting fix and
  ;; is wrong: a heartbeat carries no `prev-index` consistency check, so the
  ;; entries at those indices have not been shown to match the leader's. We
  ;; would be committing entries on no evidence. Dropping the commit costs
  ;; nothing -- we still answer, and the leader corrects its `match` from the
  ;; next `:app-resp` rejection, which does carry the check.
  [st from {:keys [commit]}]
  (-> (if (<= commit (last-index st))
        (-> st (commit-to commit) flush-commits)
        (log-line st :debug
                  (str "ignoring heartbeat commit " commit " from " from
                       " -- past our last index " (last-index st)
                       "; stale, or our log was truncated by a restart")))
      (send-msg from {:type :heartbeat-resp :term (:term st)})))

;; ============================================================
;; Leader: commit advancement
;; ============================================================

(defn- maybe-leave-joint
  "Once the joint configuration is COMMITTED, the leader proposes leaving it.

  A genuine second log entry, not a derived event -- etcd does the same
  (`raft.go:748` constructs and steps a real `EntryConfChangeV2`). Every replica
  must reach the same configuration deterministically, and the only thing they
  all agree on is the log; a leave that each node inferred locally would be a
  decision made outside the log, which is what the log exists to prevent.

  Gated on the joint entry being COMMITTED rather than merely appended. Leaving
  earlier would install the new set on the strength of the old quorum alone,
  which is precisely the disjoint-quorum case the joint state exists to
  prevent.

  Leader only, and idempotent: a leave already in the log stops another being
  appended. etcd had a bug here -- commit `bd3c759`, whose message calls the
  code undertested and buggy -- where the leave was proposed repeatedly when
  the conf change was not the last entry in the log, and it panicked."
  [st]
  (if-not (and (= :leader (:role st))
               (seq (:outgoing st))
               (not (some #(:leave-joint (:data (entry-at st %)))
                          (range (inc (:commit st)) (inc (last-index st))))))
    st
    (-> st
        (append-entries [{:leave-joint true}])
        (update-in [:fx :logs] conj
                   (node/log-effect :info {:event :proposing-leave-joint
                                           :validators (:validators st)})))))

(defn- maybe-commit
  "`raft.go:775-779`. Returns [st advanced?].

  Raft 5.4.2 is the subtle part: the leader may only advance the commit index to
  an entry from its OWN term. Counting replicas of an entry from an earlier term
  is exactly the Figure-8 bug."
  [st]
  (let [acked (into {} (map (fn [[p pr]] [p (:match pr)])) (:progress st))
        mci (joint-committed-index (:validators st) (:outgoing st []) acked)]
    (if (and (> mci (:commit st))
             (= (:term st) (term-at st mci)))
      ;; The commit may have ratified a joint configuration, in which case the
      ;; leader now owes the log a leave entry. Placed here rather than in
      ;; `commit-to` because `commit-to` runs on followers too, and only a
      ;; leader may append.
      [(maybe-leave-joint (flush-commits (commit-to st mci))) true]
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

;; A commitment is released by the completion of THE WRITE THAT CARRIED IT, and
;; only if that write was fsynced. Both halves are the fix; see the friction
;; note below.
;;
;; The port adopted etcd's durability WATERMARK -- release everything up to the
;; last completed index -- without its FIFO precondition. etcd may do that
;; because `doc.go:190-195` promises messages to one target are processed in
;; order and `msgsAfterAppend` are attached as Responses to that specific
;; `MsgStorageAppend` (`rawnode.go:254-258`); our protocol explicitly declines
;; to promise ordering (`node.cljc:218-223`), and our own simulator does not
;; provide it -- a buffered write completes at the current tick while a durable
;; one waits for `persist-latency`.
;;
;; With a watermark and no ordering, a step that changes nothing durable still
;; mints a write, that write carries no entries, and its completion released
;; every gated commitment anyway. Measured: a follower published `MsgAppResp`
;; for entries 1..3 off a later `durable? false` write with `entries nil`, so
;; the leader counted a replica that had nothing on disk. A carrier token
;; cannot do that, because the token names the write that actually carried the
;; state.

(defn- consume-self-ack
  "The leader's own entries became durable. `raft.go:836-845`.

  Fires only for the write that CARRIED the entries, identified by token. The
  previous rule -- any completion whose last index reached the armed one --
  fired on the very next buffered write, because `arm-self?` makes `need?` true
  on every subsequent step and every such write records the current log length
  as its `:last-index` while carrying no entries at all.

  The token alone is the condition; fsync is NOT an additional one. An append
  that carries entries is durable by `MustSync` anyway, and requiring it
  explicitly would break the pre-vote path, where the carrier is correctly
  buffered because a pre-vote changes neither term nor vote and grants nothing
  that must survive a crash."
  [st token]
  (let [sa (:self-ack st)]
    (if (and (= :leader (:role st)) sa (= token (:token sa)))
      (-> st
          (assoc :self-ack nil)
          (handle-app-resp (:id st) {:index (:through sa)}))
      st)))

(defn- consume-self-vote
  "Our own vote became durable, so it may now be counted. `raft.go:1051-1059`.

  Fires only for the write that carried the vote, and only if that write was
  fsynced. This docstring previously claimed it took the completed write's last
  index `so it can only fire for a write issued at or after the vote` -- the
  parameter was `_`-prefixed and never read, so the guard did not exist, and
  the finding it records as closed was not closed.

  An index would not have been sufficient anyway. Measured: a candidate
  campaigns at term 1, minting a durable write W0 carrying `term=1 vote=:a`;
  before it lands, a competing vote request arrives and is rejected, which
  gates a response and therefore mints a buffered W1 carrying no entries. W0
  and W1 have the SAME last index, so any index test passes, and the candidate
  counted its own vote off a write that never reached disk. Lose power there
  and it restarts at term 0 with no vote, grants term 1 to someone else, and
  there are two leaders at term 1."
  [st token]
  (let [sv (:self-vote st)]
    (if (and sv
             (= token (:token sv))
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
  flight (`rawnode.go:266-363`).

  Correlated by TOKEN, not by queue position. Popping the front assumed the
  interpreter completes writes in issue order, and urd's own simulator does not:
  a non-durable write completes at the current tick while a durable one completes
  `persist-latency` ticks later (`sim.cljc:178`), so a LATER buffered write
  routinely lands before an EARLIER fsync. Because an outstanding self-ack forces
  a write on every subsequent step, that reordering was the default path, not a
  rare race -- and it made the leader count its own entry as durable while the
  entry was still in flight, which is exactly the loss this barrier exists to
  prevent."
  [st token epoch]
  (let [w (get (:pending-writes st) token)]
    (if (nil? w)
      ;; Unknown or duplicate completion: nothing to attribute it to.
      st
      (let [st (update st :pending-writes dissoc token)]
        ;; Compare the write's OWN epoch against the CURRENT term. Comparing it
        ;; against the echoed `epoch` would be a tautology -- the interpreter
        ;; echoes back exactly what we sent -- and would disable the guard
        ;; entirely. The hazard is that the term MOVED while the write was in
        ;; flight, so the term at issue time is what has to be checked.
        (if (not= (:epoch w) (:term st))
          (log-line st :debug
                    (str (:id st) " dropping stale persist completion from epoch "
                         epoch " at term " (:term st)))
          (-> st
              ;; `:stable` means "entries up to here are on OUR disk", so only
              ;; an fsynced write may advance it. A buffered write carries no
              ;; entries to the platter, and advancing on one made
              ;; `flush-commits`' gate a leak rather than a delay -- it handed
              ;; the application entries this node had not durably stored.
              (cond-> (:durable? w) (update :stable max (:last-index w)))
              (consume-self-ack token)
              (consume-self-vote token)
              ;; Durability just advanced, so entries that were committed but
              ;; not yet on our own disk may now be deliverable. Without this
              ;; the gate in `flush-commits` would be a leak rather than a
              ;; delay: an entry committed before its write landed would never
              ;; be handed to the application at all, because nothing else
              ;; re-checks once the commit index has stopped moving.
              flush-commits))))))

(defn- finish
  "Turn the accumulated :fx into the effect vector, wrapping the gated messages
  in the durability barrier."
  [st]
  (let [{:keys [msgs after logs commits truncate-from appended? hs0]} (:fx st)
        hs {:term (:term st) :vote (:vote st) :commit (:commit st)}
        hs-changed? (not= hs hs0)
        li (last-index st)
        new-ents (if (< (:issued st) li)
                   (vec (subvec (:log st) (log-pos st (inc (:issued st)))))
                   [])
        arm-self? (or (:self-ack st) (:self-vote st))
        cp? (boolean (:checkpoint-due? st))
        need? (or appended? hs-changed? (seq after) truncate-from arm-self? cp?)
        ;; MustSync (rawnode.go:191-198): entries, vote, or term. A commit-index
        ;; change alone is recoverable by replaying the log, so it is buffered.
        sync? (boolean (or (seq new-ents) truncate-from cp?
                           (not= (:term hs) (:term hs0))
                           (not= (:vote hs) (:vote hs0))))
        ;; The checkpoint REPLACES this step's ordinary write rather than
        ;; accompanying it. `checkpoint-records` already carries the retained
        ;; entries and the hard state, so a second write would say the same
        ;; thing twice -- and two writes in one step would need two tokens,
        ;; which is the bookkeeping `:pending-writes` was built to avoid.
        ;;
        ;; Compaction happens HERE, after `new-ents` has been read off the
        ;; uncompacted log: `:issued` can sit below the new boundary, and
        ;; `subvec` from a position that no longer exists is the crash this
        ;; ordering avoids. `truncate-from` is subsumed for the same reason a
        ;; second write is -- rewriting the log wholesale is a superset of
        ;; dropping a tail from it.
        st (cond-> st cp? (-> compact (dissoc :checkpoint-due?)))
        records (when cp? (checkpoint-records st))
        st (-> st
               (assoc :issued (max (:issued st) li))
               (dissoc :fx))
        token (:next-write-token st 0)
        st (if need?
             (-> st
                 (assoc-in [:pending-writes token] {:epoch (:term st)
                                                    :last-index li
                                                    :durable? sync?})
                 ;; Stamp the carrier onto whatever this write is gating. This
                 ;; write is the carrier by construction: `arm-self?` forces
                 ;; `need?`, so a step that arms a commitment always mints the
                 ;; write in the same step, and a vote or term change always
                 ;; makes `sync?` true. An already-stamped arm keeps its
                 ;; original carrier -- a later write must not adopt it.
                 (cond->
                  (and (:self-ack st) (nil? (:token (:self-ack st))))
                   (assoc-in [:self-ack :token] token)
                   (and (:self-vote st) (nil? (:token (:self-vote st))))
                   (assoc-in [:self-vote :token] token))
                 (assoc :next-write-token (inc token)))
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
                                          :token token
                                          :then after}
                                   truncate-from (assoc :truncate-from truncate-from)
                                   cp? (assoc :checkpoint records)))])
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
            (let [;; BASE-AWARE. Positions here are `index - base - 1`, the
                  ;; same arithmetic as `log-pos`, because a checkpoint record
                  ;; can move the base and everything after it is relative to
                  ;; wherever it landed. Computing `(dec index)` instead --
                  ;; which is what this did -- silently renumbers a compacted
                  ;; log back to base 0 on the one path where being wrong is
                  ;; worst.
                  pos (fn [acc i] (- i (:log-base acc 0) 1))
                  ;; A checkpoint record: the compacted state, written whole.
                  acc (if (contains? writes :log-base)
                        (assoc acc :log-base (:log-base writes)
                               :base-term (:base-term writes 0)
                               :log [])
                        acc)
                  acc (if truncate-from
                        (update acc :log #(vec (take (max 0 (pos acc truncate-from)) %)))
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
                            (into (vec (take (max 0 (pos acc from)) l)) es))))
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
   :propose-interval nil
   ;; Configurable, because the right value is a deployment question -- how
   ;; much disk a replay may cost against how far behind a follower may fall
   ;; and still be caught up from the log rather than a snapshot. Threaded into
   ;; state below; `compact` and `checkpoint-due?` both read it from there, and
   ;; while it was absent from `init` they silently read the default and no
   ;; configured value had any effect.
   :log-retention default-log-retention})

(defrecord Raft []
  node/Node

  (capabilities [_]
    ;; Crash-fault tolerant and ABSOLUTELY final: an entry that Raft reports as
    ;; committed is never taken back. No `:revert` here, ever -- the log
    ;; truncation Raft does perform is of UNCOMMITTED entries, through
    ;; `:truncate-from` on a write, and that is a different thing.
    ;; `:resync` is emitted only on restart, and only to announce the durable
    ;; committed prefix. Raft never REVOKES a decision -- a conflicting suffix
    ;; is by construction above the commit index -- so `:revert` is absent and
    ;; must stay absent.
    {:emits #{:send :persist-then :set-timer :cancel-timer :request-value
              :commit :resync :log}})

  (init [_ config]
    (let [cfg (merge default-config config)
          restored (:restored config)
          ;; `:initial-log` is what was on disk before this process ever ran --
          ;; the equivalent of etcd's bootstrap snapshot. Replay starts there,
          ;; not from an empty log, or a restart would forget everything the
          ;; node was created with.
          {:keys [log hard-state log-base base-term]}
          (replay {:log (vec (:initial-log cfg))
                   :log-base 0
                   :base-term 0
                   :hard-state {:term (or (:initial-term cfg) 0)
                                :vote nil
                                :commit (or (:initial-commit cfg) 0)}}
                  (:writes restored))
          ;; From the REPLAY, not fixed at zero. A checkpoint record carries
          ;; the compacted boundary, and hard-coding it here threw that away --
          ;; the node came back holding the retained entries renumbered from 1,
          ;; which is the corruption the absolute-index design exists to avoid,
          ;; introduced on the restore path by the very line meant to make the
          ;; state explicit.
          log-base (or log-base 0)
          base-term (or base-term 0)
          li (+ log-base (count log))
          commit (min (or (:commit hard-state) 0) li)
          ;; How many committed vertices the CONSUMER has already applied.
          ;;
          ;; This is etcd's `Config.Applied`, and the comment further down
          ;; already named it as the better answer: etcd takes it from the
          ;; application and warns that, unset, "raft might return previous
          ;; applied entries" (`raft.go:147-151`).
          ;;
          ;; A COUNT rather than an index, because the consumer counts vertices
          ;; and knows nothing about Raft's numbering. For this algorithm the
          ;; two coincide -- committed vertices are exactly entries 1..commit,
          ;; delivered contiguously and one per entry -- so the count IS the
          ;; applied index. An algorithm whose prefix can be REWRITTEN cannot
          ;; use a count for this, which is why Nakamoto still announces its
          ;; whole prefix instead.
          delivered (:delivered-through cfg)
          applied (if (number? delivered) (min commit (max 0 delivered)) commit)
          st {:id (:peer-id cfg)
              :validators (node/validator-set cfg)
              :role :follower
              :term (or (:term hard-state) 0)
              :vote (:vote hard-state)
              :lead nil
              :log (vec log)
              ;; Explicit, not defaulted. Every accessor tolerates their
              ;; absence, and a state that carries them says what it means --
              ;; which matters most on the restore path, where an implicit
              ;; nil would look identical to a genuinely uncompacted log.
              :log-base log-base
              :base-term base-term
              :commit commit
              ;; `applied` starts at `commit`, and the restart path emits a
              ;; `resync` carrying the committed prefix. See below: the pair is
              ;; the fix, and either half alone is wrong.
              :applied applied
              :stable li
              :issued li
              :pending-writes {}
              :next-write-token 0
              :self-ack nil
              :self-vote nil
              :votes {}
              :progress {}
              :election-timeout (:election-timeout cfg)
              :heartbeat-timeout (:heartbeat-timeout cfg)
              :propose-interval (:propose-interval cfg)
              :pre-vote? (:pre-vote? cfg)
              :log-retention (:log-retention cfg)
              :election-draw 0}
          st (fresh-fx st)
          st (-> st
                 (reset-state (:term st))
                 (assoc :role :follower)
                 (log-line :info (str "raft " (:peer-id cfg) " [peers: " (:validators st)
                                      ", term: " (:term st) ", commit: " commit
                                      ", lastindex: " li ", lastterm: "
                                      (or (term-at st li) 0) "]"))
                 arm-election-timer
                 ;; Announce the committed prefix we can prove from disk.
                 ;;
                 ;; `:applied` starts at `commit`, so without this an entry that
                 ;; was committed but NOT yet delivered is never delivered at
                 ;; all. That state is one this implementation deliberately
                 ;; creates: `flush-commits` holds delivery behind `:stable`, so
                 ;; a follower routinely has `commit=2, applied=0` with zero
                 ;; `:commit` effects emitted -- and for a follower the entries
                 ;; and the commit index arrive in the SAME message, so every
                 ;; crash with entries in flight lands in that window. The
                 ;; restarted node would then hold entries it had silently
                 ;; never handed over, diverging from every peer with nothing to
                 ;; re-check it.
                 ;;
                 ;; `resync` rather than `commit`, and that distinction is the
                 ;; whole reason the two effects were split. This is not a
                 ;; revocation and not an extension of the prefix: it is a
                 ;; restarting node telling the interpreter what it now believes
                 ;; its committed prefix to be, which is `resync`'s stated
                 ;; purpose. Re-emitting it as `commit` would APPEND a second
                 ;; copy of the prefix -- measured: `sim/agreement?` fails,
                 ;; because the restarted node's committed sequence no longer
                 ;; matches its peers'.
                 ;;
                 ;; etcd instead takes `Config.Applied` from the application and
                 ;; warns that, unset, "raft might return previous applied
                 ;; entries" (`raft.go:147-151`) -- it errs toward re-delivery
                 ;; and pushes idempotence onto the consumer. We can do better
                 ;; because our protocol has an effect that says exactly this.
                 ;; Announced whenever we RESTARTED, even if the prefix is
                 ;; empty. The guard used to be `(pos? commit)`, which is wrong
                 ;; in exactly the case that matters: the commit-index rides in
                 ;; the hard state, so a crash that loses the last write batch
                 ;; brings us back with `commit` 0 -- and then we announced
                 ;; nothing and re-delivered the prefix as fresh commits.
                 ;;
                 ;; Measured: a leader crashed with a write in flight came back
                 ;; and delivered entry 1 a second time, so its committed
                 ;; sequence read [e1 e1 e2] against its peers' [e1 e2 e3] and
                 ;; `sim/agreement?` failed. "I have nothing" is a statement
                 ;; about the prefix and has to be made, not omitted.
                 ;; ...but ONLY when the consumer has not said where it is,
                 ;; and only from an uncompacted log.
                 ;;
                 ;; `resync` replaces the consumer's view WHOLESALE, which is
                 ;; the right shape for a node that must GUESS. After
                 ;; compaction this node no longer holds its full committed
                 ;; prefix -- that is the point of compaction -- so announcing
                 ;; what it does hold would tell a ledger to drop every
                 ;; committed transaction below the boundary: data loss on the
                 ;; recovery path, caused by a successful optimisation.
                 ;;
                 ;; Suppressing it made that safe and opened a smaller hole in
                 ;; its place. `resync` exists because an entry committed but
                 ;; not yet DELIVERED would otherwise never be handed over, and
                 ;; suppressing it for compacted nodes disabled that fix for
                 ;; exactly those nodes.
                 ;;
                 ;; `:delivered-through` closes both. When the consumer says
                 ;; where it is there is nothing to guess: `applied` starts
                 ;; there and the gap goes out as ORDINARY commits, which
                 ;; append rather than replace and so cannot truncate anything.
                 ;; Compaction is irrelevant to it, because retention is
                 ;; measured from `applied` and the undelivered window is above
                 ;; `applied` by definition -- unless the consumer is further
                 ;; behind than retention, which is the one case we cannot
                 ;; serve and therefore say so.
                 (cond->
                  (and (number? delivered) (< applied commit)
                       (> (inc applied) log-base))
                   (update-in [:fx :commits] conj
                              (node/commit (vec (subvec (vec log)
                                                        (log-pos st (inc applied))
                                                        (log-pos st (inc commit))))))

                   (and (number? delivered) (< applied commit)
                        (<= (inc applied) log-base))
                   (update-in [:fx :logs] conj
                              (node/log-effect
                               :warn
                               {:event :consumer-behind-retention
                                :delivered applied :commit commit
                                :oldest-held (inc log-base)}))

                   (and (not (number? delivered))
                        (seq (:writes restored)) (zero? log-base))
                   (update-in [:fx :commits] conj
                              (node/resync (vec (subvec (vec log) 0 commit))))))]
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
        (finish (handle-persisted st (:token input) (:epoch input)))

        ;; A proposal. Only a leader may append; a follower would have to
        ;; forward it, and urd has no effect for handing a value to a peer as
        ;; anything other than a consensus message, so we drop it.
        :value-ready
        (finish
         (let [v (:value input)]
           (cond
             (not (and (= :leader (:role st))
                       (some? v)
                       (not= v {:payload :none})))
             st

             ;; ONE AT A TIME, and this is the check the whole safety argument
             ;; rests on -- not the activation point.
             ;;
             ;; A configuration differing from its predecessor by a single
             ;; voter always has majorities that intersect the old one's (Raft
             ;; thesis S4.1). Two changes in flight lose that: each could be
             ;; committed by a majority of a DIFFERENT configuration, so the
             ;; two quorums need not overlap. etcd states it as "we simply
             ;; disallow any proposed membership change while any uncommitted
             ;; change appears in the leader's log".
             ;;
             ;; Measured against `:commit`, because that is where urd
             ;; ACTIVATES. etcd measures against `applied` because their active
             ;; config is their applied config and applied trails commit
             ;; unboundedly; urd has no such lag. Getting this pairing wrong is
             ;; how a fixed offset becomes unsound -- see `activate-config`.
             (and (seq (:validator-updates v))
                  (some #(config-entry? (entry-at st %))
                        (range (inc (:commit st)) (inc (last-index st)))))
             (update-in st [:fx :logs] conj
                        (node/log-effect
                         :warn {:event :config-change-already-in-flight
                                :commit (:commit st) :last-index (last-index st)}))

             ;; Already joint. etcd refuses the same thing (`raft.go:1326`,
             ;; "must transition out of joint config first"): a second change
             ;; entering before the first has left would nest two transitions,
             ;; and the both-halves rule relates exactly TWO configurations.
             (and (seq (:validator-updates v)) (seq (:outgoing st)))
             (update-in st [:fx :logs] conj
                        (node/log-effect
                         :warn {:event :already-in-joint-config
                                :validators (:validators st)
                                :outgoing (:outgoing st)}))

             :else (-> st (append-entries [v]) bcast-append))))

        ;; Ticks are not used: all timing goes through logical timers.
        (finish st)))))

(defn make
  "A Raft node. Per-node configuration is supplied through the simulator's
  `:node-config`, or merged into `init`'s config by a runtime."
  []
  (->Raft))
