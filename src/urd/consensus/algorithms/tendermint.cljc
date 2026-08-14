(ns urd.consensus.algorithms.tendermint
  "Tendermint BFT consensus as a pure state machine on `urd.consensus.node`.

  The first genuinely BYZANTINE algorithm in the library: Raft tolerates
  crashes, Snowman is probabilistic, this one keeps agreement while f of 3f+1
  validators lie.

  ## Source of truth

  The normative algorithm is the pseudocode of arXiv:1807.04938, `The latest
  gossip on BFT consensus`, transcribed in the CometBFT tree at
  `spec/consensus/consensus-paper/consensus.tex:28-174`. Line numbers in the
  comments below (`L22`, `L28`, ...) refer to it.

  Two sources that look authoritative and are NOT used:

  - `spec/consensus/consensus.md` is STALE -- it documents the pre-2018
    PoLC/unlock design, and `spec/consensus/readme.md:26` says so.
  - CometBFT's own implementation DIVERGES from the paper in at least two
    places we deliberately did not copy: round-skip triggers on 2f+1
    (`consensus/state.go:2362`) where the paper uses f+1, and the L28 unlock is
    not a prevote rule there at all but happens asynchronously inside `addVote`
    (`consensus/state.go:2312-2328`). We implement the paper.

  The structure follows `spec/ivy-proofs/tendermint.ivy`, a mechanically
  checked transliteration in which the paper's `for the first time` latches are
  explicit relations -- `done_l34(R)`, `done_l36(R,V)`, `done_l47(R)`
  (`tendermint.ivy:86-88`). Those three latches are the trickiest bookkeeping
  in the protocol and having them named is worth the whole file.

  ## The rules, and the four traps

  Each of these is subtle enough that it has a dedicated test:

  - **L28's unlock is `lockedRound <= vr`** -- less-than-or-EQUAL. And the 2f+1
    prevotes it needs are at round `vr`, not at the current round.
  - **L36 fires when `step >= prevote`**, so it also fires when we are already
    in precommit; in that case ONLY validValue/validRound move.
  - **L36 sets `validRound := round_p`**, the current round, NOT the proposal's
    `vr`.
  - **L47 has no step guard at all**, and **L49 decides on ANY round r**, not
    only the current one.

  ## Where the crypto is not

  Signature verification happens outside this namespace, by construction:
  ClojureScript's Web Crypto is promise-based so geheimnis' Ed25519 verify
  returns a channel and cannot be called from a pure function. Events arrive
  pre-authenticated with `:verified-by`, which is exactly the seam CometBFT's
  own layering already has -- `addVerifiedVote` is documented \"assumes
  signature is valid\" (`types/vote_set.go:259-329`).

  A consequence worth stating: `(vote -> signature)` is NOT a function.
  Signatures from a remote signer can be non-deterministic; CometBFT carries
  `ErrVoteNonDeterministicSignature` (`types/vote_set.go:215`) precisely for
  this. So two votes from the same validator for the same value with DIFFERENT
  signature bytes are a duplicate, not equivocation. Only a differing value is
  equivocation, and it is reported through `report-equivocation` rather than
  dropped.

  ## Durability

  CometBFT fsyncs exactly the messages this node SIGNS -- its own proposal,
  prevote, precommit -- plus the end-height marker, in one function with a
  `default: panic` so that a new self-message type cannot silently skip the
  barrier (`consensus/state.go:881-905`). `signed-message-step` below is that
  function, throw and all.

  The ordering is STRICTER than Raft's: sign -> fsync -> apply -> broadcast,
  with the fsync happening before this state machine even sees its own message.
  So a signed message is put in `:pending-signed`, the broadcast rides in the
  `:then` of a `persist-then`, and the vote is added to our own tally only when
  the `persisted` event comes back. A node that crashes before its own fsync
  has not voted, which is the entire point.

  ## Portability

  `.cljc`, no host interop, no clock, no RNG. Timeouts are logical ticks and
  grow per round: `timeout(r) = init + r*delta`, reset at each height."
  (:require [urd.consensus.node :as node]
            [urd.consensus.proposer :as proposer]
            [urd.consensus.signing :as signing]))

;; ============================================================
;; Value identity
;;
;; The paper carefully distinguishes a value `v` from its id `id(v)`: the
;; proposal carries the value, votes carry only the id. We keep that split,
;; because the locking rules compare ids and conflating the two hides bugs
;; where a node matches on a field the vote never carried.
;; ============================================================

(defn value-id
  "`id(v)`. A map carrying `:id` supplies its own; anything else is its own id.

  Deliberately not a hash: `hasch/sha256` is synchronous on both platforms so
  hashing here would be legal, but it would force every test value through an
  opaque digest for no gain. A real deployment supplies `:id`."
  [v]
  (cond
    (nil? v) nil
    (and (map? v) (contains? v :id)) (:id v)
    :else v))

;; ============================================================
;; Membership: BFT quorums by voting power
;;
;; `node/bft-membership` is the uniform-weight special case of this: it counts
;; statements against `byzantine-threshold(n)`. That is not enough here for two
;; reasons, both of which are findings rather than nuisances -- see the PR.
;;
;;   1. Tendermint quorums are over VOTING POWER, not validator count.
;;   2. `ThresholdMembership` counts statements, so two statements from the
;;      same sender count twice. For a Byzantine algorithm that is a safety
;;      bug, not a rounding error.
;;
;; Both are fixed by summing `weight` over DISTINCT senders. With uniform
;; powers this record and `node/bft-membership` agree exactly.
;; ============================================================

(defn- sum-power [state senders]
  (reduce (fn [acc s] (+ acc (get-in state [:powers s] 0))) 0 senders))

(defrecord PowerWeightedBft []
  node/Membership
  (quorum? [_ state statements pred]
    (let [total (reduce + 0 (vals (:powers state)))
          senders (into #{} (comp (filter pred) (map :from)) statements)]
      (>= (sum-power state senders) (node/byzantine-threshold total))))

  (v-blocking? [_ state statements pred]
    ;; f+1 by power, expressed as the dual of the quorum: a set blocks when its
    ;; complement can no longer reach the threshold. That dual is exactly the
    ;; paper's `f+1` at every n -- which is a small but pleasing result: L55's
    ;; round-skip trigger IS the v-blocking predicate, not a separate constant.
    (let [total (reduce + 0 (vals (:powers state)))
          senders (into #{} (comp (filter pred) (map :from)) statements)]
      (> (sum-power state senders)
         (- total (node/byzantine-threshold total)))))

  (weight [_ state peer-id] (get-in state [:powers peer-id] 0)))

(def power-weighted-bft (->PowerWeightedBft))

(defn fault-tolerance
  "f, the number of Byzantine faults a set of `total` voting power tolerates.

  Note f = 0 below 4: three equal validators tolerate NO Byzantine fault."
  [total]
  (node/byzantine-tolerance total))

;; ============================================================
;; Effect accumulation
;;
;; Same shape as the Raft port: helpers thread the node state and stash effects
;; under `:fx`, which `finish` strips. `step` is still a pure function of
;; (state, input).
;; ============================================================

(defn- fresh-fx [st]
  (assoc st :fx {:msgs [] :logs [] :signed []}))

(defn- emit [st effect] (update-in st [:fx :msgs] conj effect))
(defn- log-line [st level msg] (update-in st [:fx :logs] conj (node/log-effect level msg)))

;; ============================================================
;; The durability barrier
;; ============================================================

(defn signed-message-step
  "Which signing step is this self-message, if any?

  This is `writeInternalMsgToWAL` (`consensus/state.go:881-905`) transliterated,
  `default: panic` included. The panic is the load-bearing part: it is what
  stops someone adding a fourth self-message type in six months and having it
  silently skip the fsync. An unsigned message must be listed explicitly as
  unsigned, not merely omitted."
  [msg]
  (case (:type msg)
    :proposal :propose
    :prevote :prevote
    :precommit :precommit
    ;; The end-height marker is durable but not signed; it has no signing step,
    ;; so it does not participate in the double-sign guard.
    :end-height nil
    (throw (ex-info "unexpected self-message type: refusing to guess whether it needs an fsync"
                    {:msg msg}))))

(defn- sign-and-broadcast
  "Sign a message, put it behind the durability barrier, and gate its broadcast
  on the write landing.

  Refuses -- loudly, and without changing the round state -- when the
  double-sign guard says no. Skipping the broadcast costs liveness for a round;
  signing anyway costs the validator its stake."
  [st msg]
  (let [candidate {:height (:height msg) :round (:round msg)
                   :step (signed-message-step msg)}]
    (if-not (signing/may-sign? candidate (:last-signed st))
      (log-line st :error
                (str (:id st) " REFUSING to sign " (:type msg)
                     " at " [(:height msg) (:round msg)]
                     "; last signed " (:last-signed st)))
      (let [token [:signed (:write-seq st)]]
        (-> st
            (assoc :last-signed candidate)
            (update :write-seq inc)
            (assoc-in [:pending-signed token] msg)
            (update-in [:fx :signed] conj
                       {:token token
                        :msg msg
                        ;; The epoch witness. Tendermint's WAL is append-only,
                        ;; so there is no ABA hazard of the kind etcd-raft
                        ;; guards against; what the witness DOES catch here is
                        ;; a completion that arrives after we decided and moved
                        ;; to the next height, where applying our own stale
                        ;; vote to the fresh message log would be wrong.
                        :epoch [(:height msg) (:round msg)]
                        :then [(node/broadcast :consensus msg)]}))))))

;; ============================================================
;; Message log
;;
;; Per height. Proposals and votes are stored keyed by sender, so a quorum
;; count over `vals` is automatically one-per-sender.
;; ============================================================

(defn- votes-at [st kind r] (vals (get-in st [kind r] {})))

(defn- quorum-for?
  "2f+1 by power for a specific value id (nil means the nil-value vote)."
  [st kind r vid]
  (node/quorum? (:membership st) st (votes-at st kind r)
                #(= vid (:value-id %))))

(defn- quorum-any?
  "2f+1 by power for anything at all -- the `*` in the paper."
  [st kind r]
  (node/quorum? (:membership st) st (votes-at st kind r) (constantly true)))

;; ============================================================
;; Proposer selection
;; ============================================================

(defn- proposer-at [st r]
  (proposer/proposer-for (:priorities st) (:powers st) r))

(defn- proposal-from-proposer
  "The proposal for round `r` from the validator that is actually the proposer
  for it. A proposal from anyone else is not a proposal, which is what makes an
  equivocating non-proposer harmless."
  [st r]
  (get-in st [:proposals r (proposer-at st r)]))

;; ============================================================
;; Equivocation
;;
;; A first-class OUTPUT of the state machine, not a dropped message. The first
;; statement stands and is what counts toward quorums; the conflicting one
;; becomes evidence.
;; ============================================================

(defn- report-conflict [st from kind r existing conflicting]
  (let [key [from kind r]]
    (if (contains? (:reported st) key)
      st
      (-> st
          (update :reported conj key)
          (log-line :warn (str (:id st) " detected equivocation by " from
                               " (" (name kind) " at height " (:height st)
                               " round " r ")"))
          (emit (node/report-equivocation
                 from
                 {:kind kind
                  :height (:height st)
                  :round r
                  :conflicting [existing conflicting]}))))))

;; ============================================================
;; Recording messages
;; ============================================================

(def ^:private vote-kinds {:prevote :prevotes :precommit :precommits})

(defn- record-vote [st kind msg]
  (let [bucket (vote-kinds kind)
        r (:round msg)
        from (:from msg)
        existing (get-in st [bucket r from])]
    (cond
      (nil? existing) (assoc-in st [bucket r from] msg)

      ;; Same value: a duplicate. NOT compared by signature bytes -- see the
      ;; namespace docstring; a remote signer may legitimately produce two
      ;; different signatures over the same vote.
      (= (:value-id existing) (:value-id msg)) st

      :else (report-conflict st from kind r existing msg))))

(defn- record-proposal [st msg]
  (let [r (:round msg)
        from (:from msg)
        existing (get-in st [:proposals r from])]
    (cond
      (nil? existing) (assoc-in st [:proposals r from] msg)

      (and (= (value-id (:value existing)) (value-id (:value msg)))
           (= (:vr existing) (:vr msg)))
      st

      ;; An equivocating proposer -- two different proposals for the same
      ;; round. This is the canonical Byzantine attack and the reason
      ;; `report-equivocation` exists.
      :else (report-conflict st from :proposal r existing msg))))

(def ^:private max-future-heights 3)
(def ^:private max-future-messages 500)

(defn- record-message
  "File one authenticated message. Messages for the current height enter the
  log; a small window of future heights is buffered, everything else dropped."
  [st msg]
  (let [h (:height msg)]
    (cond
      (< h (:height st)) st

      (> h (:height st))
      (if (or (> h (+ (:height st) max-future-heights))
              (>= (count (get-in st [:future h] [])) max-future-messages))
        st
        (update-in st [:future h] (fnil conj []) msg))

      :else
      (case (:type msg)
        :proposal (record-proposal st msg)
        :prevote (record-vote st :prevote msg)
        :precommit (record-vote st :precommit msg)
        st))))

(defn- ingest
  "An authenticated message arrived from a peer.

  `verified-by` is the set of peer-ids whose signature was checked at the edge.
  We insist the claimed author is in it: a Byzantine node may say anything in
  its own name but may not forge another validator's identity, which is exactly
  the adversary the Ivy model assumes (`tendermint.ivy:379-383`)."
  [st from msg verified-by]
  (cond
    (not (contains? (set (:validators st)) (:from msg)))
    (log-line st :warn (str (:id st) " dropping message from non-validator " (:from msg)))

    (not (contains? (or verified-by #{}) (:from msg)))
    (log-line st :warn (str (:id st) " dropping message whose author " (:from msg)
                            " was not verified (relayed by " from ")"))

    :else (record-message st msg)))

;; ============================================================
;; Timers
;;
;; timeout(r) = init + r*delta, reset at each height. Timer ids carry the
;; (height, round) they were armed for so that a stale firing is a no-op rather
;; than a state transition at the wrong round.
;; ============================================================

(defn- timeout-for [st kind r]
  (+ (get st (case kind
               :propose :timeout-propose
               :prevote :timeout-prevote
               :precommit :timeout-precommit))
     (* r (:timeout-delta st))))

(defn- arm-timer [st kind r]
  (emit st (node/set-timer [kind (:height st) r] (timeout-for st kind r))))

(defn- cancel-round-timers [st h r]
  (reduce (fn [s k] (emit s (node/cancel-timer [k h r])))
          st
          [:propose :prevote :precommit]))

(def gossip-timer
  "Deliberately not carrying (height, round): retransmission is a property of
  the node, not of a round."
  [:gossip])

(defn- arm-gossip [st]
  (if-let [n (:gossip-interval st)]
    (emit st (node/set-timer gossip-timer n))
    st))

(defn- gossip
  "Re-broadcast the messages we ourselves signed at this height.

  The paper assumes a gossip layer that eventually delivers every message; the
  `Node` protocol has no retransmission of its own, and neither does the
  algorithm -- unlike Raft, whose AppendEntries retry loop IS the algorithm.
  Without this seam a single dropped prevote wedges the height forever, because
  nothing in the paper ever re-sends one. CometBFT puts the same behaviour in
  `consensus/reactor.go`'s gossipVotesRoutine.

  Re-sending an already-signed message is not a second signature, so this never
  touches the double-sign guard. Only the current and immediately preceding
  round are re-sent: older rounds cannot change any peer's decision that a
  newer round has not already settled."
  [st]
  (let [me (:id st)
        floor (max 0 (dec (:round st)))
        mine (for [bucket [:proposals :prevotes :precommits]
                   [r by-sender] (get st bucket)
                   :when (>= r floor)
                   :let [m (get by-sender me)]
                   :when m]
               m)
        ;; Sorted so the effect vector is a function of the state alone; map
        ;; iteration order must never reach the trace.
        ordered (sort-by (juxt :round #(case (:type %) :proposal 0 :prevote 1 :precommit 2))
                         mine)]
    (-> (reduce (fn [s m] (emit s (node/broadcast :consensus m)))
                st
                ;; Our own messages from the height we last decided, so a peer
                ;; that is exactly one height behind can still assemble the
                ;; quorum it missed. CometBFT gossips the LastCommit for the
                ;; same reason. It closes a one-height lag and nothing more --
                ;; see the note on catch-up in the PR.
                (concat (:last-commit st) ordered))
        arm-gossip)))

(defn- own-messages-at-height
  "Everything this node itself signed at the current height, ordered."
  [st]
  (let [me (:id st)]
    (->> (for [bucket [:proposals :prevotes :precommits]
               [_ by-sender] (get st bucket)
               :let [m (get by-sender me)]
               :when m]
           m)
         (sort-by (juxt :round #(case (:type %) :proposal 0 :prevote 1 :precommit 2)))
         vec)))

;; ============================================================
;; Broadcasting our own votes
;; ============================================================

(defn- broadcast-prevote [st vid]
  (sign-and-broadcast st {:type :prevote :from (:id st)
                          :height (:height st) :round (:round st)
                          :value-id vid}))

(defn- broadcast-precommit [st vid]
  (sign-and-broadcast st {:type :precommit :from (:id st)
                          :height (:height st) :round (:round st)
                          :value-id vid}))

(defn- broadcast-proposal [st v vr]
  (sign-and-broadcast st {:type :proposal :from (:id st)
                          :height (:height st) :round (:round st)
                          :value v :vr vr}))

;; ============================================================
;; StartRound (L11-21)
;; ============================================================

(defn- valid? [st v]
  (boolean ((:valid-fn st) v)))

(defn- start-round [st r]
  (let [prev (:round st)
        st (-> st
               (cancel-round-timers (:height st) prev)
               (assoc :round r :step :propose :awaiting-value nil))]
    (if (= (:id st) (proposer-at st r))
      ;; L15-18: re-propose validValue if we have one, otherwise ask the
      ;; application. `getValue()` is synchronous in the paper and an EFFECT
      ;; here, so the proposal is finished by the `value-ready` event.
      (if-let [vv (:valid-value st)]
        (broadcast-proposal st vv (:valid-round st))
        (-> st
            (assoc :awaiting-value {:height (:height st) :round r})
            (emit (node/request-value {:height (:height st) :round r}))))
      ;; L21
      (arm-timer st :propose r))))

;; ============================================================
;; Height transition
;; ============================================================

(defn- advance-height
  "L51-54: bump the height, reset the locking AND liveness state, empty the
  message log, StartRound(0).

  Resetting validValue/validRound as well as lockedValue/lockedRound is not
  optional: the paper says `reset ... to initial values`, and carrying a valid
  value across a height would make a node propose the PREVIOUS height's block."
  [st]
  (let [old-h (:height st)
        new-h (inc old-h)
        buffered (get-in st [:future new-h] [])
        last-commit (own-messages-at-height st)
        st (-> st
               (cancel-round-timers old-h (:round st))
               (assoc :last-commit last-commit)
               (assoc :height new-h
                      :locked-value nil :locked-value-id nil :locked-round -1
                      :valid-value nil :valid-round -1
                      :proposals {} :prevotes {} :precommits {}
                      :done-l34 #{} :done-l36 #{} :done-l44 #{} :done-l47 #{}
                      :reported #{}
                      :awaiting-value nil)
               (assoc :priorities (proposer/advance (:priorities st) (:powers st)))
               (update :future dissoc new-h))
        st (reduce record-message st buffered)]
    (start-round st 0)))

(defn- decide
  "L49-54. The decision itself is durable: the end-height marker is CometBFT's
  one non-signed WAL barrier, and the `commit` effect rides in its `:then`, so
  no node can be observed to have decided a value it might forget."
  [st r v]
  (let [h (:height st)
        token [:end-height h]]
    (-> st
        (assoc-in [:decisions h] v)
        (assoc-in [:pending-end-height token] h)
        (log-line :info (str (:id st) " decided " (value-id v)
                             " at height " h " round " r))
        (update-in [:fx :signed] conj
                   {:token token
                    :msg {:type :end-height :height h :decision v}
                    :epoch [h r]
                    :then [(node/commit [v] h)]}))))

;; ============================================================
;; The upon-rules
;;
;; Each returns nil when it does not fire, or the new state when it does.
;; `apply-rules` runs the first that fires; `run-rules` iterates to a fixpoint,
;; which is required -- one arriving precommit can complete a quorum that both
;; arms the L47 timer and satisfies L49.
;; ============================================================

(defn- rule-l22
  "L22-27: a proposal with vr = -1 while still in propose."
  [st]
  (when (= :propose (:step st))
    (let [r (:round st)
          p (proposal-from-proposer st r)]
      (when (and p (= -1 (:vr p)))
        (let [v (:value p)
              vid (value-id v)]
          (-> st
              (broadcast-prevote
               (if (and (valid? st v)
                        (or (= -1 (:locked-round st))
                            (= (:locked-value-id st) vid)))
                 vid
                 nil))
              (assoc :step :prevote)))))))

(defn- rule-l28
  "L28-33: a proposal that carries a valid-round, backed by 2f+1 prevotes AT
  THAT ROUND.

  Two traps live here. The prevote quorum is at `vr`, not at the current round.
  And the unlock condition is `lockedRound <= vr` -- less-than-or-EQUAL. With
  `<` a node locked at exactly `vr` would prevote nil for the very value it is
  locked on, and the algorithm would lose liveness in the case the rule exists
  to handle."
  [st]
  (when (= :propose (:step st))
    (let [r (:round st)
          p (proposal-from-proposer st r)]
      (when (and p (<= 0 (:vr p)) (< (:vr p) r))
        (let [vr (:vr p)
              v (:value p)
              vid (value-id v)]
          (when (quorum-for? st :prevotes vr vid)
            (-> st
                (broadcast-prevote
                 (if (and (valid? st v)
                          (or (<= (:locked-round st) vr)
                              (= (:locked-value-id st) vid)))
                   vid
                   nil))
                (assoc :step :prevote))))))))

(defn- rule-l34
  "L34-35: 2f+1 prevotes for anything, in prevote, for the first time."
  [st]
  (let [r (:round st)]
    (when (and (= :prevote (:step st))
               (not (contains? (:done-l34 st) r))
               (quorum-any? st :prevotes r))
      (-> st
          (update :done-l34 conj r)
          (arm-timer :prevote r)))))

(defn- rule-l36
  "L36-43: a proposal plus 2f+1 prevotes for it, for the first time per (r, v).

  Three traps. The guard is `step >= prevote`, so this ALSO fires while already
  in precommit -- in which case only validValue/validRound move. `validRound`
  is set to the CURRENT round, not to the proposal's `vr`. And the latch is
  keyed by (round, value), not by round alone, because a Byzantine proposer can
  put two values in play at one round."
  [st]
  (let [r (:round st)
        p (proposal-from-proposer st r)]
    (when p
      (let [v (:value p)
            vid (value-id v)]
        (when (and (#{:prevote :precommit} (:step st))
                   (valid? st v)
                   (not (contains? (:done-l36 st) [r vid]))
                   (quorum-for? st :prevotes r vid))
          (cond-> (update st :done-l36 conj [r vid])
            ;; NOTE: cond->'s tests read the ORIGINAL `st`, so this is the step
            ;; on entry, which is what the rule means.
            (= :prevote (:step st))
            (-> (assoc :locked-value v :locked-value-id vid :locked-round r)
                (broadcast-precommit vid)
                (assoc :step :precommit))

            true
            (assoc :valid-value v :valid-round r)))))))

(defn- rule-l44
  "L44-46: 2f+1 prevotes for nil while in prevote."
  [st]
  (let [r (:round st)]
    (when (and (= :prevote (:step st))
               (quorum-for? st :prevotes r nil)
               ;; Without this the rule would re-fire forever: it changes step
               ;; to precommit, which is its own guard, so the latch is
               ;; implicit -- but only after the precommit is actually signed.
               ;; Belt and braces for the refused-signature path.
               (not (contains? (:done-l44 st) r)))
      (-> st
          (update :done-l44 conj r)
          (broadcast-precommit nil)
          (assoc :step :precommit)))))

(defn- rule-l47
  "L47-48: 2f+1 precommits for anything, for the first time.

  NO STEP GUARD. It fires in propose, prevote or precommit alike."
  [st]
  (let [r (:round st)]
    (when (and (not (contains? (:done-l47 st) r))
               (quorum-any? st :precommits r))
      (-> st
          (update :done-l47 conj r)
          (arm-timer :precommit r)))))

(defn- rule-l49
  "L49-54: a proposal at ANY round r plus 2f+1 precommits for it at r.

  The `any round` part is not a detail: a node whose network was slow can be at
  round 5 while the decision quorum formed at round 2, and it must still
  decide. Rounds are scanned in ascending order so the outcome cannot depend on
  map iteration order."
  [st]
  (when (nil? (get (:decisions st) (:height st)))
    (some (fn [r]
            (let [p (proposal-from-proposer st r)]
              (when p
                (let [v (:value p)]
                  (when (and (valid? st v)
                             (quorum-for? st :precommits r (value-id v)))
                    (decide st r v))))))
          (sort (keys (:precommits st))))))

(defn- senders-at-round
  "Everyone we have heard from at `r`, whatever the message type."
  [st r]
  (into #{}
        (concat (keys (get-in st [:proposals r] {}))
                (keys (get-in st [:prevotes r] {}))
                (keys (get-in st [:precommits r] {})))))

(defn- rule-l55
  "L55-56: f+1 messages from a future round -> jump to it.

  The paper uses f+1, CometBFT uses 2f+1 (`consensus/state.go:2362`); we follow
  the paper. f+1 by voting power is exactly the `v-blocking?` predicate -- a set
  that can block us from a quorum is a set that must contain an honest member --
  so this rule needs no new arithmetic.

  Of the qualifying rounds we take the HIGHEST: every one of them has an honest
  validator in it, so all are legitimately reachable, and jumping straight to
  the furthest avoids walking through rounds nobody is in any more."
  [st]
  (let [cands (->> (concat (keys (:proposals st)) (keys (:prevotes st)) (keys (:precommits st)))
                   distinct
                   (filter #(> % (:round st)))
                   (filter (fn [r]
                             (node/v-blocking? (:membership st) st
                                               (map (fn [s] {:from s}) (senders-at-round st r))
                                               (constantly true))))
                   seq)]
    (when cands
      (start-round st (apply max cands)))))

(def ^:private rules
  "Rule order is fixed rather than the paper's `picked randomly`, because a
  deterministic simulator is worth more than fidelity to a scheduling
  non-determinism that the safety proof does not depend on. L49 runs first so a
  reachable decision is never delayed by a round change."
  [rule-l49 rule-l22 rule-l28 rule-l36 rule-l44 rule-l34 rule-l47 rule-l55])

(defn- apply-rules
  "Fire the first rule that fires. Returns [st fired?]."
  [st]
  (if (get (:decisions st) (:height st))
    ;; We have decided this height and are waiting for the end-height marker to
    ;; land. The paper moves to h+1 atomically here, so no rule may run at the
    ;; old height in the meantime.
    [st false]
    (loop [rs rules]
      (if-let [r (first rs)]
        (if-let [st' (r st)]
          [st' true]
          (recur (next rs)))
        [st false]))))

(def ^:private max-rule-iterations 200)

(defn- run-rules [st]
  (loop [st st, i 0]
    (let [[st' fired?] (apply-rules st)]
      (cond
        (not fired?) st'
        (>= i max-rule-iterations)
        (throw (ex-info "tendermint rule fixpoint did not converge"
                        {:id (:id st) :height (:height st) :round (:round st)}))
        :else (recur st' (inc i))))))

;; ============================================================
;; Timeouts
;; ============================================================

(defn- handle-timer [st timer-id]
  (cond
    (= gossip-timer timer-id) (gossip st)

    (not (and (vector? timer-id) (= 3 (count timer-id)))) st

    ;; We have decided this height and are waiting for the end-height marker to
    ;; land. The paper increments the height in the same atomic step as the
    ;; decision, so no round timer may fire in the gap our durability barrier
    ;; opens -- otherwise a node could start, and PROPOSE at, a round of a
    ;; height it has already finished.
    (get (:decisions st) (:height st)) st

    :else
    (let [[kind h r] timer-id]
      (if-not (and (= h (:height st)) (= r (:round st)))
        ;; A timer from a round or height we have left. Not an error: rounds
        ;; are abandoned all the time.
        st
        (case kind
          ;; L57-60
          :propose (if (= :propose (:step st))
                     (-> st (broadcast-prevote nil) (assoc :step :prevote))
                     st)
          ;; L61-64
          :prevote (if (= :prevote (:step st))
                     (-> st (broadcast-precommit nil) (assoc :step :precommit))
                     st)
          ;; L65-67 -- note NO step guard
          :precommit (start-round st (inc r))
          st)))))

;; ============================================================
;; Durability completions
;; ============================================================

(defn- handle-persisted
  "Our own write landed.

  For a signed message this is the `apply` in CometBFT's
  sign -> fsync -> apply -> broadcast: only now does our own vote count toward
  a quorum. For the end-height marker it is the point at which the height may
  advance."
  [st token epoch]
  (cond
    (contains? (:pending-signed st) token)
    (let [msg (get (:pending-signed st) token)
          st (update st :pending-signed dissoc token)]
      (if (not= (first epoch) (:height st))
        ;; The epoch witness earning its keep: we decided and moved on while
        ;; this write was in flight, so our own vote belongs to a height whose
        ;; message log no longer exists. Dropping it is a no-op, not an error.
        (log-line st :debug
                  (str (:id st) " dropping durable self-vote from height "
                       (first epoch) " at height " (:height st)))
        (record-message st msg)))

    (contains? (:pending-end-height st) token)
    (-> st
        (update :pending-end-height dissoc token)
        advance-height)

    :else st))

(defn- handle-value-ready
  "The application supplied a value for the proposal we owe."
  [st v]
  (let [{:keys [height round]} (:awaiting-value st)]
    (if (and height
             (= height (:height st))
             (= round (:round st))
             (= :propose (:step st)))
      (-> st
          (assoc :awaiting-value nil)
          (broadcast-proposal v (:valid-round st)))
      st)))

;; ============================================================
;; Assembling effects
;; ============================================================

(defn- finish [st]
  (let [{:keys [msgs logs signed]} (:fx st)
        st (dissoc st :fx)
        persists (mapv (fn [{:keys [token msg epoch then]}]
                         ;; One write per message, each with its own
                         ;; caller-supplied token. Raft had to assume the
                         ;; interpreter completes writes in issue order because
                         ;; it could not name its own writes; here the token is
                         ;; the correlation, so several signed messages can be
                         ;; in flight at once without ambiguity.
                         (node/persist-then {:writes {:wal msg}
                                             :durable? true
                                             :epoch epoch
                                             :token token
                                             :then then}))
                       signed)]
    (node/result st (vec (concat logs msgs persists)))))

;; ============================================================
;; Restart: replaying the durable write log
;;
;; Scope note: the WAL FORMAT is out of scope, so we replay only what this node
;; itself wrote -- its signed messages and its end-height markers. That is
;; strictly less than CometBFT replays (it replays received messages too), and
;; the difference is a liveness cost, never a safety one:
;;
;;   - lockedValue/lockedRound ARE recoverable from our own precommits, because
;;     L36 sets them in the same breath as it precommits;
;;   - validValue/validRound are NOT, and are lost. They exist for termination,
;;     not safety, so a restarted node simply proposes a fresh value;
;;   - the double-sign guard is recovered exactly, which is the part that must
;;     not be approximate.
;; ============================================================

(defn- replay-one [acc msg]
  (case (:type msg)
    :end-height
    (-> acc
        (assoc-in [:decisions (:height msg)] (:decision msg))
        (assoc :height (inc (:height msg))
               :round 0
               :step :propose
               :locked-value nil :locked-value-id nil :locked-round -1
               ;; A restarted node can still serve the commit it just made, so
               ;; a peer one height behind is not orphaned by our restart.
               :last-commit (vec (:own-messages acc))
               :own-messages []))

    (:proposal :prevote :precommit)
    (if (not= (:height msg) (:height acc))
      acc
      (let [r (:round msg)
            ;; The last thing we signed at a round IS our step at that round --
            ;; L22/L28 prevote and set step in one move, L36 precommits and
            ;; sets step in one move -- so the round state is recoverable
            ;; exactly from our own signatures.
            acc (assoc acc
                       :last-signed {:height (:height msg) :round r
                                     :step (signed-message-step msg)}
                       :round (max (:round acc) r)
                       :step (case (:type msg)
                               :proposal :propose
                               :prevote :prevote
                               :precommit :precommit))
            acc (update acc :own-messages conj msg)]
        ;; L38-39: locking happens in the same breath as precommitting a
        ;; non-nil value, so our own precommits determine lockedValue.
        (if (and (= :precommit (:type msg)) (some? (:value-id msg)))
          (assoc acc :locked-value-id (:value-id msg) :locked-round r)
          acc)))

    acc))

(defn- replay
  "Fold the ordered log of landed writes into restored state."
  [acc writes]
  (reduce (fn [acc {w :writes}]
            (if-let [msg (:wal w)] (replay-one acc msg) acc))
          acc
          (or writes [])))

;; ============================================================
;; The Node implementation
;; ============================================================

(def default-config
  {:timeout-propose 10
   :timeout-prevote 8
   :timeout-precommit 8
   :timeout-delta 2
   ;; Ticks between retransmissions of our own signed messages. `nil` turns
   ;; retransmission off, which is the literal paper and is only live on a
   ;; perfectly reliable network -- see `gossip`.
   :gossip-interval 12})

(defrecord Tendermint []
  node/Node

  (init [_ config]
    (let [cfg (merge default-config config)
          validators (vec (sort (:validators cfg)))
          powers (or (:powers cfg) (into {} (map (fn [v] [v 1])) validators))
          base {:id (:peer-id cfg)
                :validators validators
                :powers powers
                :membership (or (:membership cfg) power-weighted-bft)
                :valid-fn (or (:valid-fn cfg) (constantly true))
                :height 0
                :round 0
                :step :propose
                :decisions {}
                :locked-value nil
                :locked-value-id nil
                :locked-round -1
                :valid-value nil
                :valid-round -1
                :proposals {}
                :prevotes {}
                :precommits {}
                :done-l34 #{}
                :done-l36 #{}
                :done-l44 #{}
                :done-l47 #{}
                :reported #{}
                :future {}
                :priorities (proposer/initial-priorities validators)
                :last-signed nil
                :pending-signed {}
                :pending-end-height {}
                :write-seq 0
                :awaiting-value nil
                :last-commit []
                :own-messages []
                :timeout-propose (:timeout-propose cfg)
                :timeout-prevote (:timeout-prevote cfg)
                :timeout-precommit (:timeout-precommit cfg)
                :timeout-delta (:timeout-delta cfg)
                :gossip-interval (:gossip-interval cfg)}
          restored (replay base (get-in cfg [:restored :writes]))
          ;; Proposer priorities advance once per decided height.
          st (assoc restored :priorities
                    (reduce (fn [p _] (proposer/advance p powers))
                            (:priorities restored)
                            (range (:height restored))))
          own (:own-messages st)
          st (assoc st :own-messages [])
          st (fresh-fx st)
          st (reduce record-message st own)
          st (log-line st :info
                       (str "tendermint " (:id st) " [validators: " validators
                            ", height: " (:height st) ", round: " (:round st)
                            ", step: " (:step st)
                            ", locked: " (:locked-value-id st) "@" (:locked-round st) "]"))
          ;; A fresh node runs StartRound(0); a restarted one resumes the round
          ;; it was in, and arms the propose timer if it never got a proposal.
          st (if (and (zero? (:height st)) (zero? (:round st)) (nil? (:last-signed st)))
               (start-round st 0)
               ;; A restarted node resumes the round it was in rather than
               ;; restarting the height, so it does not have to re-derive a
               ;; step it already signed its way past.
               (if (= :propose (:step st))
                 (arm-timer st :propose (:round st))
                 st))
          st (arm-gossip st)]
      (finish (run-rules st))))

  (step [_ state input]
    (let [st (fresh-fx state)]
      (finish
       (run-rules
        (case (:type input)
          :message-received (ingest st (:from input) (:msg input) (:verified-by input))
          :timer-fired (handle-timer st (:timer-id input))
          :persisted (handle-persisted st (:token input) (:epoch input))
          :value-ready (handle-value-ready st (:value input))
          st))))))

(defn make
  "A Tendermint node. Per-node configuration -- `:powers`, `:valid-fn`, the
  timeouts -- is supplied through the simulator's `:node-config` or merged into
  `init`'s config by a runtime."
  []
  (->Tendermint))

;; ============================================================
;; Inspection helpers for tests and runtimes
;; ============================================================

(defn decided
  "The value this node decided at `height`, or nil."
  [st height]
  (get (:decisions st) height))

(defn locked [st] [(:locked-value-id st) (:locked-round st)])
(defn valid-pair [st] [(value-id (:valid-value st)) (:valid-round st)])
