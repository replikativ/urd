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
            [hasch.core :as hasch]
            [urd.consensus.proposer :as proposer]
            [urd.consensus.reconfig :as reconfig]
            [urd.consensus.signing :as signing]
            [urd.wire :as wire]))

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

  An explicit id is part of the existing vote format. For structured values,
  deployments must supply a deterministic :valid-fn that recomputes the
  canonical identifier from the entire consensus payload, including validator
  updates. All accepted values sharing an id must be identical."
  [v]
  (cond
    (nil? v) nil
    (and (map? v) (contains? v :id)) (:id v)
    :else v))

(defn content-id
  "Lowercase hexadecimal SHA-256 of a proposal map's canonical CBOR payload.

  Build a proposal with (assoc payload :id (content-id payload)). Every
  top-level field except :id participates, including :validator-updates."
  [proposal]
  (when-not (map? proposal)
    (throw (ex-info "content-id requires a proposal map" {})))
  (-> (dissoc proposal :id) wire/signing-bytes hasch/sha256 hasch/hash->str))

(defn valid-content-id?
  "A :valid-fn for deployments using content-id. Compose with the application's
  schema, transaction, and reconfiguration checks, e.g. (every-pred
  valid-content-id? application-valid?). All validators must agree on the
  accepted payload representation."
  [proposal]
  (and (map? proposal)
       (string? (:id proposal))
       (try (= (:id proposal) (content-id proposal))
            (catch #?(:clj Exception :cljs :default) _ false))))

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

(declare vote-payload)

(defn- sign-and-broadcast
  "Sign a message, put it behind the durability barrier, and gate its broadcast
  on the write landing.

  Refuses -- loudly, and without changing the round state -- when the
  double-sign guard says no. Skipping the broadcast costs liveness for a round;
  signing anyway costs the validator its stake."
  [st msg]
  (let [candidate {:height (:height msg) :round (:round msg)
                   :step (signed-message-step msg)}]
    (if-not (and (> (:height st) (:voting-blocked-through st -1))
                 (contains? (:powers st) (:id st))
                 (signing/may-sign? candidate (:last-signed st)))
      (log-line st :error
                (str (:id st) " REFUSING to sign " (:type msg)
                     " at " [(:height msg) (:round msg)]
                     "; last signed " (:last-signed st)))
      (let [token [:signed (:write-seq st)]
            msg (cond-> msg
                  (and (= :precommit (:type msg)) (:sign-vote st))
                  (assoc :att ((:sign-vote st) (:id st)
                                               (vote-payload (:height msg) (:round msg) (:value-id msg)))))]
        (-> st
            (assoc :last-signed candidate)
            (update :write-seq inc)
            (assoc-in [:pending-signed token] msg)
            (update-in [:fx :signed] conj
                       {:token token
                        :msg msg
                        ;; Carried so the write can persist it under its OWN
                        ;; durable key -- see `finish`.
                        :last-signed candidate
                        :signing-lock {:witness candidate :round (:locked-round st)
                                       :value-id (:locked-value-id st)}
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

(defn- proposal-for-value
  "The proposer's proposal at `r` carrying `vid`, whether or not it is the one
  we saw first.

  An equivocating proposer sends two; we keep the first under `:proposals` and
  any others under `:proposal-alts`. A rule that has a quorum in hand knows
  which value it needs, so it asks for that one rather than for whichever
  arrived first. The alternative is only ever consulted when a quorum has
  already named its value id, so this cannot be used to slip an unvoted
  proposal past a rule."
  [st r vid]
  (let [p (proposal-from-proposer st r)]
    (if (and p (= vid (value-id (:value p))))
      p
      (let [alt (get-in st [:proposal-alts r vid])]
        (when (and alt (= (:from alt) (proposer-at st r))) alt)))))

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
      ;;
      ;; The conflicting proposal is REPORTED and also KEPT, under its value
      ;; id. It used to be reported and discarded, which handed one equivocating
      ;; proposer a permanent halt: split the proposal so that a minority holds
      ;; `x` and a quorum holds `y`, and the minority node then sits on 2f+1
      ;; precommits for `y` with the proposal it needs one message away and no
      ;; way to accept it -- `rule-l49` matches on the proposal it happens to
      ;; hold. Measured: 7 validators, one faulty, well inside the f=2 budget;
      ;; five nodes committed 21 heights and the split node committed none,
      ;; frozen at height 0 round 1 holding a full quorum of precommits for the
      ;; value it could not adopt.
      ;;
      ;; CometBFT discards its held block the moment a 2/3 majority names a
      ;; different one and waits for the right one instead
      ;; (`state.go:2340-2350`, and `enterCommit`'s "commit is for a block we do
      ;; not know about" at `:1672-1692`). Keeping both is the same move made
      ;; cheaply: nothing is believed on the strength of being first, and the
      ;; rules ask for the value the quorum actually named.
      :else (-> (report-conflict st from :proposal r existing msg)
                (assoc-in [:proposal-alts r (value-id (:value msg))] msg)))))

(def ^:private max-future-heights 3)
(def ^:private max-future-messages 500)

(def ^:private max-future-rounds
  "How far past our own round a message may name before we drop it.

  The message log is keyed by round -- `[:proposals r from]`, `[:prevotes r ...]`
  -- and the keys were unbounded, so one validator sending votes at rounds
  1, 2, ... 10^9 allocated one map entry per round at a single height. Rounds
  advance only on timeouts, so no honest node is ever more than a handful ahead
  of the network; a bound costs nothing and closes the exhaustion vector.

  Chosen rather than derived: CometBFT's `HeightVoteSet` grows its round vote
  sets lazily and its `addRound` panics rather than allocating without limit
  (`types/height_vote_set.go`), so the reference bounds this too, just by a
  different mechanism."
  20)

(defn- well-formed?
  "Shape checks that need nothing but the message and our own round.

  A Byzantine peer may say anything, so a field is not trusted for being
  present. `vr` in particular: the paper's proposal carries `-1 <= vr < r`, and
  while L28's guard re-checks it at the point of USE, a proposal violating it
  has no meaning and should not be stored. L22's guard is only `(= -1 vr)`, so a
  `vr` of -7 would sit in the log looking like a valid-round claim to any future
  reader of that map."
  [st msg]
  (let [h (:height msg)
        r (:round msg)]
    (and (int? h) (not (neg? h))
         (int? r) (not (neg? r))
         ;; Bounded relative to where WE are, or -- for a future height, where
         ;; we will start -- relative to round 0.
         (<= r (+ (if (= h (:height st)) (:round st) 0) max-future-rounds))
         (or (not= :proposal (:type msg))
             (let [vr (:vr msg)]
               (and (int? vr) (<= -1 vr) (< vr r)))))))

(defn- record-message
  "File one authenticated message. Messages for the current height enter the
  log; a small window of future heights is buffered, everything else dropped."
  [st msg]
  (let [h (:height msg)]
    (cond
      (not (well-formed? st msg)) st

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

(declare answer-status record-catchup note-peer-height)

(defn- ingest
  "An authenticated message arrived from a peer.

  `verified-by` is the set of peer-ids whose signature was checked at the edge.
  We insist the claimed author is in it: a Byzantine node may say anything in
  its own name but may not forge another validator's identity, which is exactly
  the adversary the Ivy model assumes (`tendermint.ivy:379-383`)."
  [st from msg verified-by]
  (cond
    (not (contains? (or verified-by #{}) (:from msg)))
    (log-line st :warn (str (:id st) " dropping message whose author " (:from msg)
                            " was not verified (relayed by " from ")"))

    ;; Catch-up traffic is ABOUT heights we are not at, so it cannot go through
    ;; `record-message`, which drops anything below our height and buffers only
    ;; a small window above it. Both are still authenticated by the check above.
    (and (= :status (:type msg)) (nat-int? (:height msg)))
    (-> st
        (note-peer-height (:height msg))
        (answer-status (:from msg) (:height msg)))

    (= :catchup (:type msg))
    (record-catchup st (:from msg) msg)

    (not (contains? (set (:validators st)) (:from msg)))
    (log-line st :warn (str (:id st) " dropping message from non-validator " (:from msg)))

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

(def catchup-timer
  "Asking where everyone is, SEPARATELY from re-sending our own votes.

  These rode the same timer, and that made the gossip interval the catch-up
  rate: `answer-status` replies with exactly one height, so a lagging node
  gained one height per gossip interval and no faster.

  Measured on four validators over websockets, crash and restart, twenty
  seconds:

      :gossip-interval 12 (default)   gap 20 -> 40   never converges
      :gossip-interval  3             gap  7 ->  0   fully caught up

  Turning the gossip interval down fixes the lag and costs the whole vote
  retransmission at the same rate -- the payload of a `gossip` tick is every
  message we signed this round plus the last commit, while the payload of this
  one is `{:type :status :height h}`, about forty bytes.

  So they are two timers. CometBFT splits them for exactly this reason:
  peer-state broadcast (`reactor.go:516`/`:593`) is continuous and separate
  from `gossipVotesRoutine`.

  Armed ONLY while behind, so a healthy cluster pays nothing at all for it."
  ::catchup)

(defn- arm-catchup
  "Arm the catch-up poll if we have evidence we are behind, and not otherwise."
  [st]
  (if (and (:catchup-interval st)
           (> (:peer-height st 0) (:height st)))
    (emit st (node/set-timer catchup-timer (:catchup-interval st)))
    st))

(defn- note-peer-height
  "Remember the furthest height any peer has claimed, and start asking if that
  is ahead of us.

  A single number, not a map: we only ever ask 'is anyone ahead', and keeping
  it per-peer would be an unbounded map keyed by a value a peer chooses."
  [st h]
  (if (and (number? h) (> h (:peer-height st 0)))
    (-> st (assoc :peer-height h) arm-catchup)
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
  touches the double-sign guard.

  ## Which rounds, and why the obvious window was a permanent halt

  The window used to be the current and immediately preceding round only, on
  the stated grounds that \"older rounds cannot change any peer's decision that
  a newer round has not already settled\". That reasoning is WRONG, and the
  cost of it was a liveness failure on a perfect network.

  L28 lets a locked node prevote for a proposal whose POL round `vr` is at or
  above its own `locked-round`, and `vr` is chosen by the proposer -- it can sit
  arbitrarily far below the current round. Once the network is two rounds past
  `vr`, a node that missed the round-`vr` prevotes can never be sent them
  again, so it can never fire L28 for that proposal, and it prevotes nil
  forever.

  Measured on this codebase's own simulator: four validators, ZERO Byzantine
  nodes, zero crashes, no message loss. Two nodes held the round-0 POL for `V`
  and were locked on it; two had missed one round-0 prevote and were unlocked.
  After 5000 ticks the cluster was at round 25 and height 0, having decided
  nothing. When a locked node proposes, the unlocked ones cannot fire L28 (no
  POL) and cannot fire L22 (`vr` is not -1), so they prevote nil; when an
  unlocked node proposes a fresh value, the locked ones prevote nil. Two-two,
  forever.

  So the window also includes every round that is the POL round of a proposal
  we currently hold. That is the round whose prevotes somebody is, by
  construction, still trying to assemble.

  ## Why this re-sends only OUR OWN messages, which is weaker than CometBFT

  CometBFT relays OTHER validators' prevotes at `ProposalPOLRound`
  (`consensus/reactor.go` gossipVotesForHeight), and that is strictly stronger:
  it closes the case where the original prevoter has since crashed.

  urd cannot do that yet, and the reason is in `ingest`: a message is dropped
  unless its claimed author is in `verified-by`, which `auth/unseal` fills with
  the peer that SEALED the envelope. A relayed prevote therefore names an
  author the relayer's signature does not cover, and is refused -- correctly,
  since otherwise any peer could invent votes for anyone.

  Making relay work needs prevotes to carry their own attestation, the way
  precommits already do when a scheme is configured and the way round-robin's
  `record-vote` requires of every vote it accepts. That is a real gap and it is
  recorded as one; it is not this fix, because widening the window closes the
  measured halt on its own whenever the original prevoters are still up, which
  is the fault-free case the reproduction used."
  [st]
  (let [me (:id st)
        floor (max 0 (dec (:round st)))
        ;; The POL round of every proposal we hold. `vr` comes off the wire, so
        ;; it is checked rather than trusted: a non-integer or out-of-range
        ;; value must not widen the window, and a negative one means \"no POL\".
        pol-rounds (into #{}
                         (for [[_ by-sender] (:proposals st)
                               [_ m] by-sender
                               :let [vr (:vr m)]
                               :when (and (int? vr) (nat-int? vr) (< vr (:round st)))]
                           vr))
        wanted? (fn [r] (or (>= r floor) (contains? pol-rounds r)))
        mine (for [bucket [:proposals :prevotes :precommits]
                   [r by-sender] (get st bucket)
                   :when (wanted? r)
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
        ;; Announce where we are. CometBFT broadcasts (H,R,Step) continuously
        ;; (`reactor.go:516`/`:593`) and it is that peer-state, not the vote
        ;; gossip, which makes catch-up demand-driven instead of one-shot.
        ;; Without it a node more than ONE height behind had no trigger of any
        ;; kind: `:last-commit` covers the immediately preceding height only,
        ;; and it is overwritten the moment the network reaches h+2. Measured:
        ;; a node crashed at height 19 and restarted after the network reached
        ;; 66 advanced exactly one height and then froze, 117 behind, forever.
        (emit (node/broadcast :consensus {:type :status :from (:id st)
                                          :height (:height st)}))
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

(defn- signed?
  "Did `sign-and-broadcast` actually produce a signature?

  `:write-seq` advances only on the signing path, so this distinguishes a
  signature from a refusal without a second flag."
  [before after]
  (not= (:write-seq before) (:write-seq after)))

(defn- advance-step
  "Move to `step` only if the signature that justifies it was produced.

  `sign-and-broadcast`'s docstring says it refuses \"without changing the round
  state\", and that was true of the function and false of every call site: all
  four `(assoc :step ...)` ran unconditionally after it. A node that was
  refused therefore believed it had voted, and could not re-attempt the step,
  because the step guard now excluded the rule that would have done so."
  [before after step]
  (cond-> after (signed? before after) (assoc :step step)))

(defn- broadcast-prevote [st vid]
  (sign-and-broadcast st {:type :prevote :from (:id st)
                          :height (:height st) :round (:round st)
                          :value-id vid}))

(defn test-attestations
  "A toy vote-attestation scheme, for tests and simulations only.

  NOT CRYPTOGRAPHY -- a hash of the voter and the payload, so anyone reading
  this namespace can mint one for any voter. What it supplies is the SHAPE: an
  attestation binds a voter to a specific `[height round value-id]`,
  verification is a pure predicate, and anything not produced this way fails.
  That is what a test needs to drive the certificate guard down both branches.

  Unlike round-robin, `init` does NOT refuse to start without a scheme here --
  certificates are opt-in and their absence falls back to f+1 corroboration --
  so this stub is reachable by a caller who configures it. A deployment
  supplies real signatures."
  []
  (let [sign (fn [voter payload] (hasch/uuid [::test-vote voter payload]))]
    {:sign-vote sign
     :verify-vote (fn [voter payload att]
                    (and (some? att) (= att (sign voter payload))))}))

(defn vote-payload
  "What a precommit attestation covers: height, round and value id.

  All three, and none is optional. Without the HEIGHT a signature replays at
  every later height; without the ROUND it replays across rounds of the same
  height, where the same validator may legitimately precommit a different
  value; without the VALUE it attests to nothing at all. This is the same
  argument `auth/digest` makes about topic and recipient, one layer down."
  [h r vid]
  [h r vid])

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

(defn- valid?
  "`valid(v)` -- the application's predicate, plus one structural precondition.

  A value whose `id(v)` is nil is rejected unconditionally, before `:valid-fn`
  is consulted. In the paper, in `tendermint.ivy` (where `value.nil` is a
  distinguished constant) and in `TendermintAcc_004_draft.tla:56` (where
  `ValuesOrNil` is strictly larger than `Values`), nil lives OUTSIDE the value
  domain and is the sentinel for \"no value\". Here `value-id` maps both `nil`
  and `{:id nil}` onto the same nil, so without this check a proposal carrying a
  nil value is indistinguishable from a prevote-nil at every stage.

  What that cost, measured: one Byzantine proposer sending `:value nil` made
  every honest node prevote for it (L22 accepted it), then LOCK on nil (L36),
  then record `{height nil}` as a decision (L49) -- which the decision guards
  could not see, because they tested truthiness rather than membership, so L49
  refired until the rule fixpoint hit its iteration limit and threw. A
  one-validator denial of service, with three separate guards each blind to the
  single decision value that mattered.

  `:valid-fn` alone could not have caught it: it defaults to `(constantly true)`
  and was never configured anywhere in src, test or docs, so its false arm had
  never executed."
  [st v]
  (and (some? (value-id v))
       (boolean ((:valid-fn st) v))))

(defn- start-round [st r]
  (let [prev (:round st)
        st (-> st
               (cancel-round-timers (:height st) prev)
               (assoc :round r :step :propose :awaiting-value nil)
               ;; Armed for EVERYONE, proposer included.
               ;;
               ;; `enterPropose` schedules the propose timeout at the top,
               ;; before the `privValidator`/`isProposer` checks
               ;; (`state.go:1203-1204`), precisely so a proposer times itself
               ;; out too. Ours armed it only in the non-proposer branch, so a
               ;; proposer whose `request-value` never returned -- a stalled
               ;; application, a refused signature -- sat at `step :propose`
               ;; with no timer at all and could not leave the round on its own.
               ;; It was rescued only once f+1 peers reached a higher round,
               ;; which costs the whole network a full propose/prevote/precommit
               ;; cycle first: a local fault turned into a network-wide round.
               (arm-timer :propose r))]
    (if (= (:id st) (proposer-at st r))
      ;; L15-18: re-propose validValue if we have one, otherwise ask the
      ;; application. `getValue()` is synchronous in the paper and an EFFECT
      ;; here, so the proposal is finished by the `value-ready` event.
      (if-some [vv (:valid-value st)]
        (broadcast-proposal st vv (:valid-round st))
        (-> st
            (assoc :awaiting-value {:height (:height st) :round r})
            (emit (node/request-value {:height (:height st) :round r}))))
      ;; L21 -- the timer is already armed above, for proposer and
      ;; non-proposer alike.
      st)))

;; ============================================================
;; Height transition
;; ============================================================

(defn- trim-decisions
  "Bound `:decisions`, which grew one entry per height for the life of the
  process.

  It is the only unbounded structure left in this algorithm after
  `:catchup-claims` and `:proposal-alts`, and it is the awkward one, because it
  is not dead weight: `answer-status` serves it, so what we drop is exactly
  what we can no longer catch a lagging peer up on. Retention is therefore a
  policy and it is configurable, not a constant chosen here.

  The current height is always kept, whatever the retention -- several rules
  test `(contains? (:decisions st) (:height st))` and a node that forgot its
  own height's decision would re-propose it."
  [st]
  (if-let [keep-n (:decision-retention st)]
    (let [floor (- (:height st) keep-n)]
      (if (pos? floor)
        (-> st
            (update :decisions #(into {} (filter (fn [[h _]] (>= h floor))) %))
            ;; Same floor. A certificate for a height we can no longer serve
            ;; the decision for is dead weight, and keeping the two maps on
            ;; different floors would mean answering a peer with a certificate
            ;; and no decision to go with it.
            (update :certificates #(into {} (filter (fn [[h _]] (>= h floor))) %)))
        st))
    st))

(defn- activate-updates
  "Apply any validator updates carried by the decision at `h`.

  Returns `{:config m}` -- the keys to merge into state -- plus an optional log
  line. Returns an EMPTY config when there is nothing to do, so the common case
  costs one map lookup.

  A rejected update does NOT change the set, and says so at `:error`. That is a
  deterministic outcome of (config, updates) and nothing else, so every node
  reaches it identically: the network stalls on the offending value rather than
  splitting over it. CometBFT panics here; we log and continue with the old
  set, which is the same safety property with a better operational story.

  What must NOT happen is for two nodes to classify the same update
  differently. That is why `reconfig/validate` reads only the config being
  applied to -- etcd validated against whatever config happened to be active at
  propose time, and the resulting divergence between believed and actual config
  caused real data corruption in CockroachDB."
  [st h]
  (let [updates (:validator-updates (get (:decisions st) h))]
    (if-not (seq updates)
      {}
      (let [cfg {:validators (:validators st)
                 :powers (:powers st)
                 :priorities (:priorities st)}
            result (reconfig/apply-updates cfg updates)]
        (if (:error result)
          {:level :error
           :log (str (:id st) " REFUSING validator updates decided at height " h
                     ": " (pr-str result) " -- keeping the current set")}
          {:config (select-keys result [:validators :powers :priorities])
           :level :info
           :log (str (:id st) " validator set changes at height " (inc h)
                     ": " (pr-str (:validators result)))})))))

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
        ;; The set change ACTIVATES here, one height after the decision that
        ;; carried it.
        ;;
        ;; N=1, not CometBFT's +2, and the difference is structural rather than
        ;; a preference. Their first +1 is FORCED: a block header is built from
        ;; pre-execution state, so the result of deciding H cannot appear in H's
        ;; own header. urd has no header -- the decided value IS the value, and
        ;; every node that decided H holds the update the moment it decides.
        ;; Their second +1 buys pre-commitment so a light client can verify
        ;; ADJACENT headers by hash chain alone; urd's analogue is the commit
        ;; certificate, which is verified against the set for its own height.
        ;;
        ;; Safety at N=1: the update travels INSIDE the decided value, so
        ;; agreeing on the value is agreeing on the update. Every node that
        ;; decided H computes the same set for H+1, and votes at H were counted
        ;; under the set for H, which nothing here touches. There is no window
        ;; in which two sets are both live -- exactly one set per height, as in
        ;; CometBFT.
        ;;
        ;; If skipping verification is ever wanted (a verifier jumping many
        ;; heights rather than following each), this becomes +2 and the set for
        ;; H+1 has to be committed to at H. That is the only reason to pay for
        ;; the extra height.
        reconf (activate-updates st old-h)
        st (merge st (:config reconf))
        st (cond-> st (:log reconf) (log-line (:level reconf) (:log reconf)))
        st (-> st
               (cancel-round-timers old-h (:round st))
               (assoc :last-commit last-commit)
               (assoc :height new-h
                      ;; Claims are keyed by height and only ever consulted for
                      ;; the current one, so keeping older ones is pure growth.
                      :catchup-claims (select-keys (:catchup-claims st) [new-h])
                      :locked-value nil :locked-value-id nil :locked-round -1
                      :valid-value nil :valid-round -1
                      :proposals {} :prevotes {} :precommits {}
                      ;; Same lifetime as `:proposals`, and it was not in this
                      ;; list. `record-proposal` files every CONFLICTING
                      ;; proposal under `[round (value-id …)]` -- an
                      ;; attacker-chosen key, deduped for REPORTING by
                      ;; `:reported` but not for storage -- so it survived
                      ;; every height transition and grew without bound on one
                      ;; equivocating validator.
                      :proposal-alts {}
                      :done-l22 #{} :done-l28 #{}
                      :done-l34 #{} :done-l36 #{} :done-l44 #{} :done-l47 #{}
                      :reported #{}
                      :awaiting-value nil)
               (assoc :priorities (proposer/advance (:priorities st) (:powers st)))
               (update :future dissoc new-h)
               trim-decisions)
        st (reduce record-message st (filter #(contains? (:powers st) (:from %)) buffered))]
    (start-round st 0)))

(declare corroborated? decide valid-certificate?)

(defn- record-catchup
  "Note a peer's claim about a height we have not reached, and adopt it once
  enough peers agree. See `corroborated?` for why f+1 is the threshold."
  [st from {:keys [height decision cert]}]
  (if (or (not= height (:height st))
          (contains? (:decisions st) height)
          (not (valid? st decision)))
    st
    ;; A VERIFIED certificate is evidence, so one peer is enough and no claim
    ;; needs to be recorded at all. Checked before the claim is filed, because
    ;; filing it first would let a peer that supplies a good certificate also
    ;; contribute a corroboration claim -- harmless here, but the two paths
    ;; should not be able to reinforce each other.
    (cond
      (valid-certificate? st cert height (value-id decision))
      (-> st
          (log-line :info (str (:id st) " catching up to height " height
                               " on a verified commit certificate"))
          (assoc-in [:certificates height] cert)
          (decide (:round st) decision))
      (not (contains? (set (:validators st)) from)) st

      :else
      (let [st (assoc-in st [:catchup-claims height from] decision)]
        (if (corroborated? st height decision)
          (-> st
              (log-line :info (str (:id st) " catching up to height " height
                                   " on f+1 corroborated claims"))
            ;; `decide` writes the durable end-height marker and gates the
            ;; `commit` on it, exactly as the normal path does; the height
            ;; advances when that write lands. A catch-up decision must be as
            ;; durable as one we reached ourselves.
              (decide (:round st) decision))
          st)))))

(defn- answer-status
  "A peer told us where it is. If we are ahead and hold its height's decision,
  send it.

  CometBFT serves this from the block store -- `reactor.go:907-937`, \"if peer
  is lagging by more than 1, send Commit\" -- at any lag down to
  `blockStoreBase`."
  [st from h]
  (if-some [v (when (< h (:height st)) (get (:decisions st) h))]
    (emit st (node/send-to from
                           (cond-> {:type :catchup :from (:id st)
                                    :height h :decision v}
                             ;; When we hold one. A peer that can verify it
                             ;; needs no second opinion; one that cannot ignores
                             ;; the field and waits for f+1 claims as before.
                             (get (:certificates st) h)
                             (assoc :cert (get (:certificates st) h)))))
    st))

(defn- corroborated?
  "Have f+1 DISTINCT peers claimed the same decision for this height?

  This is what makes catch-up safe without relaying signatures. Our ingest
  authenticates the sender of a message and nothing else (`well-formed?`), so a
  peer cannot vouch for another peer's precommits -- forwarding a commit proof
  would mean trusting the forwarder. f+1 distinct claims contains at least one
  honest node, and an honest node only ever claims a value it decided, so the
  claim is true. It costs one extra round trip against CometBFT's single
  authenticated Commit, and needs no new cryptography."
  [st h decision]
  (let [claims (get-in st [:catchup-claims h] {})
        agreeing (keep (fn [[peer claimed]] (when (= decision claimed) peer))
                       claims)]
    (node/v-blocking? (:membership st) st
                      (map (fn [p] {:from p}) agreeing)
                      (constantly true))))

(defn commit-certificate
  "The 2f+1 precommits that decided `vid` at `[h r]`, as a relayable value.

  This is what `corroborated?` exists to work around. Our ingest authenticates
  the SENDER of a message and nothing else, so a forwarded precommit is a claim
  by the forwarder -- which is why catch-up needs f+1 DISTINCT peers to say the
  same thing independently before it can be believed. A certificate carries the
  voters' own attestations, so one peer's answer is evidence rather than
  hearsay, and the reply is verifiable by anyone holding the validator set.

  Returns nil when no signing scheme is configured, which keeps the whole
  feature opt-in and leaves the f+1 path exactly as it was."
  [st r vid]
  (when (:sign-vote st)
    (let [votes (->> (get-in st [:precommits r] {})
                     (keep (fn [[voter m]]
                             (when (and (= vid (:value-id m)) (:att m))
                               [voter (:att m)])))
                     (into {}))]
      (let [cert {:height (:height st) :round r :value-id vid :votes votes}]
        (when (valid-certificate? st cert (:height st) vid)
          cert)))))

(defn valid-certificate?
  "Does `cert` prove that 2f+1 of OUR validators precommitted `vid` at `[h r]`?

  TWO checks carry the weight, and both were mutation-verified:

    - every attestation VERIFIES over `vote-payload`, which binds the height,
      the round and the value id. This is the whole security of the thing.
    - the voters are counted by WEIGHT through the same `membership` the live
      path uses, not by counting entries. `distinct-voters` means one validator
      repeated cannot clear a threshold by itself.

  The rest is defence in depth, and is labelled as such because mutation says
  so rather than because it feels weaker. Skipping the `(= h (:height cert))`
  and `(= vid (:value-id cert))` comparisons changes NO test outcome, and the
  reason is the payload binding above: a certificate for another height or
  another value carries signatures over that height and that value, so
  verification fails on its own. They stay because a cheap explicit comparison
  documents the intent and would keep holding if the payload ever narrowed --
  not because they are currently stopping anything.

  The `(contains? vset voter)` filter is the same: `weight` returns nothing for
  a peer outside `:powers`, so padding a certificate with invented voters
  already fails the threshold.

  Returns false rather than throwing on anything malformed: this arrives from
  the network and a malformed certificate is a packet, not an error."
  [st cert h vid]
  (boolean
   (and (some? vid)
        (map? cert)
        (nat-int? (:round cert))
        (:verify-vote st)
        (= h (:height cert))
        (= vid (:value-id cert))
        (map? (:votes cert))
        (let [vset (set (:validators st))
              r (:round cert)
              good (->> (:votes cert)
                        (keep (fn [[voter att]]
                                (when (and (contains? vset voter)
                                           (try (true? ((:verify-vote st) voter
                                                                          (vote-payload h r vid) att))
                                                (catch #?(:clj Exception :cljs :default) _ false)))
                                  {:from voter})))
                        vec)]
          (true? (node/quorum? (:membership st) st good (constantly true)))))))

(defn- decide
  "L49-54. The decision itself is durable: the end-height marker is CometBFT's
  one non-signed WAL barrier, and the `commit` effect rides in its `:then`, so
  no node can be observed to have decided a value it might forget."
  [st r v]
  (let [h (:height st)
        token [:end-height h]
        cert (or (get-in st [:certificates h]) (commit-certificate st r (value-id v)))]
    (-> st
        (assoc-in [:decisions h] v)
        (cond-> cert (assoc-in [:certificates h] cert))
        (assoc-in [:pending-end-height token] h)
        (log-line :info (str (:id st) " decided " (value-id v)
                             " at height " h " round " r))
        (update-in [:fx :signed] conj
                   {:token token
                    :msg (cond-> {:type :end-height :height h :decision v}
                           cert (assoc :certificate cert))
                    :epoch [h r]
                    :then [(node/commit [v])]}))))

;; ============================================================
;; The upon-rules
;;
;; Each returns nil when it does not fire, or the new state when it does.
;; `apply-rules` runs the first that fires; `run-rules` iterates to a fixpoint,
;; which is required -- one arriving precommit can complete a quorum that both
;; arms the L47 timer and satisfies L49.
;; ============================================================

(defn- rule-l22
  "L22-27: a proposal with vr = -1 while still in propose.

  Latched by round, and the latch is not redundant with the step guard.

  On the happy path `advance-step` moves the step off `:propose` and the guard
  above stops the rule re-firing. But `advance-step` deliberately does NOT move
  it when `sign-and-broadcast` REFUSES -- the double-sign guard said no. The
  rule then returns a state differing from its input only by a log line,
  `apply-rules` reports `fired? true`, and `run-rules` spins to
  `max-rule-iterations` and THROWS, killing the node.

  That is reachable exactly in the fault `the-sign-guard-outlives-the-wal`
  exists for: wipe the WAL, keep the durable registers, and `replay` yields
  round 0 / step `:propose` while `:last-signed` comes back from its own
  register at a later round. Sweeping the crash tick over a restart scenario
  hit it in 14 of 55 timings; the existing test survives because tick 14
  happens not to be one of them.

  With the latch a refusal costs a ROUND -- the node sits out this one and
  escapes via the propose timeout or L55 -- rather than costing the process.
  L34, L36, L44 and L47 all latch for the same reason."
  [st]
  (when (= :propose (:step st))
    (let [r (:round st)
          p (proposal-from-proposer st r)]
      (when (and p (= -1 (:vr p)) (not (contains? (:done-l22 st) r)))
        (let [v (:value p)
              vid (value-id v)
              st (update st :done-l22 (fnil conj #{}) r)]
          (advance-step st
                        (broadcast-prevote
                         st
                         (if (and (valid? st v)
                                  (or (= -1 (:locked-round st))
                                      (= (:locked-value-id st) vid)))
                           vid
                           nil))
                        :prevote))))))

(defn- rule-l28
  "L28-33: a proposal that carries a valid-round, backed by 2f+1 prevotes AT
  THAT ROUND.

  Two traps live here. The prevote quorum is at `vr`, not at the current round.
  And the unlock condition is `lockedRound <= vr` -- less-than-or-EQUAL. With
  `<` a node locked at exactly `vr` would prevote nil for the very value it is
  locked on, and the algorithm would lose liveness in the case the rule exists
  to handle.

  Latched by round for the reason `rule-l22` gives at length: a refused
  signature leaves the step at `:propose`, and without a latch the rule
  re-fires until `run-rules` throws."
  [st]
  (when (= :propose (:step st))
    (let [r (:round st)
          p (proposal-from-proposer st r)]
      (when (and p (<= 0 (:vr p)) (< (:vr p) r)
                 (not (contains? (:done-l28 st) r)))
        (let [vr (:vr p)
              v (:value p)
              vid (value-id v)]
          (when (quorum-for? st :prevotes vr vid)
            ;; Rebound BEFORE the broadcast, so both sides of `advance-step`
            ;; carry the latch. Latching only the `before` argument would lose
            ;; it: `advance-step` returns the `after` state.
            (let [st (update st :done-l28 (fnil conj #{}) r)]
              (advance-step st
                            (broadcast-prevote
                             st
                             (if (and (valid? st v)
                                      (or (<= (:locked-round st) vr)
                                          (= (:locked-value-id st) vid)))
                               vid
                               nil))
                            :prevote))))))))

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
            (as-> s (let [s (assoc s :locked-value v :locked-value-id vid
                                   :locked-round r)]
                      (advance-step s (broadcast-precommit s vid) :precommit)))

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
      (let [s (update st :done-l44 conj r)]
        (advance-step s (broadcast-precommit s nil) :precommit)))))

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
  ;; `contains?`, not truthiness. A decision whose VALUE is nil is still a
  ;; decision, and a truthiness test cannot see one -- which let a nil-valued
  ;; proposal decide invisibly and refire this rule until the fixpoint threw.
  (when-not (contains? (:decisions st) (:height st))
    (some (fn [r]
            ;; Driven by the QUORUM's value rather than by the proposal we
            ;; happen to hold: find the value id that 2f+1 precommitted, then
            ;; ask for the proposal carrying it.
            (some (fn [vid]
                    (when (and (some? vid) (quorum-for? st :precommits r vid))
                      (when-let [p (proposal-for-value st r vid)]
                        (when (valid? st (:value p))
                          (decide st r (:value p))))))
                  (distinct (keep :value-id (vals (get-in st [:precommits r]))))))
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
  (if (contains? (:decisions st) (:height st))
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

    ;; Only `:status`, and only while behind. This is the catch-up rate.
    (= catchup-timer timer-id)
    (-> st
        (emit (node/broadcast :consensus {:type :status :from (:id st)
                                          :height (:height st)}))
        arm-catchup)

    (not (and (vector? timer-id) (= 3 (count timer-id)))) st

    ;; We have decided this height and are waiting for the end-height marker to
    ;; land. The paper increments the height in the same atomic step as the
    ;; decision, so no round timer may fire in the gap our durability barrier
    ;; opens -- otherwise a node could start, and PROPOSE at, a round of a
    ;; height it has already finished.
    (contains? (:decisions st) (:height st)) st

    :else
    (let [[kind h r] timer-id]
      (if-not (and (= h (:height st)) (= r (:round st)))
        ;; A timer from a round or height we have left. Not an error: rounds
        ;; are abandoned all the time.
        st
        (case kind
          ;; L57-60
          :propose (if (= :propose (:step st))
                     (advance-step st (broadcast-prevote st nil) :prevote)
                     st)
          ;; L61-64
          :prevote (if (= :prevote (:step st))
                     (advance-step st (broadcast-precommit st nil) :precommit)
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
  [st v context]
  (let [{:keys [height round]} (:awaiting-value st)]
    (if (and height
             (or (nil? context) (= context (:awaiting-value st)))
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
        ;; At most one `:end-height` can be signed in a step, so this is the
        ;; height being closed, if any.
        end-h (some (fn [{m :msg}] (when (= :end-height (:type m)) (:height m)))
                    signed)
        retention (:wal-retention st)
        cp? (boolean (and end-h retention
                          (>= (- end-h (:checkpointed-through st 0)) retention)))
        ;; Save the activated set and its priorities *before* the normal
        ;; next-height proposer increment. Restore applies that increment once.
        boundary (when (some? end-h)
                   (merge (select-keys st [:validators :powers :priorities])
                          (:config (activate-updates st end-h))
                          {:decided-through end-h :post-activation? true}))
        cp-writes (when cp?
                    (cond-> (assoc boundary
                                   :decisions (:decisions st)
                                   :last-commit (own-messages-at-height st))
                      (seq (:certificates st)) (assoc :certificates (:certificates st))
                      (:last-signed st) (assoc :last-signed (:last-signed st))))
        st (cond-> st cp? (assoc :checkpointed-through end-h))
        persists (mapv (fn [{:keys [token msg epoch then last-signed signing-lock]}]
                         (let [end? (= :end-height (:type msg))
                               writes (cond-> {:wal msg}
                                        last-signed (assoc :last-signed last-signed :signing-lock signing-lock)
                                        end? (merge boundary))]
                           (node/persist-then
                            (cond-> {:writes writes :durable? true
                                     :epoch epoch :token token :then then}
                              (and cp? end?)
                              (assoc :checkpoint [{:writes cp-writes :durable? true}])))))
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
        (cond-> (:certificate msg) (assoc-in [:certificates (:height msg)] (:certificate msg)))
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
            (cond
              (:wal w) (replay-one acc (:wal w))
              (contains? w :decided-through)
              (assoc acc :height (inc (:decided-through w))
                     :checkpointed-through (:decided-through w))
              :else acc))
          acc
          (or writes [])))

(defn- later-signed
  "The strictly greater of two `{:height :round :step}` records, nil-safe.

  Restore takes this over the WAL-derived value and the durable register, so
  neither substrate can move the guard BACKWARDS. That direction matters: the
  guard is only ever allowed to advance."
  [a b]
  (cond
    (nil? a) b
    (nil? b) a
    (signing/may-sign? b a) b
    :else a))

;; ============================================================
;; The Node implementation
;; ============================================================

(defn- restored-boundary
  "Upgrade the validator state of a legacy boundary using its original record."
  [{:keys [durable writes]}]
  (let [boundary (some (fn [{w :writes}] (when (contains? w :decided-through) w))
                       (rseq (vec writes)))]
    (cond
      (:post-activation? durable) durable

      ;; Legacy checkpoints captured the entire pre-activation configuration.
      (and boundary (:decisions boundary) (nil? (:wal boundary)))
      (merge durable (:config (activate-updates boundary (:decided-through boundary))))

      ;; Legacy ordinary writes stored the new members but old priorities.
      (and (:priorities durable) (:powers durable) (:validators durable))
      (let [{:keys [priorities powers validators]} durable
            joining (remove #(contains? priorities %) validators)
            penalty (proposer/new-validator-priority (proposer/total-power powers))]
        (assoc durable :priorities (merge (select-keys priorities validators)
                                          (zipmap joining (repeat penalty)))))

      :else durable)))

(defn- check-recovery-membership [durable replayed height]
  (when (pos? height)
    (let [{:keys [validators powers priorities]} durable
          ids (set validators)
          complete? (and (= (dec height) (:decided-through durable))
                         (seq ids) (= (count ids) (count validators))
                         (= ids (set (keys powers)) (set (keys priorities)))
                         (every? #(and (int? %) (pos? %) (<= % reconfig/max-total-power)) (vals powers))
                         (<= (reduce + (vals powers)) reconfig/max-total-power)
                         (every? int? (vals priorities)))
          ;; Old unreconfigured WALs can establish the genesis schedule by replay.
          decisions (:decisions replayed)
          legacy-history? (and (= height (count decisions))
                               (every? #(and (nat-int? %) (< % height)) (keys decisions))
                               (not-any? #(seq (:validator-updates %)) (vals decisions)))]
      (when-not (or complete?
                    (and (not (or validators powers priorities)) legacy-history?))
        (throw (ex-info "Tendermint needs a height-matched validator checkpoint"
                        {:consensus-height height}))))))

(defn- replay-delivery [st delivered]
  (when (and (some? delivered) (not (nat-int? delivered)))
    (throw (ex-info "Tendermint :delivered-through must be a non-negative integer"
                    {:delivered-through delivered})))
  (if (and (some? delivered) (< delivered (:height st)))
    (let [vertices (mapv (fn [h]
                           (if (contains? (:decisions st) h)
                             (get (:decisions st) h)
                             (throw (ex-info "Tendermint decision needed for application replay is unavailable"
                                             {:height h :delivered-through delivered
                                              :consensus-height (:height st)}))))
                         (range delivered (:height st)))]
      (emit st (node/commit vertices)))
    st))

(def default-config
  {:timeout-propose 10
   :timeout-prevote 8
   :timeout-precommit 8
   :timeout-delta 2
   ;; Ticks between retransmissions of our own signed messages. `nil` turns
   ;; retransmission off, which is the literal paper and is only live on a
   ;; perfectly reliable network -- see `gossip`.
   :gossip-interval 12
   ;; The catch-up poll, armed only while behind. Much shorter than the
   ;; gossip interval because its payload is one tiny message, and because it
   ;; IS the rate at which a lagging node returns.
   :catchup-interval 3
   ;; How many decided heights to retain. This is what `answer-status` can
   ;; serve a lagging peer from, so it is a retention POLICY, not a cache
   ;; size: a peer further behind than this cannot be caught up by us. `nil`
   ;; keeps everything, which is the old behaviour and an unbounded one.
   :decision-retention 1000
   ;; How many decided heights of WAL to keep before rewriting it.
   ;;
   ;; The WAL is append-only and every signed message goes in it, so without
   ;; this a node that has been up for a week replays a week of votes to reach
   ;; a state it could have written down in one record. `:decision-retention`
   ;; bounds MEMORY; this bounds the store, and they are independent -- a node
   ;; can hold a thousand decisions in RAM while replaying a million WAL
   ;; entries to get them.
   ;;
   ;; Checkpoints are taken only at `:end-height`, which is not a tuning
   ;; choice: it is the only boundary where a truncated WAL loses nothing.
   ;; Mid-height, the WAL holds this node's own votes for a height still in
   ;; progress, and `init` replays them back into its tallies -- dropping them
   ;; would make the node forget how it voted at a height it can still be asked
   ;; about. CometBFT truncates at `#ENDHEIGHT` for the same reason.
   :wal-retention 100})

(defrecord Tendermint []
  node/Node

  (capabilities [_]
    ;; Byzantine fault tolerant and absolutely final below n/3. Emits
    ;; `:report-equivocation` because a conflicting vote is evidence, not just a
    ;; message to drop.
    ;; `:send` is here for catch-up only: a peer that announced a height below
    ;; ours is answered directly rather than by broadcasting a decision the
    ;; rest of the network already has.
    {:emits #{:broadcast :send :persist-then :set-timer :cancel-timer
              :request-value :commit :report-equivocation :log}
     :topics #{:consensus}})

  (init [_ config]
    (let [cfg (assoc-in (merge default-config config) [:restored :durable]
                        (restored-boundary (:restored config)))
          ;; The DURABLE set wins over the configured one.
          ;;
          ;; Once a decided value can change the validator set, the set is state
          ;; rather than configuration: a restart that read it from the config
          ;; file would silently revert every change the network had agreed, and
          ;; the node would then count quorums over a set nobody else has. The
          ;; config remains the genesis value, used when nothing is stored.
          ;;
          ;; Still routed through `node/validator-set`, which refuses an empty
          ;; or duplicated set -- a durable value deserves the same check as a
          ;; configured one, and more so, since it arrived over the network.
          stored-validators (get-in cfg [:restored :durable :validators])
          validators (node/validator-set
                      (cond-> cfg stored-validators (assoc :validators stored-validators)))
          powers (or (get-in cfg [:restored :durable :powers])
                     (:powers cfg)
                     (into {} (map (fn [v] [v 1])) validators))
          base {:id (:peer-id cfg)
                :validators validators
                :powers powers
                :membership (or (:membership cfg) power-weighted-bft)
                :valid-fn (or (:valid-fn cfg) (constantly true))
                ;; OPTIONAL, unlike round-robin's, which are required. Absent,
                ;; precommits carry no attestation, no certificate is ever
                ;; assembled, and catch-up falls back to f+1 corroboration --
                ;; which is exactly what this algorithm did before. Making them
                ;; required would break every existing caller to buy a feature
                ;; none of them asked for.
                :sign-vote (:sign-vote cfg)
                :verify-vote (:verify-vote cfg)
                :height 0
                :round 0
                :step :propose
                :decisions {}
                ;; Bounded with `:decisions`, by the same retention: a
                ;; certificate is only useful for a height we can still serve,
                ;; and an unbounded map of them is the growth `:decisions` was
                ;; already fixed for.
                :certificates {}
                :locked-value nil
                :locked-value-id nil
                :locked-round -1
                :valid-value nil
                :valid-round -1
                :proposals {}
                :prevotes {}
                :precommits {}
                :done-l22 #{}
                :done-l28 #{}
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
                :gossip-interval (:gossip-interval cfg)
                :catchup-interval (:catchup-interval cfg)
                :decision-retention (:decision-retention cfg)
                :wal-retention (:wal-retention cfg)
                :checkpointed-through 0
                :peer-height 0}
          ;; Seeded from the durable registers BEFORE the WAL is replayed, so
          ;; a checkpoint that replaced the WAL still restores what the WAL
          ;; used to carry. Both are last-write-wins keys, so a later WAL
          ;; `:end-height` replayed on top overrides them, which is the right
          ;; precedence: the WAL is more recent than the checkpoint that
          ;; truncated it.
          base (cond-> base
                 (get-in cfg [:restored :durable :certificates])
                 (assoc :certificates (get-in cfg [:restored :durable :certificates]))
                 (get-in cfg [:restored :durable :decisions])
                 (assoc :decisions (get-in cfg [:restored :durable :decisions]))
                 (get-in cfg [:restored :durable :last-commit])
                 (assoc :last-commit (get-in cfg [:restored :durable :last-commit])))
          replayed (replay base (get-in cfg [:restored :writes]))
          ;; The double-sign guard is restored from its OWN durable register --
          ;; `:restored :durable` is the last-write-wins merge of landed writes,
          ;; which is exactly the semantics of CometBFT's atomically rewritten
          ;; `FilePVLastSignState` file (`privval/file.go:74-83`). The
          ;; WAL-derived value is kept only as a floor: whichever of the two is
          ;; further along wins, so the guard survives a truncated WAL and
          ;; equally survives a lost register.
          restored (update replayed :last-signed
                           later-signed (get-in cfg [:restored :durable :last-signed]))
          boundary-height (some-> (get-in cfg [:restored :durable :decided-through]) inc)
          history-height (max (or boundary-height 0) (:height replayed))
          delivered (:delivered-through cfg)
          ;; A ledger count does not identify the validators or priority schedule.
          ;; State transfer must install the matching consensus boundary as well.
          _ (when (and (nat-int? delivered) (> delivered history-height))
              (throw (ex-info "Tendermint needs a height-matched validator checkpoint for state sync"
                              {:delivered-through delivered :consensus-height history-height})))
          _ (check-recovery-membership (get-in cfg [:restored :durable]) replayed history-height)
          resume boundary-height
          restored (assoc restored :height history-height)
          witness (:last-signed restored)
          lock-register (get-in cfg [:restored :durable :signing-lock])
          restored (cond
                     (or (nil? witness) (< (:height witness) history-height)) restored
                     (and (= history-height (:height witness))
                          (= witness (:witness lock-register))
                          (int? (:round lock-register))
                          (<= -1 (:round lock-register) (:round witness))
                          (= (= -1 (:round lock-register)) (nil? (:value-id lock-register))))
                     (assoc restored :locked-round (:round lock-register)
                            :locked-value-id (:value-id lock-register))
                     (not= witness (:last-signed replayed))
                     (assoc restored :voting-blocked-through (:height witness))
                     :else restored)
          ;; Proposer priorities: READ BACK, not replayed from genesis.
          ;;
          ;; This used to be `(reduce advance p0 (range height))` -- one advance
          ;; per height, every restart. Two things were wrong with it:
          ;;
          ;; COST. It is O(height). CometBFT has the same shape in
          ;; `LoadValidators` and measured up to 903x slowdown at 100k heights
          ;; past a checkpoint, which is why they added one.
          ;;
          ;; CORRECTNESS, and this is the one that matters. The replay uses
          ;; TODAY's `powers` for every historical height. That is right only
          ;; while powers never change. Measured, with powers changing at
          ;; height 5 of 10:
          ;;
          ;;     truth (5 at old powers, then 5 at new):  {:a 3, :b -3, :c 0}
          ;;     replayed (10 at current powers):         {:a 1, :b -4, :c 3}
          ;;
          ;; A restarted node would compute a different proposer schedule than
          ;; one that stayed up -- a fork caused by restarting, and invisible
          ;; until validator powers can change. It also cannot work at all for
          ;; a state-synced joiner, which has no history to replay.
          ;;
          ;; The stored value is as of `:decided-through`, the same height that
          ;; register names, so both are advanced by exactly one to reach the
          ;; height we resume at. Keeping the two on one height is deliberate:
          ;; off-by-ones around this offset are the single largest bug cluster
          ;; in CometBFT's history -- the same error in six subsystems.
          stored-priorities (get-in cfg [:restored :durable :priorities])
          st (assoc restored :priorities
                    (cond
                      ;; Stored, and we are resuming past the height it names.
                      (and stored-priorities resume)
                      (proposer/advance stored-priorities powers)

                      stored-priorities stored-priorities

                      ;; No stored value: replay, as before. Correct for a
                      ;; static power set and the only option for a log written
                      ;; before this key existed.
                      :else
                      (reduce (fn [p _] (proposer/advance p powers))
                              (:priorities restored)
                              (range (:height restored)))))
          own (:own-messages st)
          st (assoc st :own-messages [])
          st (fresh-fx st)
          st (replay-delivery st (:delivered-through cfg))
          st (trim-decisions st)
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
               (cond
                 (not= :propose (:step st)) st

                 ;; CRASHED BEFORE PROPOSING, and it is our turn. Arming the
                 ;; propose timer here -- which is what this did -- makes the
                 ;; node wait for a proposal from ITSELF. Nobody else proposes
                 ;; at this round, so the timer expires, everyone prevotes nil,
                 ;; and the round is spent. One round per crash of a proposer,
                 ;; every time.
                 ;;
                 ;; The guard is our own proposal being absent from the log:
                 ;; `replay-one` sets step to `:propose` both for a node that
                 ;; never proposed and for one that proposed and crashed, and
                 ;; those need opposite handling. A node that DID propose has
                 ;; its own message replayed into `:proposals`, and re-proposing
                 ;; would be refused by the double-sign guard anyway -- but it
                 ;; would also skip arming the timer, so it is checked rather
                 ;; than left to the refusal.
                 (and (= (:id st) (proposer-at st (:round st)))
                      (nil? (get-in st [:proposals (:round st) (:id st)])))
                 (start-round st (:round st))

                 :else (arm-timer st :propose (:round st))))
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
          :value-ready (handle-value-ready st (:value input) (:context input))
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
