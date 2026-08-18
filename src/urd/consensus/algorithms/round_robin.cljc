(ns urd.consensus.algorithms.round-robin
  "Round-robin consensus: a rotating single proposer with majority voting, on
  urd's core protocol.

  The simplest thing that is still consensus, and it is in the portfolio for two
  reasons. It is the reference the datahike writer path was first built against,
  and it is the CRASH-fault-tolerant corner: fixed proposer per height, no
  locking, no equivocation handling.

  Proposer selection rotates by HEIGHT, not by round:

    height 0 -> validator 0 proposes
    height 1 -> validator 1
    ...

  Each height: the proposer broadcasts, validators vote if the proposal is
  valid, a majority finalizes, and a timeout bumps the round and retries.

  ## Ported from the legacy `ConsensusAlgorithm` protocol

  This used to sit on `urd.consensus.state-machine`, an earlier version of
  `node` -- same idea, its docstring even says so: transitions are pure
  functions from (state, event) to state plus effects. Two protocols for one
  concept is one too many, so this moved and `state-machine` went.

  Four things changed in the move, and each was a defect rather than a
  translation:

  1. **The transitions were not pure.** `handle-proposal-received` and
     `handle-proposal-ready` called `println` -- I/O inside `step`, which rule 1
     of the core protocol forbids, and which is why the legacy runtime's test
     output was full of interleaved debug lines from concurrent validators.
     Those are `log` effects now, which is what the effect exists for.

  2. **Timeouts were in MILLISECONDS.** The legacy runtime interpreted
     `set-timer` with `:duration-ms` against a wall clock. Logical ticks are
     what make a failing schedule reproducible, and half the repository did not
     have them; the flakiness of the legacy tests under load traces to exactly
     this.

  3. **`:add-own-vote` was an effect**, so a node's own vote was written to a log
     by the runtime rather than held in the node's own state. The algorithm now
     records it directly, which is both simpler and the only version that can
     be reasoned about locally -- a vote that lives outside the state machine is
     a vote the state machine cannot count.

  4. **The effect vocabulary was this algorithm's, generalised by accident.**
     `request-missing-proposal`, `request-state-sync`, `request-votes`,
     `broadcast-finalization` and `trigger-next-round` were all interpreted by a
     runtime that called itself generic. They are ordinary messages and a timer,
     and they are spelled that way now."
  (:require [urd.consensus.node :as n]
            [urd.consensus.reconfig :as reconfig]
            [hasch.core :as hasch]))

;; ============================================================
;; Helpers -- pure, and unchanged by the port
;; ============================================================

(def max-vote-bundle
  "Ceiling on a relayed vote collection before the message is refused outright.

  `handle-vote-bundle` already dedups by voter and truncates to the validator
  count, so this is not what bounds the WORK. It bounds what has to be held to
  do the truncating: a 50,000-element vector still gets allocated, walked and
  reduced before the bound applies. Refusing it at the edge costs one `count`."
  10000)

(defn well-formed?
  "Shape checks that need nothing but the message itself.

  Authentication says WHO sent a message. It says nothing about whether the
  fields inside it mean anything, and a Byzantine peer is authenticated too --
  so every field here is one an authenticated peer may choose freely.

  The TYPE checks are the load-bearing half. `get-proposer-id` computes
  `(mod height (count validators))` and `nth`s the result, so a height that is
  a string throws inside `step`. The runtime's containment turns that into a
  dropped message and a counter, which is survivable -- but containment is the
  wrong layer to lean on for something `int?` answers, and a contained throw
  costs a stack unwind per message where a predicate costs nothing.

  The NON-NEGATIVE half is defence in depth, and is documented as such because
  the obvious justification for it is false. `(mod -1 3)` is 2 in Clojure --
  `mod` is floored, not truncated -- so a negative height selects a valid
  proposer rather than indexing backwards or throwing, and it is dropped by the
  height comparison before that anyway. `answer-state-sync`'s `(>= h from)`
  with a negative `from` selects everything it holds, which retention already
  bounds. No reachable harm was found; the check stays because a negative
  height is meaningless and cheap to refuse, not because it is known to stop
  anything. Mutation-verified as NOT load-bearing today, which is the honest
  status rather than an assumed one.

  NOT bounded relative to our own height, deliberately. A node at 0 hearing a
  finalization for height 500 is the catch-up path working, not an attack, and
  a bound tight enough to matter here would refuse exactly the messages a
  lagging node needs. What an absurd height actually costs is one throttled
  sync request -- `:sync-requested-at` -- which is already bounded."
  [msg]
  (let [h (:height msg)
        r (:round msg)
        nat? (fn [x] (and (int? x) (not (neg? x))))]
    (and
     (keyword? (:kind msg))
     (or (nil? h) (nat? h))
     (or (nil? r) (nat? r))
     (case (:kind msg)
       :vote (some? (:proposal-id msg))
       (:vote-bundle :catchup)
       (let [v (:votes msg)]
         (or (nil? v) (and (coll? v) (<= (count v) max-vote-bundle))))
       :state-sync-response
       (and (or (nil? (:finalized msg)) (map? (:finalized msg)))
            (or (nil? (:oldest msg)) (nat? (:oldest msg)))
            (or (nil? (:current-height msg)) (nat? (:current-height msg))))
       ;; `:from` here is the REQUESTER'S HEIGHT, not a peer id -- the sender
       ;; is `(:from input)`, which the transport supplies and the message
       ;; cannot forge. `answer-state-sync` does arithmetic on this one.
       :state-sync (or (nil? (:from msg)) (nat? (:from msg)))
       true))))

(defn get-proposer-id
  "Which validator proposes at `height`.

  Rotates by height, not round. Ids are sorted so every node computes the same
  answer without coordinating."
  [height validator-set]
  (let [validator-ids (vec (sort (keys validator-set)))]
    (nth validator-ids (mod height (count validator-ids)))))

(defn am-proposer? [state]
  (= (get-proposer-id (:height state) (:validator-set state)) (:peer-id state)))

(defn quorum-size
  "CRASH-fault-tolerant quorum: a simple majority, floor(n/2) + 1.

  This is deliberately NOT the Byzantine threshold, and the difference is not an
  oversight -- read before 'fixing' it to match the certificate threshold.

  Round-robin is a CFT reference algorithm. It has a fixed proposer per height,
  no locking, and no equivocation handling, so it is not Byzantine-safe at ANY
  threshold: a faulty proposer can equivocate and nothing here detects it.
  Raising the threshold would cost liveness while buying no safety.

      n | CFT majority | BFT floor(2n/3)+1 | f = floor((n-1)/3)
      3 |      2       |         3         |        0
      4 |      3       |         3         |        1
      5 |      3       |         4         |        1
      7 |      4       |         5         |        2

  Note n=3 tolerates ZERO Byzantine faults, so its Byzantine quorum is
  unanimity -- which is why a 3-validator cluster is a CFT configuration only.

  `urd.consensus.attest/byzantine-quorum-size` uses the Byzantine threshold
  because it validates CERTIFICATES, which are meant to be checkable by third
  parties under an adversarial assumption. The two are different threat models
  and are supposed to differ. `quorum-thresholds-are-intentionally-different` in the generative
  tests pins that."
  [validator-set]
  (inc (quot (count validator-set) 2)))

(defn has-quorum? [state proposal-id]
  (>= (count (get (:votes state) proposal-id {}))
      (quorum-size (:validator-set state))))

(defn proposal-id
  "A proposal's identity, or nil if it has none.

  Separated out because ABSENT is a value here and the code used to treat it as
  an ordinary one. Every id came from `(:snapshot-id proposal)`, and a proposal
  without that key produced `nil` -- which then flowed through `:votes` as a
  perfectly good map key, matched `:current-proposal-id` (also nil) so the
  \"is this vote for our current proposal\" guard passed, accumulated a quorum,
  and committed `(:current-proposal state)`, which was nil as well. A node
  emitted `nil` into its committed sequence twice in a 120-tick run, and two
  peers that had also done it at different moments then disagreed."
  [proposal]
  (:snapshot-id proposal))

(defn valid-proposal?
  "For our current HEIGHT, and identifiable.

  Deliberately not `(= round (:round state))`, and the reason is the whole
  safety argument of this algorithm. Exactly one validator proposes per height
  -- `get-proposer-id` takes the height alone -- so there is at most one
  proposal per height ever, and that is what makes a majority quorum safe here
  without any locking: two different values cannot both reach a majority when
  only one was ever offered.

  Requiring the ROUND to match as well bought nothing and cost liveness
  outright. A validator that missed the proposal broadcast bumped its round on
  timeout, and from then on refused the very proposal it was waiting for, while
  the proposer -- which only proposes from `handle-start-round`, driven by the
  post-finalization timer -- never sent another. Measured: 5 nodes at 30%
  message loss committed NOTHING in 300 ticks, with the proposer sitting on its
  proposal at round 2 and every other node at round 1 holding none.

  Rotating the proposer by round instead, which is what a view change normally
  does, would fix the liveness and BREAK the safety: two proposers for one
  height means two proposals, and with no locking a node may vote for both, so
  two values could each collect a majority across rounds. The round bump is
  vestigial here by design -- see `handle-timeout`.

  `:valid-fn` is the APPLICATION's predicate, and it defaults to
  `(constantly true)` so nothing changes for a caller that does not supply one.
  Tendermint has had this seam since it was ported; round-robin had no way for
  an application to refuse a proposal on its CONTENT at all, which meant the
  app-hash convention (`urd.consensus.apphash`) was enforceable in exactly one
  of the six algorithms. Structural checks stay above it: a proposal with no
  id is refused before the application is consulted, because there is nothing
  coherent to consult it about."
  [state proposal height _round]
  (and (= height (:height state))
       (some? (proposal-id proposal))
       (boolean ((:valid-fn state) proposal))))

(defn valid-proposer? [sender height validator-set]
  (= sender (get-proposer-id height validator-set)))

(defn valid-voter? [voter validator-set]
  (contains? validator-set voter))

(defn vote-payload
  "What an attestation by a voter covers: `[height proposal-id]`.

  The HEIGHT is not decoration. This used to sign a bare `proposal-id`, which is
  only safe while a proposal id never repeats -- and a proposal id may be a
  `snapshot-id` is a \"UUID or content-hash\". Under the content-hash reading,
  proposing the same value at two heights produces the SAME id, so a vote cast
  at the first height is a valid vote at the second, and an attacker who kept a
  single old attestation could replay it into a later quorum. Tendermint's
  `vote-payload` has made this argument since it was ported; round-robin was
  the one that had not.

  `(:height state)` is the right anchor at every call site because
  `valid-proposal?` requires `(= height (:height state))` -- a proposal is only
  ever accepted at the current height, so there is no moment at which the
  proposal's height and the state's height differ."
  [state proposal-id]
  [(:height state) proposal-id])

(defn valid-height-round?
  "Current, neither stale nor implausibly far ahead. The upper bound is memory
  exhaustion protection: anyone may send anything."
  [state height round]
  (let [h (:height state), r (:round state)]
    (and (or (> height h) (and (= height h) (>= round r)))
         (<= height (+ h 5)))))

(def default-finalized-retention
  "How many finalized heights to keep, and therefore how far behind a peer may
  fall and still be caught up from memory.

  Ten was hard-coded, and ten is very few. `:finalized` is the ONLY history
  this algorithm can serve -- `answer-state-sync` reads it and nothing else --
  so a node that misses eleven heights can never be caught up by anyone, no
  matter how many peers are healthy or how much history the store holds. For a
  validator that restarts, or one whose link drops for a few seconds, that is
  not an edge case.

  Raising it trades memory for reachable catch-up, and the useful range is
  wide: a finalized height is one proposal, so thousands cost little. It stays
  a bound rather than becoming unbounded because the alternative is a map that
  grows for the life of the process.

  The floor is `height - retention` INCLUSIVE, so this keeps N+1 heights. The
  exact number matters because `answer-state-sync` reports the floor as
  `:oldest` and a requester decides whether it is stranded by comparing against
  it.

  It does not FIX the limitation, it sizes it. A peer further behind than this
  still cannot be caught up from a peer's memory and still needs a snapshot
  transfer, which is Tier 5 work: serving arbitrary history means reading the
  durable store, and `step` is pure by construction."
  10)

(defn cleanup-old-data
  "Bound `:finalized`, which would otherwise grow for the life of the process."
  [state]
  (let [floor (max 0 (- (:height state)
                        (:finalized-retention state default-finalized-retention)))]
    (update state :finalized #(into {} (filter (fn [[h _]] (>= h floor))) %))))

;; ============================================================
;; Effects
;; ============================================================

(def default-config
  "Timeouts in TICKS. The legacy runtime used milliseconds against a wall clock;
  see the namespace docstring."
  {:valid-fn (constantly true)
   :proposal-timeout 8
   :quorum-timeout 8
   :next-round-delay 1
   :finalized-retention default-finalized-retention
   ;; How long a stranded node waits before it will ask again. See
   ;; `handle-timeout`'s `:sync-retry` branch for why asking again matters and
   ;; why it has to be on a timer rather than immediately.
   :sync-retry-delay 20})

(defn- log [state level msg] (n/log-effect level msg))

(defn- recovery
  "Recovery requests are ordinary messages. They were five bespoke effects that
  a supposedly generic runtime had to know about by name."
  [kind params]
  (n/broadcast :recovery (assoc params :kind kind)))

;; ============================================================
;; Transitions
;; ============================================================

(defn- bounded-votes
  "The most work a relayed vote list may cost us: one entry per validator.

  A bundle is attacker-supplied and was consumed whole. `record-vote`
  verifies each entry and records NOTHING when verification fails, so
  `(contains? votes voter)` stays false and the same
  `{:voter :a :att \"junk\"}` pair can be repeated as many times as fit in a
  message -- each repeat costing a full Ed25519 verification, inside `step`,
  on the event loop. One message with a million entries is a million
  verifications and a wedged node.

  Two bounds, and both are just the shape of an honest bundle:

  - DEDUPED by voter, because a second vote from the same validator is either
    a duplicate or an equivocation and neither needs re-verifying;
  - TRUNCATED to the validator count, because a bundle naming more distinct
    voters than there are validators cannot be telling the truth.

  Work is now bounded by the size of the validator set no matter how large the
  message is, which is the property that matters -- an attacker can still make
  us do n verifications, but n is ours, not theirs."
  [state votes]
  (let [limit (count (:validator-set state))]
    (->> (if (sequential? votes) votes [])
         (reduce (fn [[seen acc] v]
                   (let [voter (:voter v)]
                     (if (or (contains? seen voter) (>= (count acc) limit))
                       [seen acc]
                       [(conj seen voter) (conj acc v)])))
                 [#{} []])
         second)))

(defn- record-vote
  "Record a voter's ATTESTATION for a proposal, ignoring unknown validators,
  duplicates, and anything that does not verify.

  `:votes` is a map of `{voter attestation}` and used to be a set of bare
  names. A name is all a relayed bundle could carry and all a receiver could
  check, so `:vote-bundle` and `:catchup` -- which exist precisely to relay
  other nodes' votes -- amounted to \"here are the validators I say voted\",
  and one peer could hand us a full quorum it invented. Holding the
  attestation is what makes a vote something a third party can pass on without
  being trusted, which is the same reason Bullshark keys its votes by signer.

  Verification happens HERE rather than at the call sites because every path
  that admits a vote goes through this function, and a check placed on the
  direct path only would have left the two relay paths open -- which is where
  the forgery was cheapest anyway."
  [state proposal-id voter att]
  (if (and (valid-voter? voter (:validator-set state))
           (not (contains? (get-in state [:votes proposal-id]) voter))
           ((:verify-vote state) voter (vote-payload state proposal-id) att))
    (assoc-in state [:votes proposal-id voter] att)
    state))

(declare advance-height)

(defn- maybe-finalize
  "If `proposal-id` has a majority, commit it AND advance.

  Both halves, in one transition, and that is a change from the legacy design
  rather than a translation of it. There, `finalize-effect` was interpreted by
  the runtime, which then fed a `:proposal-finalized` event back in to make the
  node advance -- so a height only completed if the runtime performed a
  round trip through the algorithm. Ported literally that stalls after the first
  commit, because the core protocol has no such loop-back and should not: a node
  that has seen a quorum knows the height is decided, and needing to be told so
  by its own runtime is a design that cannot be reasoned about locally."
  [state proposal-id extra-effects]
  (if-not (and (some? proposal-id) (:current-proposal state) (has-quorum? state proposal-id))
    (n/result state extra-effects)
    (let [proposal (:current-proposal state)
          height (:height state)
          votes (get (:votes state) proposal-id {})]
      (n/result (advance-height state height proposal)
                (into extra-effects
                      [(n/cancel-timer :quorum-timeout)
                       (n/commit [proposal])
                       (n/broadcast :finalizations {:kind :finalized :proposal proposal
                                                    :height height :votes votes})
                       (n/set-timer :next-round (:next-round-delay state))])))))

(defn- activate-updates
  "Apply any validator updates carried by the proposal finalized at `height`.

  ## Why this algorithm is the most sensitive of the three to getting it wrong

  The proposer is `(mod height (count validators))` over the SORTED ids, and
  that is the whole safety argument: exactly one validator proposes per height,
  so at most one proposal per height ever exists, so two different values
  cannot both reach a majority without any locking. `valid-proposal?` says so
  directly.

  A validator set change reindexes that rotation. If two nodes disagree about
  the set at height H they compute DIFFERENT proposers, each accepts a
  different proposal, and the one-proposal-per-height premise is gone -- two
  values could each collect a majority. Nothing else in this algorithm defends
  against that, because nothing else has to.

  So the activation point is not a detail here, it is the safety property.
  Applied at the height boundary, from the finalized proposal, which every node
  agrees on by construction: agreeing on the value IS agreeing on the update.

  A rejected update leaves the set alone. Deterministic, since validity is a
  function of the config and the updates only, so no two nodes can classify it
  differently."
  [state height proposal]
  (let [updates (:validator-updates proposal)]
    (if-not (seq updates)
      state
      (let [vset (:validator-set state)
            cfg {:validators (vec (sort (keys vset)))
                 :powers (zipmap (keys vset) (repeat 1))}
            result (reconfig/apply-updates cfg updates)]
        (if (:error result)
          (update state ::refusals (fnil conj [])
                  {:height height :reason result})
          ;; `:validator-set` is {id -> public-key}; a joiner has no key here.
          ;; Every use in this namespace reads only the KEYS -- `get-proposer-id`
          ;; sorts them, `valid-voter?` tests membership -- and the verifier is
          ;; supplied separately as `:verify-vote`, so a nil value is the same
          ;; "no key material held locally" this map already carries for peers
          ;; whose key was never configured.
          (assoc state :validator-set
                 (into {} (map (fn [v] [v (get vset v)])) (:validators result))))))))

(defn- advance-height
  "Record the decision and move to the next height.

  The validator set change rides here, activated from the finalized proposal.
  See `activate-updates` for why this algorithm cannot tolerate nodes
  disagreeing about the set even briefly."
  [state height proposal]
  (-> state
      (activate-updates height proposal)
      (assoc :height (inc height)
             :sync-requested-at nil
             :round 0
             :phase :proposing
             :current-proposal nil
             :current-proposal-id nil
             :votes {})
      (assoc-in [:finalized height] proposal)
      cleanup-old-data))

(defn handle-start-round [state]
  (if (am-proposer? state)
    (n/result (assoc state :phase :proposing)
              [(n/request-value {:height (:height state) :round (:round state)})
               (n/set-timer :proposal-timeout (:proposal-timeout state))])
    (n/result (assoc state :phase :voting)
              [(n/set-timer :proposal-timeout (:proposal-timeout state))])))

(defn handle-value-ready
  "The application supplied a proposal. Broadcast it and count our own vote --
  IN STATE, not as an effect for a runtime to remember for us.

  ## One proposal per height, enforced here rather than assumed

  `valid-proposal?` rests the entire safety argument of this algorithm on there
  being at most one proposal per height: one proposer per height, therefore one
  proposal, therefore two values cannot both reach a majority because only one
  was ever offered. That is true of the PROPOSER and was not true of the
  PROPOSAL. This function overwrote `:current-proposal` unconditionally, so an
  application that answered a second `request-value` for the same height with a
  different value replaced a proposal that had already been broadcast and voted
  on -- and then two values had been offered for one height after all.

  Nothing in the protocol forbids that answer. `request-value` asks the
  application for a payload; it does not promise to ask once, and it cannot
  require the application to be a pure function of height. So the algorithm
  pins it: the first value for a height is the proposal for that height, and a
  later one is ignored.

  Measured on the real runtime, four nodes, all honest: with a fresh value per
  request the committed sequences diverged at position 148 -- the proposer had
  committed its own second value where its peers had committed the first. With
  a value that was a pure function of height, 298 committed positions and no
  divergence. The application was doing nothing wrong; the algorithm was
  trusting something it had not established."
  [state proposal]
  (let [pid (proposal-id proposal)
        {:keys [height round]} state]
    (cond
      (nil? pid)
      (n/result state [(log state :warn "application supplied a proposal with no :snapshot-id")])

      ;; Already proposing for this height. Re-broadcast what we committed to
      ;; rather than replacing it -- the peers that voted for it are right.
      (some? (:current-proposal state))
      (n/result state
                [(log state :debug "value for a height we have already proposed for -- keeping the first")
                 (n/broadcast :proposals {:kind :proposal
                                          :proposal (:current-proposal state)
                                          :height height :round round})])

      :else
      (n/result (-> state
                    (assoc :current-proposal proposal
                           :current-proposal-id pid
                           :phase :voting)
                    (record-vote pid (:peer-id state)
                                 ((:sign-vote state) (:peer-id state)
                                                     (vote-payload state pid))))
                [(n/broadcast :proposals {:kind :proposal :proposal proposal
                                          :height height :round round})
                 (n/set-timer :quorum-timeout (:quorum-timeout state))]))))

(defn handle-proposal-received [state proposal height round sender]
  (cond
    (not (valid-proposer? sender height (:validator-set state)))
    (n/result state [(log state :warn (str "rejecting proposal from non-proposer "
                                           sender " at height " height))])

    (not (valid-height-round? state height round))
    (n/result state [(log state :debug (str "ignoring out-of-range proposal: height "
                                            height " round " round))])

    (:current-proposal state)
    (n/result state [(log state :debug "ignoring duplicate proposal")])

    (valid-proposal? state proposal height round)
    (let [proposal-id (proposal-id proposal)]
      (n/result (-> state
                    (assoc :current-proposal proposal
                           :current-proposal-id proposal-id
                           :phase :voting)
                    (record-vote proposal-id (:peer-id state)
                                 ((:sign-vote state) (:peer-id state)
                                                     (vote-payload state proposal-id))))
                [(n/cancel-timer :proposal-timeout)
                 (n/broadcast :votes {:kind :vote :proposal-id proposal-id
                                      :voter (:peer-id state)
                                      :att ((:sign-vote state) (:peer-id state)
                                                               (vote-payload state proposal-id))
                                      :height height :round round})
                 (n/set-timer :quorum-timeout (:quorum-timeout state))]))

    :else
    (n/result state [(log state :debug "ignoring proposal for another height/round")])))

(defn handle-vote-received [state proposal-id voter att]
  (cond
    (not (valid-voter? voter (:validator-set state)))
    (n/result state [(log state :warn (str "rejecting vote from unknown validator " voter))])

    (not ((:verify-vote state) voter (vote-payload state proposal-id) att))
    ;; Rejected here as well as in `record-vote`, so the reason is LOGGED. A
    ;; forged vote that is merely not counted looks identical to a vote that
    ;; never arrived, and an operator has no way to tell a broken link from a
    ;; peer minting votes for its neighbours.
    (n/result state [(log state :warn (str "rejecting unattested vote claiming to be from "
                                           voter))])

    (or (nil? proposal-id) (not= proposal-id (:current-proposal-id state)))
    (n/result state [(log state :debug "ignoring vote for a non-current proposal")])

    (= :finalizing (:phase state))
    (n/result state [(log state :debug "ignoring vote -- already finalizing")])

    (contains? (get-in state [:votes proposal-id]) voter)
    (n/result state [(log state :debug (str "ignoring duplicate vote from " voter))])

    :else
    (maybe-finalize (record-vote state proposal-id voter att) proposal-id [])))

(defn handle-finalization
  "A peer told us a height finalized, or our own commit did."
  [state proposal height]
  (cond
    ;; ANY height above ours means we are behind. This was
    ;; `(> height (inc (:height state)))` -- two or more ahead -- so a node
    ;; exactly ONE height behind fell through to the `:else` branch, logged
    ;; "already finalized", and never asked for state sync. One behind is the
    ;; common case: miss a single finalization and you are there.
    ;;
    ;; And it is unrecoverable without this. A node at height h refuses every
    ;; proposal for h+1, because `valid-proposal?` requires exact height
    ;; equality; the finalizations that would carry it forward land in `:else`;
    ;; and its `:want-proposal` requests are only answered by peers still at h,
    ;; of which there are none. The trace shows it plainly -- a stranded node
    ;; receives 41 proposals and 143 finalizations and commits nothing.
    (> height (:height state))
    ;; ONCE per height, not once per finalization seen.
    ;;
    ;; Correct and unthrottled is a message storm. Every peer's finalization
    ;; broadcast reaches every node that is behind, each of which asked for a
    ;; state sync, and each answer carries the responder's whole `:finalized`
    ;; map. Five nodes over kabel went from ten heights finalized each to one,
    ;; and the simulator showed nothing -- it models neither message size nor
    ;; bandwidth, so an amplification that is ruinous on a real transport is
    ;; free there.
    ;;
    ;; This is the shape to watch for generally: a fix that is correct per
    ;; message and wrong per second.
    (if (= (:sync-requested-at state) (:height state))
      (n/result state)
      (n/result (assoc state :sync-requested-at (:height state))
                [(log state :info (str "behind: at " (:height state)
                                       ", saw finalization for " height))
                 (recovery :state-sync {:from (:height state) :to height})]))

    ;; A peer announcing a DIFFERENT proposal for the height we are working on
    ;; is not a decision we can adopt: we hold one proposal for this height and
    ;; it is not that one. Only one proposal per height can exist in an honest
    ;; run -- `handle-value-ready`, `handle-proposal-received` and
    ;; `handle-proposal-catchup` each enforce it -- so this branch firing means
    ;; something upstream is already broken, and committing the announcement
    ;; over what we hold is how one peer rewrites another's committed prefix.
    ;;
    ;; Loud, and not adopted. The alternative is picking whichever arrived last
    ;; and calling it consensus.
    ;; Derived from `:current-proposal` rather than read from
    ;; `:current-proposal-id`. The id is a cache of the proposal, and a safety
    ;; guard should not be able to fail open because a cache was not filled in.
    (and (= height (:height state))
         (:current-proposal state)
         (not= (proposal-id proposal) (proposal-id (:current-proposal state))))
    (n/result state
              [(log state :warn
                    (str "REFUSING a finalization for height " height
                         " naming " (proposal-id proposal)
                         " -- we hold " (proposal-id (:current-proposal state))))])

    (= height (:height state))
    ;; A peer reached quorum before we did, so we learn the decision from its
    ;; announcement and commit it ourselves. A node that already finalized this
    ;; height locally has moved on and takes the `:else` branch below, so no
    ;; height is ever committed twice.
    (n/result (advance-height state height proposal)
              [(log state :info (str "finalized height " height " from a peer"))
               (n/commit [proposal])
               (n/set-timer :next-round (:next-round-delay state))])

    :else
    (n/result state [(log state :debug (str "already finalized height " height))])))

(defn handle-timeout [state timer-id]
  (case timer-id
    :next-round (handle-start-round state)

    :proposal-timeout
    ;; RETRANSMIT rather than advance. The round is not bumped: it selects
    ;; nothing (the proposer depends on height alone) and bumping it only
    ;; narrowed what this node would accept. Tendermint recorded the same
    ;; lesson -- no retransmission inside the state machine means zero progress
    ;; under loss -- and this algorithm had the recovery messages for it all
    ;; along, with nothing in the state machine answering them.
    (if (am-proposer? state)
      (if-let [proposal (:current-proposal state)]
        (n/result state
                  [(log state :debug "proposal timeout -- re-broadcasting")
                   (n/broadcast :proposals {:kind :proposal :proposal proposal
                                            :height (:height state) :round (:round state)})
                   (n/set-timer :proposal-timeout (:proposal-timeout state))])
        (n/result state
                  [(log state :debug "proposal timeout -- asking the application again")
                   (n/request-value {:height (:height state) :round (:round state)})
                   (n/set-timer :proposal-timeout (:proposal-timeout state))]))
      (n/result state
                [(log state :debug "proposal timeout -- asking peers")
                 (recovery :want-proposal {:height (:height state) :round (:round state)})
                 (n/set-timer :proposal-timeout (:proposal-timeout state))]))

    :quorum-timeout
    ;; Same: ask again and keep asking, rather than advancing a round that
    ;; selects nothing.
    (let [pid (:current-proposal-id state)]
      (n/result state
                (if pid
                  [(log state :debug "quorum timeout -- asking for votes")
                   (recovery :want-votes {:proposal-id pid
                                          :height (:height state)
                                          :round (:round state)})
                   (n/broadcast :votes {:kind :vote :proposal-id pid
                                        :voter (:peer-id state)
                                        :att ((:sign-vote state) (:peer-id state)
                                                                 (vote-payload state pid))
                                        :height (:height state) :round (:round state)})
                   (n/set-timer :quorum-timeout (:quorum-timeout state))]
                  [(log state :debug "quorum timeout with no proposal to ask about")
                   (n/set-timer :quorum-timeout (:quorum-timeout state))])))

    :sync-retry
    ;; Let the next finalization we see ask again. This does not itself send
    ;; anything: a request needs a peer we know is ahead, and seeing a
    ;; finalization above us is how we learn that. Clearing the flag is
    ;; therefore the whole action, and it re-arms the throttle for one request
    ;; rather than opening the gate.
    (n/result (assoc state :sync-requested-at nil)
              [(log state :debug "sync retry: will ask again on the next finalization")])

    (n/result state [(log state :warn (str "unknown timer " timer-id))])))

;; ============================================================
;; Recovery
;; ============================================================

(defn handle-proposal-catchup
  "A peer sent us a proposal together with the votes it has for it.

  It does NOT replace a proposal we already hold. This function used to
  `assoc` `:current-proposal` unconditionally, which is the same mistake
  `handle-value-ready` and `handle-proposal-received` each already guard
  against, on the one path that had no guard -- and the most dangerous path to
  leave open, because a catchup is precisely a proposal arriving from someone
  who is not its author.

  A node that has voted for P and is then handed Q for the same height would
  adopt Q and vote for that too. Having voted for both, it counts toward BOTH
  tallies, and with four validators both can reach three. That is two nodes
  committing different values at one position, from one relayed message.

  The rule is the same one stated at `handle-value-ready`: the first proposal
  for a height is THE proposal for that height. It has to hold on every path
  that can set one, and this was the third.

  Known gap, recorded rather than fixed here: a proposal carries no signature
  from its proposer, so a relayed one cannot be checked against
  `valid-proposer?` -- the sender is the relayer. Votes are attested now;
  proposals are not. Until they are, this guard is what keeps a relayer from
  introducing a second proposal for a height we have already committed to."
  [state proposal height round votes]
  (let [pid (proposal-id proposal)]
    (cond
      (not (valid-proposal? state proposal height round))
      (n/result state [(log state :debug "catchup: proposal is not for our height/round")])

      (and (:current-proposal state)
           (not= pid (proposal-id (:current-proposal state))))
      (n/result state
                [(log state :warn
                      (str "catchup: refusing a SECOND proposal for height " height
                           " -- we hold " (proposal-id (:current-proposal state))))])

      :else
      (let [state (reduce (fn [s v] (record-vote s pid (:voter v) (:att v)))
                          (assoc state :current-proposal proposal
                                 :current-proposal-id pid
                                 :phase :voting)
                          (bounded-votes state votes))]
        (maybe-finalize state pid
                        [(log state :info (str "catchup: proposal with " (count votes)
                                               " votes"))])))))

(defn handle-state-sync-response
  "Adopt a peer's finalized history -- and COMMIT what we learn from it.

  The commits are the point. This used to jump the height and merge the
  finalized map while emitting nothing, so a node that synced skipped straight
  past decisions it had never reported: its committed sequence acquired a hole,
  and two nodes then disagreed at those positions. `sim/agreement?` catches it
  as a safety violation, which is what it is.

  It went unseen because `handle-finalization` only asked for a sync when it was
  TWO or more heights behind, and being exactly one behind -- the common case --
  fell into a branch that did nothing. Fixing that off-by-one made syncs
  ordinary and the hole appeared at once. One defect was hiding the other.

  Only the CONTIGUOUS run starting at our own height is committed. A peer may
  send a history with gaps, and a commit sequence with a gap is precisely what
  is being fixed here; the rest arrives on the next sync.

  ## A sync that teaches us nothing must change nothing

  This used to reset `:round`, `:current-proposal` and `:votes`
  UNCONDITIONALLY, including when `new-height` came out equal to the height we
  were already at -- which is the common case, because a `state-sync-response`
  is an answer to a question we asked a while ago and the answer is routinely
  stale by the time it lands.

  For an ordinary node that is merely wasteful. For the PROPOSER it is a safety
  violation, and it is the one that had round-robin diverging on roughly one
  conformance run in eight:

    1. `:a` is the proposer for height 8. It has asked the application for a
       value, got one, broadcast it and voted for it. Peers are voting too.
    2. A stale `state-sync-response` arrives that teaches it nothing.
    3. It wipes its own proposal and the votes cast for it, and returns to
       `:proposing` at round 0.
    4. `:next-round` fires. It is still the proposer for height 8, so it asks
       the application AGAIN -- and an application is entitled to answer with a
       different value, because `request-value` never promised to ask once.
    5. Two proposals now exist for one height. Nodes holding the first keep it
       (`handle-value-ready` guards that); nodes holding nothing take the
       second. Votes accumulate on BOTH tallies, and with four validators both
       can reach three. Two nodes commit different values at the same position.

  `handle-value-ready`'s \"the first value for a height is the proposal for that
  height\" was the right rule and could not hold, because the state it is
  written on was being erased underneath it. The whole safety argument of this
  algorithm -- one proposer per height, therefore one proposal, therefore only
  one value can reach a majority -- fails at the second step.

  So the reset is now conditional on actually having moved.

  ## We advance only as far as we have COMMITTED

  `new-height` used to include the peer's `current-height` in its `max`, so a
  node at 0 syncing from a peer at 500 arrived at 500 having committed nothing
  at all. Its committed sequence then began at 500 with heights 0-499 missing,
  and against the datahike ledger that transacts height 500 into a database
  that has never seen the preceding 499 -- a hole, presented as a catch-up.

  The height now advances only over the contiguous run we actually learned and
  emitted commits for. A node that is far behind therefore takes several
  rounds, which is correct and merely slow.

  `oldest` is what the responder can still serve. `:finalized` is bounded to
  ten heights, so a peer far enough behind cannot be caught up by this peer at
  all -- and that is a real limitation of having no archival history (see the
  compaction finding), not something to paper over. It is reported at `:warn`,
  because the alternative is what this function used to do: jump, and look
  caught up."
  [state finalized-heights current-height oldest]
  (let [ours (:finalized state)
        merged (merge ours finalized-heights)
        h0 (:height state)
        learned (->> (iterate inc h0)
                     (take-while #(contains? merged %))
                     (remove #(contains? ours %))
                     vec)
        ;; Only what we actually LEARNED is kept, never the peer's whole map.
        ;;
        ;; `merged` is used to walk the contiguous run and then discarded.
        ;; Storing it merged every entry a peer chose to send, at any height,
        ;; with no size bound -- and `cleanup-old-data` prunes only BELOW
        ;; `height - 10`, so entries above our height survived every future
        ;; prune. `answer-state-sync` then re-served them, making each node a
        ;; relay for whatever it had been fed. One broadcast could plant an
        ;; arbitrary number of permanent entries on every node at once.
        ;;
        ;; The contiguous run is exactly what we emit commits for, so keeping
        ;; that and nothing else also makes `:finalized` agree with what the
        ;; consumer was told.
        kept (reduce (fn [m h] (assoc m h (get merged h))) ours learned)
        new-height (if (seq learned) (inc (apply max learned)) h0)
        advanced? (> new-height h0)
        stranded? (and (not advanced?)
                       (some? oldest)
                       (> oldest h0)
                       (> current-height h0))]
    (n/result (cond-> (assoc state :finalized kept :height new-height)
                ;; Only when the height actually moved. At a NEW height the
                ;; old proposal and its votes are meaningless and must go; at
                ;; the same height they are live consensus state and this node
                ;; may be the one proposer that owns them.
                advanced? (assoc :round 0
                                 :phase :proposing
                                 :current-proposal nil
                                 :current-proposal-id nil
                                 :votes {}))
              (into [(if stranded?
                       (log state :warn
                            (str "state sync: cannot catch up from this peer -- we are at "
                                 h0 " and its history starts at " oldest
                                 ". Retrying; a peer with deeper history may appear."))
                       (log state :info (str "state sync: now at height " new-height
                                             ", learned " (count learned))))]
                    (concat
                     (map (fn [h] (n/commit [(get merged h)])) learned)
                     (when advanced?
                       [(n/set-timer :next-round (:next-round-delay state))])
                     ;; Arm a retry. `:sync-requested-at` is set to the current
                     ;; height to throttle the request storm, and a stranded
                     ;; node never leaves that height -- so it asked once, was
                     ;; told nobody could help, and then never asked again for
                     ;; the rest of the process's life. A validator that
                     ;; rejoins with deeper history, or one that finishes
                     ;; catching up itself, could serve it, and it would never
                     ;; find out.
                     ;;
                     ;; On a TIMER rather than by clearing the flag here:
                     ;; clearing it means the next finalization broadcast --
                     ;; which arrives constantly -- triggers another request,
                     ;; which is exactly the storm the flag exists to prevent.
                     ;; The throttle and the retry are both necessary and they
                     ;; are in tension; the timer is what resolves it.
                     (when stranded?
                       [(n/set-timer :sync-retry (:sync-retry-delay state))]))))))

(defn answer-state-sync
  "A peer is behind. Send the history it asked for, and say what we still hold.

  `from` is the requester's height, which the request has always carried and
  this function used to ignore -- it replied with `(:finalized state)`
  wholesale. That map is bounded to the last ten heights, so a peer at 0 asking
  a peer at 500 was answered with heights 490-499: nothing it could use, and
  nothing that told it so.

  `:oldest` is the earliest height we can still serve. A requester below it
  cannot be caught up by us, and needs to hear that rather than infer it from
  an answer that looks fine and helps not at all."
  [state to from]
  (let [fin (:finalized state)
        wanted (into {} (filter (fn [[h _]] (>= h (or from 0)))) fin)]
    (n/result state
              [(n/send-to to {:kind :state-sync-response
                              :finalized wanted
                              :oldest (if (seq fin) (apply min (keys fin)) 0)
                              :current-height (:height state)})])))

(defn answer-want-proposal
  "A peer timed out waiting for a proposal. If we hold one for that height, send
  it with every vote we have -- proposal and votes together, since a peer that is
  behind needs both and one round trip is enough.

  The peer's ROUND is not checked, for the same reason `valid-proposal?` does
  not check it: one proposer per height means one proposal per height, so a peer
  asking about our height is asking about the only proposal there is.

  ## Answering a peer that is BEHIND, which used to get silence

  A request for a height we have already passed used to fall through to
  `(n/result state)` -- no reply at all. That is the stranding described in
  `handle-finalization`, seen from the other side, and it is permanent.

  The catch-up path fires only inside `handle-finalization`, so a node learns
  it is behind only by RECEIVING a finalization. Finalizations are broadcast
  once, at the moment of finalization. Miss that one-shot event -- subscribe a
  few milliseconds late, drop the packet -- and there is no second trigger
  ever: the node refuses every later proposal on the exact-height check, its
  `want-proposal` is answered by nobody, and `:sync-requested-at` stays nil.

  Measured over kabel: two of five validators missed the first finalization,
  received 105 `:want-proposal` messages and NOTHING else for twenty seconds,
  and sat at height 0 with no votes and no sync request. The network then
  halted outright -- once a stranded node's turn to propose came round it
  produced nothing, and the remaining nodes spent the run asking for a proposal
  that was never going to arrive. One height committed in twenty seconds where
  a healthy run does two hundred.

  So a peer asking about a height below ours is told where we are. It is the
  one moment we are certain it is behind, and it costs a single directed
  message -- the requests are already rate-limited by the asker's proposal
  timeout, and they stop as soon as it catches up."
  [state height _round to]
  (let [pid (:current-proposal-id state)]
    (cond
      (and pid (= height (:height state)))
      (n/result state
                [(n/send-to to {:kind :catchup
                                :proposal (:current-proposal state)
                                :height height :round (:round state)
                                ;; The ATTESTATION travels with the name. A
                                ;; bundle of bare names is a claim by the
                                ;; relayer, not evidence about the voters.
                                :votes (mapv (fn [[v att]] {:voter v :att att})
                                             (get (:votes state) pid {}))})])

      (< height (:height state))
      (answer-state-sync state to height)

      :else
      (n/result state))))

(defn answer-want-votes
  "A peer reached the quorum timeout. Send it what we have for that proposal."
  [state proposal-id to]
  (if (and proposal-id (= proposal-id (:current-proposal-id state)))
    (n/result state
              [(n/send-to to {:kind :vote-bundle
                              :proposal-id proposal-id
                              :votes (mapv (fn [[v att]] {:voter v :att att})
                                           (get (:votes state) proposal-id {}))})])
    (n/result state)))

(defn handle-vote-bundle [state proposal-id votes]
  (if-not (and (some? proposal-id) (= proposal-id (:current-proposal-id state)))
    (n/result state [(log state :debug "vote bundle: not for the current proposal")])
    (let [votes (bounded-votes state votes)
          state (reduce (fn [s v] (record-vote s proposal-id (:voter v) (:att v)))
                        state votes)]
      (maybe-finalize state proposal-id
                      [(log state :debug (str "vote bundle: " (count votes) " votes"))]))))

;; ============================================================
;; Attestations -- TEST ONLY
;; ============================================================

(defn test-attestations
  "A toy vote-attestation scheme, for tests and simulations only.

  NOT CRYPTOGRAPHY. It is a hash of a per-voter string, so anyone who can read
  this namespace can mint one for any voter. What it provides is the SHAPE: an
  attestation binds a voter to a `vote-payload`, verification is a pure
  predicate, and anything not produced this way fails -- which is what a test
  needs to drive the guard down both branches.

  `urd.consensus.attest/attestations` is the real one and is a drop-in for
  this. `init` refuses to start without a scheme precisely so this stub cannot
  be reached by accident."
  []
  (let [sign (fn [voter payload] (hasch/uuid [::test-vote voter payload]))]
    {:sign-vote sign
     :verify-vote (fn [voter payload att]
                    (and (some? att) (= att (sign voter payload))))}))

;; ============================================================
;; The node
;; ============================================================

(defrecord RoundRobin [validator-set]
  n/Node

  (capabilities [_]
    ;; Crash-fault tolerant and absolutely final: a majority-voted proposal is
    ;; never taken back. No `:sample`, no `:persist-then` -- this algorithm keeps
    ;; no durable state, which is a real limitation rather than an omission and
    ;; is why it is a reference rather than a deployment candidate.
    {:emits #{:broadcast :send :set-timer :cancel-timer :request-value :commit :log}
     :topics #{:proposals :votes :finalizations :recovery}})

  (init [_ config]
    (let [cfg (merge default-config config)
          ;; Checked: an EMPTY set makes `get-proposer-id` divide by zero on
          ;; the first timer tick and kills the event loop before this node has
          ;; done anything, and a DUPLICATE under-counts every quorum. Both
          ;; come from a config file, so the error belongs at `init` where an
          ;; operator can read it.
          vset (or validator-set
                   (zipmap (n/validator-set config) (repeat nil)))
          ;; REQUIRED, not defaulted, following Bullshark. A vote here is
          ;; relayed -- `:vote-bundle` and `:catchup` exist to carry other
          ;; nodes' votes -- so the peer handing us one is usually not its
          ;; author, and transport authentication says nothing about the
          ;; voters. Without a verifier a bundle is just a list of names the
          ;; relayer chose, and a node that cannot check one has no business
          ;; counting it toward a quorum. A permissive default is how this
          ;; survived a full audit round in the first place.
          sign-vote (or (:sign-vote config)
                        (throw (ex-info "round-robin requires :sign-vote -- (fn [voter vote-payload]) -> attestation"
                                        {:peer-id (:peer-id config)})))
          verify-vote (or (:verify-vote config)
                          (throw (ex-info "round-robin requires :verify-vote -- (fn [voter vote-payload att]) -> boolean"
                                          {:peer-id (:peer-id config)})))]
      (n/result (merge cfg
                       {:peer-id (:peer-id config)
                        :sign-vote sign-vote
                        :verify-vote verify-vote
                        :validator-set vset
                        :height 0
                        :round 0
                        :phase :proposing
                        :current-proposal nil
                        :current-proposal-id nil
                        :votes {}
                        :finalized {}})
                [(n/set-timer :next-round (:next-round-delay cfg))])))

  (step [_ state input]
    (case (:type input)
      :timer-fired (handle-timeout state (:timer-id input))

      :value-ready (handle-value-ready state (:value input))

      :message-received
      (let [msg (:msg input)
            from (:from input)]
        (if-not (well-formed? msg)
          (n/result state)
          (case (:kind msg)
            :proposal (handle-proposal-received state (:proposal msg) (:height msg)
                                                (:round msg) from)
            :vote (handle-vote-received state (:proposal-id msg) (:voter msg) (:att msg))
            :finalized (handle-finalization state (:proposal msg) (:height msg))
            :catchup (handle-proposal-catchup state (:proposal msg) (:height msg)
                                              (:round msg) (:votes msg))
            :state-sync-response (handle-state-sync-response state (:finalized msg)
                                                             (:current-height msg)
                                                             (:oldest msg))
            :vote-bundle (handle-vote-bundle state (:proposal-id msg) (:votes msg))
            ;; A recovery REQUEST is answered HERE. The legacy runtime answered
            ;; these itself, outside the state machine -- which is why it needed to
            ;; know five algorithm-specific effects by name, and why porting the
            ;; algorithm without them stalled completely under message loss: the
            ;; requests still went out and nobody replied. A node answering a
            ;; question about its own state is the state machine's job.
            :want-proposal (answer-want-proposal state (:height msg) (:round msg) from)
            :want-votes (answer-want-votes state (:proposal-id msg) from)
            :state-sync (answer-state-sync state from (:from msg))
            (n/result state [(log state :debug (str "unhandled message kind " (:kind msg)))]))))

      ;; An unrecognised input is LOGGED, never silently dropped -- the same
      ;; rule `schedule` applies to an unknown step and `signing` to an unknown
      ;; signing step. A machine that quietly ignores what it does not
      ;; understand cannot be distinguished from one that is working.
      (n/result state [(log state :warn (str "unknown input type " (:type input)))]))))

(defn create
  "A round-robin node.

  `validator-set` is {peer-id -> public-key}; when omitted it is derived from
  `:validators` in the config, since this algorithm only ever uses the KEYS."
  ([] (->RoundRobin nil))
  ([validator-set] (->RoundRobin validator-set)))

(defn make [] (create))
