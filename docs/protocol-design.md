# Urd — Core Protocol Design

Status: first pass, 2026-08-14. Written to guide implementation and keep orientation
across a long build. Every non-obvious decision below cites the algorithm that *forces*
it, so we can tell a requirement from a preference when we revisit.

Sources: fresh reads of `../etcd-raft`, `../cometbft`, `../avalanchego`, `../btcd`,
`../narwhal`, `../HoneyBadgerBFT`, Stellar SCP, plus measurements against
`../geheimnis`, `../hasch`, `../konserve`, `../datahike`.

---

## 0. What we are building, and what we are not

A **portable (clj + cljs), pure-functional consensus library**: algorithms are pure
state machines, a runtime interprets their effects, and a deterministic simulator drives
them under adversarial schedules.

Priority order, as decided:

1. **General portable library.** clj+cljs purity and cross-algorithm generality win when
   they conflict with any single consumer's convenience.
2. Datahike failover and permissionless consensus are *consumers*, not the design driver.

Explicit non-goals: competitive mining; being a production Bitcoin/Tendermint node;
matching any reference implementation byte-for-byte except where we deliberately port a
conformance corpus.

---

## 1. The core abstraction

**Not** "a log of decided values at increasing heights." That shape cannot express three
of our eight algorithms.

The core is **fork choice over a vertex DAG, plus a finality predicate**:

- **vertices** carry parent links and a payload;
- a **fork-choice rule** maps known vertices + votes/weights → the current head;
- a **finality rule** identifies the irreversible prefix;
- an **eligibility rule** says who may extend, and with what weight.

Why this shape is forced, not chosen:

| algorithm | needs |
|---|---|
| **Raft** | a new leader makes followers truncate a conflicting *uncommitted* suffix (§5.3) — that is a revert. `etcd-raft` carries `log_unstable.go` precisely for this. |
| **Nakamoto** | heaviest-chain fork choice with deep reorgs; committed state is un-committed. |
| **Bullshark** | one certificate retroactively commits several earlier anchors and their whole sub-DAGs. |
| **Snowman** | preference flips freely before finalization; finalization is then absolute. |
| **Tendermint** | no forks in the happy path; absolute finality. The degenerate case. |

So **revocable commits are not a PoW concession — Raft needs them too.** That settles the
`:commit`/`:revert` question in the affirmative for the core API.

**Why this fits our substrate.** Yggdrasil already *is* a git-like causal DAG of
copy-on-write snapshots. Urd's job reduces to: pick the canonical head, say when it is
final. And reorgs are cheap here in a way they are not elsewhere — reverting is moving a
branch pointer to an older commit, because index blocks are immutable and still in the
store. `btcd` confirms the general principle from the other direction: **at the header
layer its undo log is empty** — every consensus quantity is a fold over the ancestor path,
so a reorg of any depth is a pointer swap plus a work comparison. All of Bitcoin's
two-phase reorg and spend-journal machinery exists *only* because its UTXO set is a
destructively-mutated map. We do not have that problem.

---

## 2. The node protocol

```clojure
(defprotocol Node
  (init [this config]
    "-> {:state s :effects fx}")
  (step [this state input]
    "input is an event or a tick. -> {:state s' :effects fx}"))
```

Two departures from today's `ConsensusAlgorithm`, both forced:

**`init` returns effects.** A node must be able to persist hard state or arm a timer at
startup. Today's `initial-state` returns bare state.

**`step` must be allowed to run an internal fixpoint.** SCP's `advanceSlot` is recursive
and re-entrant (`BallotProtocol.cpp:1835-1850`): accepting one statement unlocks the next
three checks. One-transition-per-event cannot express it. So `step` is permitted to loop
internally until no rule fires, accumulating effects — the loop lives *inside* the pure
function, over immutable state, so determinism is preserved.

### Events

```clojure
{:type :message-received  :from peer-id :msg {...} :verified-by #{peer-id}}
{:type :timer-fired       :timer-id id}
{:type :sampled           :request-id id :peers bag}      ; response to :sample
{:type :persisted         :token t :epoch e}              ; response to :persist-then
{:type :value-ready       :value v}                       ; response to :request-value
{:type :vertex-received   :vertex v}
{:type :instance          :instance-id iid :inner event}  ; see §6
```

`:verified-by` is the crux of §5: the state machine never sees an unverified signature.

### Effects

```clojure
[:send        {:to peer-id :msg m}]                  ; UNICAST — absent today
[:broadcast   {:topic t :msg m}]
[:persist-then {:writes {...} :durable? bool
                :epoch e :then [effect ...]}]        ; see §3
[:sample      {:request-id id :k n :from :validators|:peers}]
[:set-timer   {:timer-id id :after-ticks n}]         ; LOGICAL time
[:cancel-timer {:timer-id id}]
[:request-value {:context ...}]
[:commit      {:vertices [v ...] :index n}]          ; ORDERED SEQUENCE
[:revert      {:to-vertex v}]
[:report-equivocation {:peer p :evidence [a b]}]
[:log         {:level l :message m}]
```

Justification for each of the non-obvious ones:

- **`:send` (unicast).** `ConsensusNetwork` today has only `broadcast!`. Raft's
  AppendEntries is per-peer with per-peer `Progress` state, and Snowman queries exactly
  `k` sampled peers. This is the single biggest structural gap in the current code.
- **`:sample`.** Avalanche samples `k` peers per poll. Randomness must be an *effect* so
  the simulator owns the seed and traces replay. Note: `avalanchego` samples **stake
  weight without replacement**, which means *node indices may repeat*
  (`weighted_without_replacement.go:6-8`) — so the response is a **bag, not a set**, and
  multiplicity is vote weight. Getting this wrong silently changes the protocol.
- **`:commit` takes a vector and an index.** Bullshark's `process_certificate` returns
  `Vec<ConsensusOutput>`; one certificate can commit an anchor and then back-fill several
  earlier anchors plus their sub-DAGs — potentially hundreds of vertices at once. A
  `(finalize proposal height)` signature cannot express that. The `:index` is a globally
  increasing consensus index, **decoupled from round/height**.
- **`:revert`.** §1.
- **`:report-equivocation`.** In CometBFT, `addVerifiedVote` returns a conflicting vote
  which becomes evidence (`state.go:2127-2151`). Detecting specific misbehaviour is a
  *protocol action*, not a dropped message. HoneyBadger likewise treats caught
  equivocation as a first-class outcome (`includeTransaction.py:112-115`).
- **Timers are logical.** `:after-ticks`, not milliseconds. Wall-clock timers in the
  runtime make timeout behaviour unsimulatable — and timeouts are exactly where consensus
  bugs live.

**`step` may return `:effects []` and still finalize.** Bullshark's ordering layer sends
*zero* messages — ordering is a deterministic function of the DAG. A runtime that assumes
"a decision is preceded by a vote round" will not fit it.

---

## 3. Durability: the `:persist-then` barrier

Two independent reference implementations converged on the same rule, which is strong
evidence it is the right one:

- **etcd-raft** routes exactly `{MsgAppResp, MsgVoteResp, MsgPreVoteResp}` into
  `msgsAfterAppend` (`raft.go:546`); everything else sends immediately.
- **CometBFT** fsyncs exactly the messages *this node signs* — its own proposal, prevote,
  precommit — plus the end-height marker (`state.go:881-905`).

Stated once: **durability-gate exactly the messages that constitute this node's binding
commitment. Send everything else immediately.**

Three details worth copying:

1. **Not everything needs fsync.** etcd-raft's `MustSync` (`rawnode.go:191-198`) is
   `entries≠0 ∨ vote changed ∨ term changed`. A *commit index* change alone does not,
   because commit is recoverable by replay. Hence `:durable?` on the effect.
2. **Completion tokens must carry an epoch/term witness.** etcd-raft's
   `newStorageAppendRespMsg` (`rawnode.go:266-363`) carries `r.Term` and *drops the
   response if the term changed*, defeating an ABA hazard where two in-flight appends
   overwrite the same indices across a leader change. So `:persisted` carries `:epoch`,
   and a stale completion is a **no-op, not an error**.
3. **The state machine must remember which effects it already emitted**, or it re-emits
   them next step. etcd-raft's `unstable` tracks three regions — stable / in-progress /
   pending (`log_unstable.go:37-54`). We need the equivalent.

**A second, separate barrier: the double-sign guard.** CometBFT keeps
`FilePVLastSignState{Height,Round,Step,...}` in an atomically-rewritten file, distinct
from the WAL (`privval/file.go:74-83`) — it is the only thing that survives a WAL wipe.
Keep it out of the effect log. Its predicate `may-sign?` is a ~20-line total function and
**the theorem that it admits at most one prevote and at most one precommit per (height,
round) is what makes a validator non-slashable.** That is our first verification target
(§8).

**A note on how a revert appears.** In etcd-raft a truncation produces *no distinguished
effect at all* — the storage layer must infer it from an append at a lower index
(`doc.go:76-77`). That is a classic source of storage bugs. **We make it explicit**:
`:persist-then` carries `:truncate-from` where applicable.

---

## 4. Trust and membership

Today's `:validator-set` is `{peer-id → public-key}` with `(quorum-size n)` a number.
**That does not generalize.** In Stellar SCP, quorum-ness is not a cardinality — it is a
*greatest fixpoint* over other nodes' advertised trust configurations
(`LocalNode.cpp:252-290`), so it is transitive and subjective.

The membership abstraction is therefore protocol-supplied predicates:

```clojure
(defprotocol Membership
  (quorum?     [this state statements pred])
  (v-blocking? [this state statements pred])
  (weight      [this state peer-id]))
```

Note these take a **predicate over statements**, not a count — SCP's federated voting
calls the same machinery with three different predicates (`voted`, `voted ∨ accepted`,
`accepted`; `Slot.cpp:345-375`). Note also the asymmetry: `v-blocking?` is *local* and
cardinality-dual, while `quorum?` is *transitive*.

Three consequences:

- Standard BFT supplies `quorum? = |S| > 2n/3`, Raft supplies majority, Nakamoto supplies
  a work-weight rule, SCP supplies the fixpoint. One protocol, four instantiations.
- **Quorum evaluation must be able to fail for want of data.** SCP routinely receives a
  statement whose `quorumSetHash` it has never seen. So the result is tri-state —
  stellar-core literally has `TB_TRUE/TB_FALSE/TB_MAYBE` (`LocalNode.cpp:428-479`) — with
  a `[:request-qset]` effect and a `:qset-received` event. No CFT/classical-BFT algorithm
  has a "my safety check is currently undecidable" state; SCP does.
- Open membership (Nakamoto) means there is no set at all — eligibility is proof-of-work.
  `weight` covers stake, work, and uniform cases.

---

## 5. The crypto boundary

**Measured, not assumed:**

- `hasch/sha256` is **synchronous** bytes→bytes on *both* platforms — JVM `MessageDigest`
  (`platform.clj:41`), cljs `goog.crypt.Sha256` (`platform.cljs:97`).
- geheimnis Ed25519 is **channel-returning on cljs** (`sign.cljc:121-136`), because Web
  Crypto's `subtle.sign`/`verify` are promise-based. There is no way around it.

Therefore: **signature verification cannot happen inside the pure state machine.** It runs
at the edge; the machine sees only pre-authenticated events carrying `:verified-by`. This
is forced by the platform, not preferred — and it is also what CometBFT's own layering
implies, since `addVerifiedVote` is documented "assumes signature is valid"
(`vote_set.go:257`).

The asymmetry is useful: **hashing is sync, signing is async.** PoW proofs *are*
inline-verifiable inside the pure machine; BFT votes are not.

Two traps:

- **`(vote → signature)` is not a function.** Ed25519 signatures from remote signers can
  be non-deterministic (CometBFT has `ErrVoteNonDeterministicSignature`,
  `vote_set.go:215`). The verified-event stream must carry the raw signature and the core
  must not assume uniqueness.
- **Signing is async too** and may fail recoverably (`SignAndCheckVote` returns
  `(recoverable, err)`), so `:sign` is an effect, not a function call.

**Crypto we do not have.** HoneyBadger needs threshold signatures (coin) and threshold
encryption. geheimnis has Ed25519/AES/RSA/HMAC/HKDF and **no pairing-based crypto**.
Recommendation: skip pairings. Cachin–Kursawe–Shoup threshold PRF for the coin and
Shoup–Gennaro TDH2 for decryption both work under plain DDH on secp256k1/P-256 —
`@noble/curves` on cljs, BouncyCastle on JVM, both exposing the raw group operations that
Web Crypto and `java.security` deliberately hide. ~2–4 person-weeks versus 4–8, and far
faster in a browser. The **coin cannot be descoped** (a local coin gives expected 2^N
rounds); **threshold encryption can** — it buys censorship-resistance, not safety.

---

## 6. Instance addressing

One HoneyBadger ACS round runs **N reliable-broadcasts and N binary-agreements
concurrently**, each ABA with an unbounded sequence of internal rounds, each containing a
binary-value broadcast plus a coin. No other algorithm here needs this.

So events and effects carry an instance address:

```clojure
{:type :instance :instance-id [:rbc 3] :inner {...}}
[:instance {:instance-id [:aba 3] :inner [:broadcast {...}]}]
```

and node state holds `{:instances {iid → sub-state}}` with `step` dispatching. Get this
wrong and **HoneyBadger is not implementable in the framework at all** — which is why it
goes in from day one rather than being retrofitted.

This also subsumes simpler needs: Raft's per-peer `Progress` and Snowman's per-block
snowball instances are the degenerate one-level case.

---

## 7. The deterministic simulator

Layer 0, and the reason the whole design is shaped this way.

```clojure
{:tick 0 :seed 42
 :nodes {peer-id {:node n :state s}}
 :inflight [{:deliver-at t :from p :to q :msg m}]
 :partitions [#{...} #{...}]
 :storage {peer-id {...}}}
```

- **Virtual clock.** Timers are `:after-ticks`; the simulator advances tick by tick.
- **Seeded PRNG.** Every `:sample`, every message delay, every crash point is drawn from
  the seed. A failing run is reproducible from `(seed, schedule)` alone.
- **Adversarial schedules**: drop, delay, reorder, duplicate, partition, heal, crash,
  restart-from-persisted-state.
- **Crash injection** should follow `konserve.simulation.crash`, which already does this
  deterministically (RNG-free, explicit crash points) and is explicitly shipped for
  downstream use. House style already points here.

The simulator is the *only* way algorithms are tested at the property level. Any test that
needs wall-clock time or real sockets is an integration test and lives elsewhere.

---

## 8. Verification strategy

Four tiers, each doing what it is actually good at:

| tier | tool | scope |
|---|---|---|
| pure total functions | **ansatz** | unbounded proof — *and it is the running code* |
| protocol invariants, small instances | **TLC** | automatic, free counterexamples |
| implementation ↔ spec conformance | **trace validation** | reuses the effect log |
| end-to-end histories | **elle** | anomaly detection, pure Clojure |

**Ansatz** (as of 0.2.82) proves the BFT quorum-intersection lemma in floor-division form,
proves reachability invariants over transition systems, handles hard equalities from
`2f+1`/`3f+1`, and has min/max. Remaining gap: Int/BigInt division (`int-mul-gap`), which
matters only for cumulative-work comparison.

Verification targets, in priority order:

1. **`may-sign?`** — at most one prevote and one precommit per (height, round). ~20 lines,
   total, and it is what makes a validator non-slashable. **Do this first.**
2. Quorum arithmetic — done, keep it as a regression.
3. Fork-choice comparison; difficulty retarget and its 4×/¼ clamp; median-time-past;
   compact-target codec roundtrip; the Snowflake confidence update rule.
4. Snowflake's **beta-run characterization** — finalization implies the last β polls were
   all `(≥ alphaConfidence, same choice)`. This is the bridge between the code and the
   paper's probability bound.

**Out of omega's reach — do not chase**: median-time-past is list selection; the
compact-target codec is bit manipulation. Property tests, not omega.

**Standing rule, learned twice the hard way in ansatz:** a green test proves nothing
unless (a) it runs in CI's environment and (b) it asserts through a path that invokes the
kernel. One ansatz suite asserted `proof/solved?`, which never typechecks the term; another
read a gitignored fixture and silently skipped on CI. Both were green for months.

**Conformance corpora available**: etcd-raft `testdata/*.txt` (28 datadriven files, plus
the far easier `quorum/testdata` and `confchange/testdata` which are purely functional);
avalanchego's `snowflake_test.go` (already an implementation-agnostic suite behind a
3-method interface); CometBFT's `TendermintAcc_004_draft.tla` as specification-of-record
with an `action` variable already threaded through every disjunct — and its 37-line
`TendermintAccTrace_004_draft.tla` as the trace-oracle skeleton.

---

## 9. Namespace layout

```
urd.consensus.node          ; the Node protocol, event/effect constructors
urd.consensus.membership    ; Membership protocol + standard instantiations
urd.consensus.runtime       ; effect interpreter (clj + cljs)
urd.consensus.sim           ; deterministic simulator
urd.consensus.network       ; transport protocol (send! + broadcast! + subscribe!)
urd.consensus.networks.{simulation,kabel}
urd.consensus.algorithms.{paxos,raft,tendermint,snowman,nakamoto,bullshark,scp,hbbft}
urd.crypto                  ; edge verification, geheimnis-backed
urd.log                     ; consensus log over konserve
urd.verified.*              ; ansatz-verified pure functions (compile to plain Clojure)
```

---

## 10. Staging

**Phase 0 — honesty.** The current `round_robin` ships `(inc (quot n 2))` (simple
majority, i.e. CFT) while the README claims BFT, and `handle-vote-received` ignores its
`signature` argument entirely while the runtime writes the literal string `"self-vote"`.
Either fix or retract the claims before anything else. This is on Clojars.

**Phase 1 — protocol + simulator.** §2, §3, §6, §7. Port round-robin onto it as a smoke
test, then **single-decree Paxos** — ~100 lines, real safety properties, small enough to
model-check, and a far better shakedown of the API than round-robin.

**Phase 2 — Raft.** Forces durable hard state, unicast, log truncation. Port
`quorum/testdata` and `confchange/testdata` first (purely functional, easy), then the
`raft/testdata` corpus. Unlocks datahike failover.

**Phase 3 — Tendermint.** Multi-phase, locking/valid-round, real BFT quorums. Implement
from the arXiv pseudocode, **not** `spec/consensus/consensus.md` (stale — their own readme
says so) and not from CometBFT's implementation (which diverges: round-skip uses 2f+1, not
the paper's f+1). Use `spec/ivy-proofs/tendermint.ivy` as the line-by-line reference — it
is a mechanically-checked transliteration with the "for the first time" latches made
explicit as `done_l34`/`done_l36`/`done_l47`.

**Phase 4 — Snowman.** Leaderless, sampled, probabilistic. Order:
Snowflake → Snowball → Flat → Topological → Tree. Note `betaVirtuous`/`betaRogue` are gone
upstream, replaced by a single `Beta` plus a termination-condition list; and the Avalanche
DAG consensus has been **deleted** from avalanchego (moved to Snowman in Cortina), so the
paper is the only source for it.

**Phase 5 — Nakamoto.** Open membership, deep reorgs. Mining is `[:mine header target]`
with only a toy miner in-core. Header layer only — the UTXO/script layer is not consensus.
Watch the retarget off-by-one: `first = last.height - (interval - 1)`.

**Phase 6+ — Bullshark, SCP, HoneyBadger.** Bullshark first: it needs **no new crypto**
(substitute a bitmap of Ed25519 signatures for BLS aggregates) and its DAG maps closely
onto yggdrasil. SCP next. HoneyBadger last, gated on the threshold-crypto work in §5.

**Datahike integration** is independent of phases 3+: `datahike.writer/create-writer` is
already a multimethod on `(get-in config [:writer :backend])` with `:self` built in and
`:kabel` registered externally, so urd lands as `(defmethod create-writer :urd ...)` with
**zero changes to datahike core**. For cloud failover, don't Raft-replicate transactions —
with konserve/S3 all nodes already see the same immutable index blocks, so only the branch
head needs agreement. `konserve-s3` already has `put-object-conditional` with an `.ifMatch`
ETag; embed the term in the CAS and a demoted leader is fenced automatically.

---

## 11. Open questions

1. **Vertex identity.** Content-addressed via hasch (aligns with yggdrasil), or
   algorithm-supplied? Leaning content-addressed, but Raft's log entries are
   index-addressed and the mapping needs care.
2. **How much does the core know about vertices?** Fully opaque payloads, or does the core
   own parent links? Bullshark and Nakamoto need the core to walk the DAG; Raft does not.
3. **Bag semantics for `:sample`** — confirmed necessary for avalanchego fidelity, but it
   leaks a fairly specific concept into the general API. Acceptable?
4. **Do we need `:tick` as a distinct input**, or is a timer effect sufficient? HoneyBadger
   needs *no* timers at all, which is a good stress test of the answer.
5. **Reorg depth bounds.** Nakamoto permits unbounded reorgs; datahike's GC will not.
   Where does the bound live — core, or consumer?

---

## 12. Revisions from implementation (2026-08-14, first pass)

Recorded as they were found, so the design stays honest about what survived
contact with code.

**§4 Membership is OPTIONAL, not universal.** Writing Snowman showed the
abstraction does not apply to it at all: Snowman never asks "is this set a
quorum of the validators?", it asks "did alpha of my k SAMPLED peers agree?".
There is no quorum anywhere in the algorithm. A runtime must therefore not
require a `Membership`, and §4's framing ("one protocol, four instantiations")
overstated it -- it is one protocol, three instantiations, and one algorithm
that does not need it.

**A missing input class: external stimulus.** Nothing in §2 covered "an input
that did not arrive over the network and is not a response to an effect" -- a
newly mined block, a client request, an operator command. Added as
`sim/inject` / `inject-all`. A production runtime needs the same seam.

**§1's central justification for `:revert` was WRONG, and this is the most
important correction so far.**

§1 claimed: "revocable commits are not a PoW concession -- Raft needs them too,"
because a new leader makes followers truncate a conflicting uncommitted suffix.
Implementing Raft showed that argument confuses two different things.

A conflicting suffix is *always above the commit index* -- etcd-raft PANICS if a
conflict falls at or below it (`log.go:120-121`), and so does our port. So what
Raft truncates is **uncommitted log entries**, which is a STORAGE concern already
handled by `:persist-then`'s `:truncate-from`. It never revokes a commit.
**Raft does not use `:revert` at all.**

Snowman does not either: its preference flips freely before finalization and
never after.

So the justification for a revocable `:commit` now rests on **Nakamoto alone**,
where a reorg genuinely un-commits previously committed state, plus the weaker
observation that Bullshark commits retroactively (which is additive, not a
revert). The decision to have `:revert` may still be right -- open membership is
in scope, and retrofitting it after five algorithms would be a rewrite -- but it
rests on one algorithm, not three, and it should be re-examined when Nakamoto
lands rather than treated as settled.

The distinction worth carrying forward: **truncating uncommitted state is not
reverting a commit.** Conflating them is what produced the wrong argument.

**Confirmed as designed, with evidence:**

- `:sample` returning a bag is load-bearing (Snowman weights votes by
  multiplicity).
- The `:persist-then` barrier works: the toy decree node's commit lands strictly
  after its durable write, verified in `sim_test`.
- Logical time is enough; nothing has yet wanted wall-clock.
- The simulator caught a genuine agreement violation in a deliberately unsafe
  toy algorithm under 30% message loss, which is the detector working.

**Still unvalidated** (no algorithm has exercised these yet): instance
addressing (needs HoneyBadger), the tri-state `quorum?` (needs SCP),
`:report-equivocation` (needs a Byzantine algorithm), and `:commit` of a
multi-vertex sequence (needs Bullshark).

---

## 13. Revisions after Tendermint and Nakamoto (2026-08-14)

Five algorithms now run on the protocol: Raft, Snowman, Tendermint, Nakamoto, and
round-robin. What each disproved matters more than what each confirmed.

### §1's `:revert` argument was wrong twice, and the primitive still earns its place

The original claim -- "revocable commits are not a PoW concession, Raft needs them
too" -- was wrong: Raft truncates *uncommitted* entries via `:truncate-from`, which
is storage, and never revokes a commit. Snowman never reverts either. That left
Nakamoto as the sole justification, so Nakamoto was implemented to settle it.

**Verdict: keep `:revert`.** A reorg here really is cheap: detaching needs no undo
data at all, so any depth is one `:revert` naming the fork point plus one
`:commit`, and an eighteen-block detach has the same shape as a one-block one.
That is the property §1 predicted from btcd -- at the header layer the undo log is
empty -- and it held.

But three defects came with it:

1. **The simulator recorded reverts and never applied them.** `:committed` was
   append-only, so `agreement?` could not possibly detect a reorg-induced
   divergence: both nodes kept their abandoned branches and stayed unequal
   forever. §12 listed `:revert` as "still unvalidated"; this is what that was
   hiding. **Every reorg test written before this was meaningless.**

2. **`[:revert {:to-vertex v}]` does not carry enough.** An interpreter holds a
   flat sequence with no parent links, so it must SEARCH and truncate. A
   `to-vertex` that was never committed -- the genesis block, where every
   reorg-to-root lands -- is indistinguishable from an unknown one, and both must
   mean "discard everything". **A mistyped id silently wipes committed history.**
   Fix: carry the detached path, which the algorithm has for free
   (`[:revert {:to-vertex v :dropped [...]}]`), or fuse the pair into one
   `[:reorg {...}]`, since neither is ever emitted without the other.

3. **`:index` is under-specified, and the docstring is wrong.** "Globally
   increasing consensus index" and "position in the committed prefix" coincide for
   Raft and Snowman and come apart under a reorg. Only the position is usable by a
   consumer that honours `:revert`.

### `:persist-then` is OPTIONAL, and Nakamoto is the proof

The barrier gates "exactly the messages that constitute this node's binding
commitment". Under proof-of-work a node signs nothing, so that set is empty and the
rule has no left-hand side. Nakamoto uses no barrier at all and is correct. §3
should not read as though every algorithm needs one.

### `Membership` does not apply to three of five algorithms

Snowman samples rather than counting quorums; Nakamoto has open membership and
weighs work; Raft's commit index is a QUANTILE over per-peer values, not a
predicate over attributable statements. It fits Tendermint and Raft's *votes*.
§4's "one protocol, four instantiations" was wrong: it is one protocol, two
instantiations, and three algorithms that do not want it.

Two safety bugs were found in it, both by implementing algorithms rather than by
review: a missing `:validators` key made a single statement a quorum, and counting
statements rather than distinct senders let one Byzantine validator clear a quorum
by repeating itself. A pleasing result in the other direction: Tendermint's L55
round-skip threshold of `f+1` is EXACTLY `v-blocking?` -- `n - byzantine-threshold
= byzantine-tolerance` for every n -- so the abstraction covered a case it was not
designed for.

### The `tick` event is dead

Nothing delivers one. A clock-driven algorithm must arm a repeating timer instead.
Either wire it up or delete it; a documented event no runtime produces is a trap.

### What Tendermint could not express

- **Catch-up / state sync.** A node more than one height behind is stuck forever.
- **Retransmission.** Without a gossip timer *inside* the state machine, 30%
  message loss produces zero progress.
- **Relayed messages.** `:verified-by` assumes point-to-point authentication and
  offers no seam for a third party's message forwarded by a peer -- which makes
  evidence gossip inexpressible. Unicast equivocation is provable but locally
  undetectable.

`report-equivocation` is the right shape -- carrying both statements was natural --
but says nothing about which statement wins (without a rule, a Byzantine node can
retroactively re-vote) or how to stop re-emitting evidence forever.

### Confirmed, with evidence

- The caller-supplied `:token` removed Raft's FIFO workaround entirely; Tendermint
  routinely has two signed writes in flight.
- `:epoch` earns its keep, though for a different hazard in each algorithm than the
  ABA case it was designed for. This is now the third independent appearance of the
  fencing-token pattern, after etcd-raft's term-on-storage-response and datahike's
  Lease & Fence design note.
- `fixpoint` is load-bearing well before SCP.
- `deliver-self` and logical time have held across all five.

## 14. Relationship to datahike's Lease & Fence (design note, Aug 2026)

That design coordinates several datahike instances over one konserve store with no
coordination server: safety from a compare-and-swap on the branch head (store
state, never a clock), liveness from a heartbeat lease that is explicitly allowed
to be wrong.

**It does not need urd, and should not wait for it.** Its strength is avoiding
consensus. Independently, this project reached the same shape for datahike cloud
failover -- do not replicate transactions, since konserve/S3 already gives every
node the same immutable index blocks, so only the branch head needs agreement, with
the term embedded in the CAS so a demoted leader is fenced. Two independent
derivations agreeing is worth more than either.

Where urd genuinely relates, in decreasing confidence:

1. **As the optional lease provider they leave a slot for.** They reject
   Redis/ZooKeeper/etcd as "standing infrastructure" but keep the door open. An
   embedded Clojure Raft is that, without the objection. Layer 2 only; the fence
   stays underneath.
2. **When the store cannot do CAS** -- their own fallback is "degrade to
   lease-only, with a loudly documented weaker guarantee". Consensus supplies the
   fence the store cannot.
3. **Their non-goals are consensus-shaped**: cross-store replication, active-active
   multi-region, surviving the store's outage. All lack a single arbiter to CAS
   against.

**One caution.** Their Layer 3 -- floating transactor: leader election,
`:owner-address` discovery, kabel forwarding -- is the problem urd solves. Building
both puts two leader-election implementations in one stack that can silently
disagree, which is the failure mode this project hit in ansatz's two omegas and
urd's two quorum functions. Layers 0-2 are complementary; Layer 3 is a fork.

Worth taking FROM them: the `:db.tx/forward-id` dedup token resolved by walking the
commit graph across the ambiguity window is a good answer to the in-flight-RPC
problem urd's client interface will face. And "an acked-but-uncommitted transaction
is a durability lie that dies with the pod" states our barrier's principle better
than §3 does.

## 15. A standing rule, learned five times

Every one of these was green for the wrong reason:

- ansatz tests asserting `proof/solved?`, which never typechecks the term;
- an ansatz suite reading a gitignored fixture, so CI silently skipped the
  motivating theorem;
- `restart-discards-in-memory-state` passing because `:durable` was never written;
- a portability claim with no JavaScript runtime to test it;
- `agreement?` unable to see a reorg, because `:revert` was recorded and not
  applied.

**A guard is only a guard once you have watched it fail.** Before trusting a check,
make it fail on purpose.
