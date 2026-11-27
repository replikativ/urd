# The Node protocol

Everything in urd rests on one idea: **a consensus algorithm is a pure
function, and everything it wants done is a value.**

```clojure
(step node state input) ;; => {:state new-state :effects [...]}
```

No clock. No I/O. No randomness. No `println`. A node that wants a timer emits
`[:set-timer {...}]`; a node that wants to persist emits `[:persist-then {...}]`
and does not continue until it is told the write landed. Something else — an
*interpreter* — does the work.

That constraint is what buys the two properties urd is built on: the same
algorithm runs unchanged under a deterministic simulator and under a real
runtime, and a failing schedule in the first is meaningful about the second.

## The protocol

`urd.consensus.node/Node` has three methods.

**`(init node config)` → `{:state _ :effects _}`.** Effects at init are not
unusual — a node commonly arms its first timer or restores durable state here,
and both interpreters run them immediately.

**`(step node state input)` → `{:state _ :effects _}`.** May run an internal
fixpoint before returning: SCP needs one, because a single statement can
cascade through federated voting. May also commit with no effects at all —
Bullshark orders a whole sub-DAG from one certificate arriving.

**`(capabilities node)` → `{:emits #{...} :topics #{...}}`.** Required, not
optional, and enforced by both interpreters.

## Inputs

`urd.consensus.node` defines the following inputs.

| input | meaning |
|---|---|
| `message-received` | an **authenticated** message; carries `:verified-by` |
| `timer-fired` | a timer id; ticks, never milliseconds |
| `sampled` | the result of a poll — a **bag**, not a set |
| `persisted` | a durable write landed; carries an epoch |
| `durable-values` | the requested keys found in retained local storage, tagged with the request token |
| `value-ready` | the application answered `:request-value` |
| `vertex-received` | a DAG vertex arrived and was authenticated |

Two of these repay a close reading.

`:verified-by` is a **set of peer ids whose signature was actually checked**,
supplied by the verification edge, not by the sender. It used to be
`#{(:sender msg)}` — a field the sender writes — which meant every Byzantine
property urd proved was conditional on an authenticated transport that did not
exist. Algorithms that care check membership in this set.

`sampled` is a bag because multiplicity is meaningful: a node drawn twice
counts twice. Snowman supplies the configured voting powers to both interpreters.

## Effects

`node/all-effects` is the canonical set.

**Communication** — `send-to`, `broadcast`, `deliver-self`.

`deliver-self` is not `send-to` addressed at yourself. etcd-raft has the same
construct for the same reason: a leader appending to its own log must observe
that append in the same causal position every follower does, and routing it
through the network would put it somewhere else.

**Historical lookup** — `(n/read-durable token ks)` requests the latest landed
values for explicit keys. The `:durable-values` response carries the token and
the values found. A failed optional lookup returns an empty map. Bullshark uses
this effect to answer requests beyond its in-memory retention window.

**Durability** — `persist-then`.

**Sampling** — `sample`. **Timers** — `set-timer`, `cancel-timer`.

**Application** — `request-value`, `commit`, `resync`, `revert`.

**Reporting** — `report-equivocation`, `log-effect`.

## The durability barrier

`persist-then` is the most load-bearing effect and the least obvious:

```clojure
[:persist-then {:writes {...}          ; what to write
                :durable? true         ; fsync, or merely buffered
                :epoch 7               ; defeats an ABA hazard
                :then [...]            ; effects gated behind the write
                :token ...             ; opaque, echoed back
                :truncate-from 42      ; log truncation
                :checkpoint [...]}]    ; REPLACES, does not extend
```

The rule — *gate exactly the messages that constitute this node's binding
commitment* — was arrived at independently by etcd-raft and CometBFT, and the
docstring cites both. A vote that reaches a peer before it reaches the disk is
a vote a crash can un-cast, and that is how a Byzantine-safe algorithm equivocates
by accident.

`:epoch` exists because a naive completion signal has an ABA hazard: a write
completing after a restart could be mistaken for a write issued before it.

## Commit, revert, resync

Three ways the committed prefix moves, and they are not interchangeable.

`commit` takes an **ordered sequence** and carries **no index**. It used to
carry one; the removal is documented at length, and the short version is that
an index invites the interpreter to reorder or deduplicate, which is precisely
what it must not do.

`revert` requires `:dropped` — what the node believes it is taking back — and
an interpreter *should* reject a mismatch rather than trusting it. The
simulator throws.

`resync` is **not** a revert. It is wholesale replacement, used when a node has
been told authoritative state rather than having reconsidered its own.

## Capabilities

```clojure
(capabilities [_] {:emits #{:broadcast :set-timer :commit :log}
                   :topics #{:consensus}})
```

Both interpreters validate at registration and refuse any effect or topic the
node did not declare. This is not ceremony. The runtime's subscription list was
once round-robin's, hardcoded, so every other algorithm subscribed to topics it
never used and none to the ones it did — silently, because an unsubscribed
topic simply never delivers.

Topics are per-algorithm and disjoint: round-robin uses
`#{:proposals :votes :finalizations :recovery}`, Tendermint `#{:consensus}`,
SCP `#{:scp}`, Bullshark `#{:bullshark}`, Nakamoto `#{:headers}` — and Raft and
Snowman do not broadcast at all.

## Membership: trust as a protocol

`node/Membership` abstracts "is this set enough". It has three methods —
`quorum?` (**tri-state**: yes, no, or *not enough information*), `v-blocking?`
(local, not global) and `weight`.

Three implementations: `ThresholdMembership` (counts, or weights),
`tendermint/PowerWeightedBft` (voting power), `scp/FbaMembership` (quorum
slices, computed as a greatest fixpoint — there is no global validator set at
all).

The tri-state matters because in a federated system "not a quorum" and "I
cannot tell yet" are different answers with different correct responses.

> Two docstrings here — `total-weight` and `ThresholdMembership/weight` — record
> a **safety hole caused by measuring the two sides of a comparison
> differently**. They are worth reading before you write a `Membership`.

## Writing one

```clojure
(reify node/Node
  (capabilities [_] {:emits #{:set-timer :commit :log}})
  (init [_ cfg]  (node/result {:h 0} [(node/set-timer :tick 1)]))
  (step [_ st _] (node/result (update st :h inc)
                              [(node/commit [{:h (:h st)}])
                               (node/set-timer :tick 1)])))
```

`node/result` builds the return map; `node/add-effects` appends; `node/fixpoint`
runs a step to convergence with a bound of 100 iterations.

Anything satisfying this protocol runs in the simulator and the runtime alike —
which is how the Byzantine test suites work: an adversary is an ordinary `Node`
that wraps an honest one and rewrites its outbound effects.
