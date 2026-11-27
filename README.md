# Urd

<p align="center">
<a href="https://clojurians.slack.com/archives/CB7GJAN0L"><img src="https://badgen.net/badge/-/slack?icon=slack&label"/></a>
<a href="https://clojars.org/org.replikativ/urd"><img src="https://img.shields.io/clojars/v/org.replikativ/urd.svg"/></a>
<a href="https://circleci.com/gh/replikativ/urd"><img src="https://circleci.com/gh/replikativ/urd.svg?style=shield"/></a>
<a href="https://github.com/replikativ/urd/tree/main"><img src="https://img.shields.io/github/last-commit/replikativ/urd/main"/></a>
</p>

**Seven consensus algorithms, one protocol, and a simulator that makes the
hard failures cheap to test.**

Urd implements Tendermint, Raft, Narwhal-Bullshark, Nakamoto, Snowman, SCP and
a round-robin reference as **pure state machines** behind a single protocol.
A node is `(step state input) -> {:state _ :effects _}`: no clock, no I/O, no
randomness. Everything a node wants done is a value, and something else does
it — which is why the same algorithm runs unchanged under a deterministic
simulator and under a real runtime with sockets and disks.

In Norse myth Urðr is the Norn of what has become, and Urðarbrunnr the well
where the gods hold council. Consensus is the same question: what has become,
and who agrees.

Portable Clojure and ClojureScript. Part of the
[replikativ](https://github.com/replikativ) stack.

## Status

Urd is experimental. The JVM, Node and real-network suites exercise the
implementations, and the proof suite checks the signing order and quorum
arithmetic. Each algorithm has its own deployment assumptions.

- **Raft** is the first beta target for crash faults. It supports joint
  membership and local checkpoints. A follower or application behind the
  retained log needs an external snapshot. A legacy compacted store requires
  the authoritative voter configuration for recovery.
- **Tendermint** supports weighted Byzantine voting, durable locks and
  certificate-based catch-up. Applications using map proposals with an
  explicit `:id` must verify that the ID binds the entire payload, including
  any validator updates. Build a proposal with
  `(assoc payload :id (tm/content-id payload))` and configure every validator
  with `:valid-fn (every-pred tm/valid-content-id? application-valid?)`,
  where `tm` names `urd.consensus.algorithms.tendermint`.
- **Round-robin** is a crash-fault reference with volatile votes.
- **Nakamoto** implements header-chain selection and exposes reversible commits.
- **Snowman**, **SCP** and **Bullshark** are reference implementations for
  protocol experiments and simulation.

Cryptography is real. `urd.consensus.auth` is Ed25519 over canonical CBOR and
the runtime verifies every inbound message; `:auth` is a required argument, and
opting out means typing `:none`. The toy attestation schemes in each algorithm
are labelled NOT CRYPTOGRAPHY in capitals, and `urd.consensus.attest` is the
real one.

## Installation

```clojure
org.replikativ/urd {:mvn/version "RELEASE"}
```

## Quick start

Four Tendermint nodes, in a deterministic simulator. No network, no store, no
keys.

```clojure
(require '[urd.consensus.sim :as sim]
         '[urd.consensus.algorithms.tendermint :as tm])

(def peers [:a :b :c :d])

(defn cluster []
  (sim/make {:seed 7
             :nodes (zipmap peers (repeat (tm/make)))
             :config {:value-fn (fn [_sim peer ctx]
                                  {:id [:block peer (:height ctx)]})}}))

(def s (sim/run (cluster) 200))

(count (sim/committed s :a))   ;; => 21
(first (sim/committed s :a))   ;; => {:id [:block :a 0]}
(sim/agreement? s)             ;; => true
```

`sim/make` needs only `:nodes` — it derives the validator set from the node
keys. `:value-fn` answers the `:request-value` effect; without one, every node
is handed `{:payload :none}`.

Now break it. A minority partition, then a crash and restart:

```clojure
(-> (cluster) (sim/run 40)
    (sim/partition-network [#{:a :b :c} #{:d}]) (sim/run 60)
    sim/heal (sim/run 60)
    sim/agreement?)                              ;; => true

(-> (cluster) (sim/run 40)
    (sim/crash :b) (sim/run 40)
    (sim/restart :b) (sim/run 80)
    sim/agreement?)                              ;; => true
```

Every block above is executed by
[`test/urd/readme_test.clj`](test/urd/readme_test.clj) on every run. This
README used to open with six calls to functions that had been deleted months
earlier; prose about code drifts silently, and a test does not.

> **One trap worth knowing.** With **round-robin**, the value must carry
> `:snapshot-id` — that is what identifies a proposal. A value without one has
> a nil id, every guard declines, and the cluster commits *nothing*, with no
> error and no log line. Tendermint has no such requirement. This is pinned by
> a test.

## Which algorithm?

| | faults | quorum | durable | set changes | maturity |
|---|---|---|---|---|---|
| **tendermint** | Byzantine | 2f+1 by **voting power** | yes | yes, at height+1 | deployment candidate |
| **raft** | crash | majority, head count | yes | yes, joint consensus | deployment candidate (CFT) |
| **round-robin** | crash | majority, head count | **no** | yes, next height | reference |
| **bullshark** | Byzantine | 2f+1 by **stake** | yes | refuses, loudly | reference-grade |
| **scp** | Byzantine, federated | quorum slices | yes | n/a | reference-grade |
| **snowman** | Byzantine, probabilistic | sampling (k/α/β) | no | no | protocol stress test |
| **nakamoto** | open membership | cumulative work | yes | n/a | generality test |

`snowtree` and `snowflake` are not algorithms in this sense — they are the
Snowball trie and the Slush/Snowflake/Snowball primitives that Snowman uses.

Full detail, including each implementation's deliberate divergences from its
reference, is in [doc/algorithms.md](doc/algorithms.md).

## Documentation

- [The Node protocol](doc/node-protocol.md) — pure `step`, thirteen effects,
  the durability barrier, capability declarations
- [Algorithms](doc/algorithms.md) — the seven in depth, and where each departs
  from its paper or its reference implementation, with reasons
- [The simulator](doc/simulator.md) — partitions, crashes, restarts, bandwidth,
  Byzantine adversaries, and schedules as shrinkable data
- [The runtime](doc/runtime.md) — running a node for real: network, storage,
  auth, timers, callbacks
- [Security](doc/security.md) — what each signature covers, replay protection,
  vote attestations, commit certificates, the double-sign guard
- [Wire format](doc/wire-format.md) — canonical CBOR, keyword tag 39, framing
- [Validator sets](doc/validator-sets.md) — reconfiguration and when changes
  activate, per algorithm
- [Portability](doc/portability.md) — what runs where, what is JVM-only and why
- [Interop](doc/interop/README.md) — talking to urd from another language

API documentation is on [cljdoc](https://cljdoc.org/d/org.replikativ/urd).

## Testing

```bash
clj -M:test                              # JVM unit and property tests
clj -M:integration                       # real sockets, real handshakes
clj -M:cljs-test && node target/cljs-test.js   # portable tests under Node
clj -M:storage-sim                       # konserve's crash simulator
clj -M:proofs                            # theorems and implementation correspondence
bin/test-all                             # all of the above, sequentially
```

`:integration` is excluded from the default run on purpose: those tests stand
up real WebSocket servers and their outcome depends on machine load. A suite
whose result varies run to run cannot tell you whether a change was safe.

## Design principles

**Effects are values.** A node returns what it wants done; an interpreter does
it. This is what makes two interpreters possible, and the second one is not a
luxury — it found three bugs the simulator structurally could not, because the
simulator has no wall clock, no core.async, and no orphaned timers.

**Capabilities are declared and enforced.** A node states which effects it
emits and which topics it uses, and both interpreters refuse anything else. A
typo cannot silently narrow what a node is allowed to do.

**Refusing is a choice you have to make.** `:auth` has no default. A node that
cannot verify its peers should refuse to start, not start and trust them.

**Some things are proved, not tested.** The double-sign guard and quorum
intersection are machine-checked in
[ansatz](https://github.com/replikativ/ansatz) — five theorems over Nat —
and `clj -M:proofs` re-checks them along with a differential test that the
shipped copies still match the verified definitions. Ansatz is not a runtime
dependency: it erases proofs and emits ordinary Clojure.

**Every divergence is documented where it lives.** Where this code departs from
CometBFT, etcd-raft, narwhal or stellar-core, the docstring says so and says
why — usually with the file and line of the reference it was read against, and
sometimes with the measured failure that prompted it.

## Related

[datahike](https://github.com/replikativ/datahike) ·
[konserve](https://github.com/replikativ/konserve) ·
[kabel](https://github.com/replikativ/kabel) ·
[geheimnis](https://github.com/replikativ/geheimnis) ·
[boring](https://github.com/replikativ/boring) ·
[skuld](https://github.com/replikativ/skuld) — a ledger built on urd

## References

Tendermint: [The latest gossip on BFT consensus](https://arxiv.org/abs/1807.04938) ·
Raft: [In Search of an Understandable Consensus Algorithm](https://raft.github.io/raft.pdf) ·
Narwhal-Bullshark: [Narwhal and Tusk](https://arxiv.org/abs/2105.11827),
[Bullshark](https://arxiv.org/abs/2201.05677) ·
Avalanche: [Snowflake to Avalanche](https://www.avalabs.org/whitepapers) ·
SCP: [The Stellar Consensus Protocol](https://stellar.org/papers/stellar-consensus-protocol) ·
Bitcoin: [Nakamoto](https://bitcoin.org/bitcoin.pdf)

## License

Copyright © 2026 Christian Weilbach. Distributed under the Eclipse Public
License 2.0.
