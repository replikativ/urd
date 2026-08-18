# Algorithms

Seven implementations of `urd.consensus.node/Node`. Each is a port, each was
read against its reference implementation as well as its paper, and each
documents where it departs and why.

`snowtree` and `snowflake` are **not** `Node`s: they are the Snowball patricia
trie and the Slush/Snowflake/Snowball primitives that Snowman is built from.

## Choosing

| | faults | quorum | over | durable | set changes | maturity |
|---|---|---|---|---|---|---|
| **tendermint** | Byzantine | `2f+1` | **voting power** | yes | yes, height+1 | deployment candidate |
| **raft** | crash | majority | head count | yes | yes, joint consensus | deployment candidate |
| **round-robin** | crash | majority | head count | **no** | yes, next height | reference |
| **bullshark** | Byzantine | `2f+1` | **stake** | yes | refuses | reference-grade |
| **scp** | Byzantine, federated | quorum slices | per-node slices | yes | n/a | reference-grade |
| **snowman** | probabilistic | sampling | n/a | **no** | no | stress test |
| **nakamoto** | open membership | cumulative work | n/a | yes | n/a | generality test |

Two thresholds appear throughout and are **not** interchangeable:
`majority-threshold` is `floor(n/2)+1`, `byzantine-threshold` is
`floor(2n/3)+1`. They coincide at n=4 and diverge from n=5 on. A generative
test pins the distinction so that nobody "fixes" one to match the other.

## Tendermint

Byzantine, absolutely final below n/3. The strongest candidate here for real
use: durable WAL, a double-sign guard restored from its own register, validator
set changes, proposer priorities ported from CometBFT, and a dedicated
adversarial test suite.

Quorum is over **voting power**, not head count — `node/threshold-membership`
is deliberately unusable with it.

**It implements the paper, not CometBFT.** Two knowing divergences: CometBFT
skips rounds on `2f+1` where the paper uses `f+1`, and its L28 unlock happens
inside `addVote` rather than as a prevote rule.

Set changes activate at **height + 1**. That offset is pinned by a test that
verifies it *by mutation* — shifting it passes every other test in the suite.

Out of scope: the WAL replay is narrower than CometBFT's, which replays received
messages too. That is a liveness cost after a restart, never a safety one.

## Raft

Crash-fault, absolutely final, ported from `etcd-io/raft`. PreVote, log
replication with per-peer progress, durable hard state, log truncation on a
conflicting suffix, and **membership changes including joint consensus**.

Quorum is a head-count majority and unweighted by construction — Raft has no
notion of stake.

Out of scope: snapshots, leadership transfer, read-index/lease reads,
CheckQuorum, inflight flow control.

Unlike etcd, urd's Raft does not use a self-addressed message for local
appends; it uses the `deliver-self` effect, which puts the append in the same
causal position every follower observes.

## Round-robin

A rotating single proposer with majority voting. **Keeps no durable state at
all** — no `persist-then` anywhere — which is a real limitation stated in its
own docstring, and why it is a reference rather than a deployment candidate.

The safety argument is worth understanding because it explains the constraints:
the proposer is `(mod height (count validators))` over the **sorted** ids, so
there is at most one proposal per height ever, which is what makes a *majority*
quorum safe without any locking. A set change reindexes that rotation, which is
why nodes disagreeing about the set even briefly would break it.

> **Values must carry `:snapshot-id`.** That is what identifies a proposal. A
> value without one has a nil id and the cluster commits nothing, silently.

## Narwhal-Bullshark

A certified DAG mempool with a zero-message ordering layer. Quorum is over
**stake**. Byzantine-safe via `2f+1`-stake certificates.

**Refuses validator set changes, loudly** — which is the honest answer rather
than a silent approximation, since the DAG's certificate history is over a
fixed committee.

One deliberate code divergence: `order-anchors` follows the *papers*, not
narwhal's implementation, whose bug is invisible to its own tests because
`#[cfg(test)]` makes the leader function constant.

Out of scope: BLS signature aggregation.

## SCP

Federated Byzantine Agreement. There is no global validator set: each node
declares quorum slices, and "quorum" is a **greatest fixpoint** over them.
Finality holds only *between intertwined nodes* — that is the model, not a
limitation of the port.

It refuses a flat `:validators` config, because accepting one would silently
turn FBA into ordinary BFT.

Three documented divergences from stellar-core, the sharpest being that
stellar-core's `if (n < targetCounter) break;` means one lagging peer aborts the
whole counter scan; urd follows §5.4 of the draft instead.

Out of scope: catch-up.

## Snowman

Leaderless consensus by repeated sampling, parameterised by `k`, `α`, `β`.
No quorum and no `Membership` — the safety argument is probabilistic.

It exists to **stress the opposite corner of the protocol** from Tendermint: no
leader, no rounds, no durable state, decisions that are statistical rather than
absolute. If the `Node` protocol can express both, it is general.

`snowtree` is the patricia trie avalanchego actually runs under Snowman;
`snowflake` holds the Slush/Snowflake/Snowball primitives, where Snowball is
explicitly reference material rather than production behaviour.

## Nakamoto

The Bitcoin **header** layer: proof of work, cumulative work with a strict `>`
tie-break, reorgs. Open membership, so `Membership` does not apply at all.

**In the portfolio as a generality test, not a product.** Checkpoints are
dropped on purpose — a checkpoint is exactly a violation of the open membership
this algorithm exists to test.

It is the only algorithm here that emits `:revert`, which is why the effect
exists.

## A note on reading these

The namespace docstrings are the primary source and are unusually detailed:
they cite the file and line of the reference implementation they were read
against, name the divergences, and in several cases record the measured failure
that prompted a change. Where this page and a docstring disagree, the docstring
is authoritative — and please open an issue, because it means this page rotted.
