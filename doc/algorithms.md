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
| **round-robin** | crash | majority | head count | yes | yes, next height | reference |
| **bullshark** | Byzantine | `2f+1` | **stake** | yes | refuses | reference-grade |
| **scp** | Byzantine, federated | quorum slices | per-node slices | yes | n/a | reference-grade |
| **snowman** | probabilistic | weighted sampling | stake | accepted chain | no | stress test |
| **nakamoto** | open membership | cumulative work | n/a | yes | n/a | generality test |

Two thresholds appear throughout and are **not** interchangeable:
`majority-threshold` is `floor(n/2)+1`, `byzantine-threshold` is
`floor(2n/3)+1`. They coincide at n=4 and diverge from n=5 on. A generative
test pins the distinction so that nobody "fixes" one to match the other.

## Running a validator over time

The consensus WAL, the application's database, and the history served to peers
have different retention requirements. Size each window for the expected write
rate and maximum offline time. Keep a durable application cursor alongside the
state it describes. The following costs refer to an ordinary validator on this
implementation. A WAL record or certificate can contain many votes or parents.

| Algorithm | What grows and what recovery reads | Difference from the reference |
|---|---|---|
| Raft | Compaction retains an applied window plus the unapplied suffix. Inside the window a follower receives missing entries. Beyond it, install an authenticated application snapshot and its term, index and membership together. | etcd-raft can send a snapshot through its host. Urd requires an offline install and then verifies the boundary through ordinary replication. |
| Tendermint | The defaults keep 1,000 decision heights and checkpoint every 100 decided heights. Each retained certificate can contain one signature per validator. A deep restore needs the committee, powers and proposer priorities at the application cursor, plus the recovering node’s own signing state. | CometBFT provides indexed commit history and state-sync machinery. Urd serves retained evidence and expects the host to install a trusted boundary beyond that window. |
| Round-robin | Restart scans the full decision WAL even when the application needs only one decision. Peer recovery serves a bounded window. | The original Urd prototype kept votes in memory. The current version persists the voting fence and history. An unavailable assigned proposer can still stall a height. |
| Bullshark | The live DAG is pruned. Startup replays local certificate history. An optional archive lookup scans the full retained WAL once per batch of missing digests. | Narwhal has keyed certificate storage and resumes ordering from persisted progress. Old-peer catch-up in Urd costs more as the archive grows. |
| Snowman | Each poll samples up to `k` peers. Selecting `k` stake units can take `O(kN)` work for `N` validators. Ordinary recovery rebuilds the accepted history since the stored root and keeps those blocks addressable in memory. | AvalancheGo separates the live processing tree from the VM’s historical block store. Urd can start from a trusted frontier but does not advance it automatically to bound history. |
| Nakamoto | For `B` retained connected headers, including forks, a checkpoint sorts `B` headers and writes all of them. Forward sync sends up to 128 headers per reply. | btcd maintains an incremental block index. In Urd, checkpoint write volume rises with the size of the index even when all peers are current. |
| SCP | Local recovery resumes persisted slot state. Quorum evaluation depends on the topology and size of the quorum sets. Bounding the set cache does not supply a ledger history to an offline peer. | Stellar Core combines SCP with history archives and ledger catch-up. A Urd application must supply that recovery path. |

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

For state transfer, install the authenticated consensus boundary for the last applied
height alongside the application snapshot. Its fields are `:decided-through`,
`:post-activation?`, `:validators`, `:powers`, and `:priorities` as written by
the end-height record. Keep the joining validator’s own signing state. A ledger
count alone cannot reconstruct earlier membership changes or proposer priorities.

Each signed write also records the current lock. A legacy validator whose WAL
has been lost and whose signing register is ahead of replay waits for a decision
before signing at a later height. Authenticated peers can relay retained commit
certificates across membership changes. Validators check the signatures using
the set for the certificate’s height. Configure the authenticator and vote-key
resolver with the historical public keys needed for that check.

## Raft

Crash-fault, absolutely final, ported from `etcd-io/raft`. PreVote, log
replication with per-peer progress, durable hard state, log truncation on a
conflicting suffix, and **membership changes including joint consensus**.

Quorum is a head-count majority and unweighted by construction — Raft has no
notion of stake.

Raft supports offline checkpoint installation. Stop the recovering peer.
Obtain and authenticate an application snapshot and its consensus checkpoint
from the same committed index, including the term at the boundary and the
voter configuration there. Keep the recovering peer’s own election term,
vote, signing identity and replay registers. Stage the replacement offline,
verify the application cursor and consensus boundary agree, and switch to the
complete store before restarting. A leader verifies the reported boundary
through ordinary log replication before advancing follower progress.
Snapshot transfer is external. Leadership transfer, read-index/lease reads,
CheckQuorum and inflight flow control are outside this implementation.

Unlike etcd, urd's Raft does not use a self-addressed message for local
appends; it uses the `deliver-self` effect, which puts the append in the same
causal position every follower observes.

## Round-robin

A rotating single proposer with majority voting. Before broadcasting a new
proposal or vote, answering recovery queries about it, or publishing a
decision, the node waits for its durable write. The versioned WAL stores
the selected proposal, local vote, decisions, roster, and retained handover
witnesses. On restart it resumes the outstanding proposal and uses the
signing, verification and validity callbacks supplied at startup. These
callbacks must be pure and must keep signatures private until the node
publishes them. A durable store is required for recovery across process loss.

Use the application's durable `:delivered-through` count to replay the
missing suffix. Without a cursor, a recovered node emits `:resync` with
its full prefix. The WAL grows with local decision history. Peer recovery
serves the configured `:finalized-retention` window. A permanently unavailable
proposer can still halt the chain at its assigned height.

Older releases kept no record of a vote or proposal. An application cursor
alone cannot establish that an existing identity is safe to reuse. Start the
new version at genesis or restore its complete versioned WAL. Set
`:require-round-robin-history? true` on an existing identity to refuse startup
when the store has no such history, including when the application cursor
is zero. Leave that option unset for first startup of a fresh identity.

A finalizing member signs the height and the full proposal, including any
membership change. A new roster can relay that attestation during recovery.
The receiver checks the signer against the roster at the decision height.
Custom attestation callbacks must sign and verify the complete payload for
both votes and finalization witnesses. Recovery across a full turnover requires
the retained decisions and verification keys for their historical members.
Updated nodes accept earlier message formats from a member of the roster at
the decision height. Upgrade the old roster before handing off to a disjoint
roster so its decisions carry witnesses that the new members can relay.

UUID validator IDs sort by canonical UUID text on both platforms. Coordinate
the upgrade for active UUID rosters whose order differed on older JVM nodes.
The same ordering applies to Bullshark anchor selection.

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

Stake must be a positive integer for each validator, with a total of at most
4,294,967,295. Parent digests travel as a set. Each peer serves retained
certificates from memory for `:store-depth` rounds, which must exceed
`:gc-depth`. Set `:archive-catchup? true` on a responder to serve older
certificates from its retained durable history. Without an archive responder
holding the missing parents, a peer behind every memory window needs external
bootstrap history. Recovery replays the locally persisted certificate history.

An archive responder starts at most one log scan per gossip tick, with one
scan in flight. It rotates through requesting validators in arrival order and
keeps one pending batch per validator, each holding at most one digest per
committee member. For a committee of N, queued digests occupy O(N²) space
and each scan returns at most N certificates. The durable store reads its
entire retained log per batch and can delay writes while it scans. Historical
replies go through the receiving validator’s usual certificate checks.

The archive records its ordering version. For legacy UUID rosters whose JVM
and JavaScript orders differ, or stake totals above 2,147,483,647, provide an
explicit `:anchor-fn` reproducing the chain’s historical schedule on every
node before replay. Keep that schedule for the chain’s lifetime. An archive
containing earlier non-set parent representations needs reconciliation against
the application's committed prefix before it can be replayed.

The certificate covers the inline payload. When the payload contains snapshot
IDs, the application provides availability of the referenced snapshots.
BLS signature aggregation is outside this implementation’s scope.

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

Set `:valid-fn` to the deterministic application predicate for this slot. The
default accepts non-nil values. The predicate covers nominations, composite
candidates, and ballot values including prepared ballots.

A node can nominate up to 256 distinct values per slot. Accepting a value it
already nominated retains that value in both sets. Once the limit is reached,
the node continues voting on those values. Federations expecting more competing
values should bound proposal diversity at the application layer. The node pins
configured quorum sets and retains up to `:qset-cache-limit` fetched sets
(default 1000). Size the cache for the active federation.

Out of scope: catch-up.

## Snowman

Leaderless consensus by repeated sampling, parameterised by `k`, `α`, `β`.
No quorum and no `Membership` — the safety argument is probabilistic.

Accepted blocks are written to the WAL before delivery. On restart the node
rebuilds its accepted chain and uses the application's `:delivered-through`
cursor to deliver the missing suffix. The WAL grows with accepted history.
An externally restored application can supply a trusted `:accepted-frontier`
with the matching block ID and height.

Remote blocks use a content ID over canonical CBOR by default. Applications
with their own ID scheme supply a deterministic `:verify-block` predicate
that verifies both the binding and application validity. Validator sampling
uses the configured `:powers`, including the local validator’s stake.

`snowtree` implements the Patricia trie. Its default preserves the derived
keys used by earlier deployments. For native 256-bit hexadecimal block IDs,
`:params {:tree-key-mode :avalanche}` selects AvalancheGo’s bit order.
`snowflake` also includes the Slush, Snowflake and Snowball primitives.

## Nakamoto

The Bitcoin **header** layer: proof of work, cumulative work with a strict `>`
tie-break, reorgs. Open membership, so `Membership` does not apply at all.

**In the portfolio as a generality test, not a product.** Checkpoints are
dropped on purpose — a checkpoint is exactly a violation of the open membership
this algorithm exists to test.

An unknown tip triggers a `:get-header` request carrying up to 64 recent and
exponentially spaced ancestor IDs. A peer sharing an ancestor on its best
chain sends up to 128 headers in forward order. Each header passes the ordinary
proof, difficulty, and timestamp checks. A repeated announcement retries a lost
page, including when the downloaded fork has yet to outweigh the local tip.
Older peers and requests for side-branch parents use the single-header response.

It is the only algorithm here that emits `:revert`, which is why the effect
exists.

## A note on reading these

The namespace docstrings are the primary source and are unusually detailed:
they cite the file and line of the reference implementation they were read
against, name the divergences, and in several cases record the measured failure
that prompted a change. Where this page and a docstring disagree, the docstring
is authoritative — and please open an issue, because it means this page rotted.
