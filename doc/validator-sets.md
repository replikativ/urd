# Validator sets

Changing who votes is three separate questions, and only the middle one
generalises:

```
TRIGGER      what caused the change            application's business
TRANSITION   config + updates -> new config    urd.consensus.reconfig
ACTIVATION   when it takes effect              the algorithm's business
```

`urd.consensus.reconfig` was written after reading four references — CometBFT,
etcd-raft, Narwhal and stellar-core — which gave four different answers. It is
deliberately only their **intersection**.

## The transition

An update is `{:id peer :power n}`, with **power 0 meaning removal** — CometBFT's
`ValidatorUpdate` shape.

```clojure
(reconfig/validate config updates)      ; five named rejections
(reconfig/apply-updates config updates) ; => new config, or {:error ...}
```

A sparse diff rather than a replacement, following both CometBFT and etcd. The
cost of a diff is that it can be invalid in ways a replacement cannot — hence
`validate`.

## Order independence is a safety property

`canonical` deduplicates and then sorts before anything else looks at the
updates. This is not tidiness: **CometBFT issue #3181** was two honest nodes
computing different proposer priorities because the updates arrived in a
different order in the ABCI response. The fix was consensus-breaking.

A generative test runs 200 cases asserting order independence.

## Rejection is data, not an exception

An invalid update returns `{:error ...}` and **the set does not change**. Halt
and skip are both defensible; what is not defensible is two nodes classifying
the same update differently.

Validity is a function of `(config, updates)` and nothing else — deliberately,
because etcd validated against whatever configuration happened to be active at
propose time, and the resulting divergence between believed and actual config
caused real data corruption in CockroachDB.

## Activation, per algorithm

| | when | note |
|---|---|---|
| **tendermint** | height **+1** | pinned by a mutation test |
| **raft** | on config entry apply | joint consensus for arbitrary changes |
| **round-robin** | next height | reindexes the proposer rotation |
| **bullshark** | — | **refuses**, loudly |
| **scp** | — | not applicable: no global set |
| **snowman**, **nakamoto** | — | not applicable |

Tendermint's +1 rather than CometBFT's +2 is structural, not preference:
CometBFT's first +1 is *forced* because a block header is built from
pre-execution state, so the result of deciding H cannot appear in H's own
header. urd has no header — the decided value *is* the value.

**Round-robin is the most sensitive.** Its proposer is
`(mod height (count validators))` over the sorted ids, and that is its whole
safety argument: exactly one proposal per height, so two values cannot both
reach a majority without locking. If two nodes disagree about the set at height
H they compute *different* proposers, and that premise is gone.

## Joiners cannot propose immediately

A joining validator gets a priority of `-(P + P>>3)`. This is CometBFT's rule
and it does two things: a new validator cannot propose the moment it joins, and
it cannot clear a negative priority by unbonding and rebonding.

## Why one voter at a time is safe

`single-voter-change?` implements the Raft thesis §4.1 result: a configuration
differing by **one voter** always has majorities intersecting its predecessor's,
which is the entire safety argument for changing membership without joint
consensus.

It counts *membership* changes, not power changes — and the docstring records
that neither reference can answer the power question for us. Raft has no powers;
CometBFT changes them freely but under a different quorum rule.

## The power ceiling

`max-total-power` is `2^37`. CometBFT's cap exists for proposer-priority
accumulator headroom, not for BFT reasons; urd's is lower because ClojureScript
numbers are doubles and exact only to `2^53`. Discovering that at scale would
mean a divergence between platforms; discovering it here means a parameter is
wrong.

## Reachability is not authority

Two different things, and the simulator keeps them apart on purpose:

- a joiner must be **reachable before it counts** toward a quorum;
- a removed validator stays **reachable after it stops counting**.

Getting this backwards makes reconfiguration tests pass for the wrong reason.
`sim/add-peer` is the clearest statement of it.
