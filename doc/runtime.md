# The runtime

`urd.consensus.runtime` is the second interpreter: the same effects the
simulator handles, executed against core.async, a wall clock, real sockets and
a real store.

Having two interpreters is not redundancy. Three bugs lived in exactly the gap
between them — timers orphaned by a race, an out-of-order commit, a `go` block
referred in the wrong reader branch — and the simulator **structurally could
not** have found any of them, because it has no clock, no threads and no
core.async. `urd.consensus.conformance-test` runs the same algorithms through
both and asserts they agree.

## Starting one

```clojure
(<!! (rt/start-runtime!
      {:peer-id     :a
       :node        (tm/make)
       :auth        (auth/authenticator auth-config :a)   ; REQUIRED
       :validators  [:a :b :c :d]
       :network     (sn/create-simulation-network :a router)
       :store       (store/memory-store)
       :tick-ms     20
       :on-propose  (fn [ctx] {:id (random-uuid)})
       :on-finalize (fn [vertices] ...)}))
```

`start-runtime!` returns a **channel**, and follows the superv convention: a
failure arrives *on* the channel rather than being thrown. An exception object
is truthy, so check for it:

```clojure
(let [r (<!! (rt/start-runtime! cfg))]
  (when (instance? Throwable r) (throw r))
  r)
```

### Configuration

| key | |
|---|---|
| `:peer-id` | who we are |
| `:node` | the `Node` implementation |
| `:auth` | **required** — an authenticator or `:none` |
| `:validators` | the initial set |
| `:network` | a `ConsensusNetwork` |
| `:store` | a `DurableStore` |
| `:on-propose` | answers `:request-value` |
| `:on-finalize` | receives committed vertices, **synchronously** |
| `:on-revert` / `:on-resync` / `:on-equivocation` / `:on-error` | callbacks |
| `:tick-ms` | timer granularity, default 100 |
| `:tail-limit` | committed tail retained for revert, default 4096 |
| `:seed` | seeds sampling; makes a run reproducible *and predictable* |
| `:delivered-through` | resume point after a restart |

Algorithm-specific keys (`:params`, `:genesis`, timeouts, attestation schemes)
pass straight through to `init`.

## Effects, for real

**`persist-then`** writes through the `DurableStore` and only then feeds
`:persisted` back through the **event channel** — not inline. Completing inline
would run the node's continuation on the writer's stack, out of order with
everything else. A durable-write failure is fatal, and used to be silent.

**`read-durable`** asks for the latest landed values of explicit storage keys.
The runtime streams the retained log once, accumulating matching keys, then
delivers a local `:durable-values` input carrying the caller’s token. The
simulator reads its merged view of landed records. A missing key is omitted.
A failed read logs a warning and returns an empty result so optional
historical catch-up can retry.

**`set-timer`** is where the subtlest bug lived. Registration must be
synchronous, removal conditional *by identity*, and a replacement must be
registered before the old one is cancelled — otherwise a timer fires after
being cancelled, or is cancelled after being replaced. The simulator has none
of this machinery, which makes it the purest example of the
sim-passes/production-fails class.

**`commit`** calls `:on-finalize` **synchronously on the event loop**. That is
deliberate: an asynchronous callback delivered commits out of order, measured
at position 486 of a run.

**`broadcast` and `send-to`** go over topics the node declared. Unicast is
emulated over a broadcast transport, with `:to` riding on the envelope
*outside* the signed payload — the signature covers `:to` via the digest, but
the transport needs to read it without verifying first.

**`:log`** prints. There is currently no logging seam, so an algorithm's log
effects land on your stdout. That is a known gap.

## The verification edge

`setup-network-handlers` subscribes to exactly the topics the node declared,
plus `:direct`. Every inbound message goes through `auth/unseal` before it
becomes a `message-received` input — verification is async on ClojureScript, so
it happens here, in a go block, and never inside `step`.

An unsubscribed topic never delivers, silently, which is why capability
declarations are enforced rather than advisory.

Await `stop-runtime!` before reusing a node’s store or network. Shutdown waits
for the event loop, in-flight message authentication, and transport broadcasts.
A pending backend operation must complete for shutdown to finish. If removing
a subscription fails, a second stop retries the remaining handles.

## Faults are not all equal

A `step` that throws on a **remote** input is a dropped packet, not a node
fault: anyone who can reach the port can send arbitrary bytes, so garbage is an
expected input. Sixty bytes could otherwise kill a cluster.

Effects are deliberately *not* covered by that rule — an effect this node
produced and cannot interpret is a real fault. `rt/last-error` and
`rt/dropped-messages` report both.

## Storage

`urd.consensus.store/DurableStore`: `write!`, `fold`, `restore`, `checkpoint!`,
`close-store!`.

- `store/memory-store` — for tests and simulations
- `urd.consensus.stores.konserve/konserve-store` — any konserve backend
  (file, LMDB, S3, JDBC, IndexedDB); `connect-fs-store!` is a JVM convenience

Use one writer per logical consensus log. The Konserve backend serializes
appends, reads and checkpoints on that writer. A durable operation must yield
`true` before the runtime releases its dependent effects.

For Raft and Tendermint recovery, supply `:delivered-through` from the
application's own durable state. Update that cursor in the same transaction as
the application data. If the application is behind the retained history,
restore an application snapshot before restarting the validator. For an older
compacted Raft log with no voter metadata, supply `:restored-membership` with
the authoritative `:index`, `:validators` and `:outgoing` at that index.

Konserve checkpoints retire the previous generation’s reachable records. The
scoped manifest records each pending deletion before the first affected write,
so an interrupted build or cleanup resumes on the next operation or reopen.
A checkpoint temporarily holds one physical key per retired record in memory
and in its recovery manifest. Orphans from versions that already discarded the
old head require a separate offline migration with verified ownership.

An older Konserve checkpoint recorded its physical log key without recording
which logical log owned it. The default log remains readable. If a custom
`:log-key` encounters that ambiguous pointer, startup reports the keys needed
to identify and migrate the correct history. Stop writers and preserve a copy
of the backend before resolving ownership.

## Networks

`urd.consensus.network/ConsensusNetwork` is `broadcast!` and `subscribe!`.

- `create-mock-network` / `create-mock-cluster` — in-memory, for tests
- `urd.consensus.networks.simulation` — an in-process router. Note this is
  **not** the deterministic simulator; it stamps wall-clock timestamps and
  dispatches into unordered go blocks. For determinism use
  `urd.consensus.sim`.
- `urd.consensus.networks.kabel` — real WebSockets over
  [kabel](https://github.com/replikativ/kabel), CBOR-framed. JVM-only.

> **A caution before facing untrusted peers.** kabel's WebSocket transport has
> no outbound backpressure today: one client that stops reading was measured
> costing a server 1,364 MB of heap in 8 seconds, with `send!` returning `true`
> throughout. urd inherits that, and consensus liveness depends on validators
> staying up.


A runtime admits up to 128 incoming and 128 outgoing envelope operations
concurrently. When authentication or transport falls behind, excess envelopes
increment `dropped-messages` and the protocol can retransmit. Consensus WAL
writes and local archive responses retain their delivery semantics. Monitor
drops alongside disk latency and configure consensus timeouts for the store.
