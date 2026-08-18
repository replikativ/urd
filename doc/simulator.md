# The simulator

`urd.consensus.sim` runs a whole cluster deterministically, in memory, with no
sockets, no threads and no wall clock. It is the reason the Byzantine and
partition tests in this repository are ordinary tests rather than an
integration environment somebody has to keep alive.

**The simulator is a value.** `advance` takes a sim and returns a sim. There is
no mutable world; you can hold onto a state from forty ticks ago, branch it, and
run both.

## Time is logical

A tick is a tick. Message delays are drawn in ticks, timers are armed in ticks,
persistence takes ticks. Nothing consults a clock, so a run is a pure function
of `(seed, schedule)` and reproduces exactly.

The determinism rule that matters when you extend it: **sort anywhere order is
observable.** Map iteration order must never reach the trace.

## Building one

```clojure
(sim/make {:seed 7
           :nodes {:a (tm/make) :b (tm/make) :c (tm/make) :d (tm/make)}
           :node-config {:a {...}}     ; optional, per node
           :config {:value-fn (fn [sim peer-id ctx] {:id ...})}})
```

Only `:nodes` is required. The validator set is derived from the node keys; each
node's `init` runs immediately and its effects are interpreted.

`:config` defaults are `{:min-delay 1 :max-delay 3 :drop-rate 0.0
:duplicate-rate 0.0 :persist-latency 1 :max-inflight 10000}`, plus two keys not
in that map: `:bandwidth-per-tick` and `:value-fn`.

`:value-fn` is the interpreter for the `:request-value` effect. Without one,
every node receives `{:payload :none}`.

## What a tick does

`advance` performs, in this order:

1. roll bandwidth budgets
2. `tick++`
3. deliver the self-inbox (`deliver-self` effects)
4. deliver messages now due
5. fire timers now due
6. complete persistence now due

`run` is `advance` iterated. Compare `(:tick sim)` against your bound to tell
convergence from exhaustion — a run that stopped because it ran out of ticks
looks exactly like one that finished, unless you check.

## Faults

This is what the simulator is for.

```clojure
(sim/partition-network sim [#{:a :b :c} #{:d}])   ; disjoint groups
(sim/heal sim)
(sim/crash sim :b)                                ; loses buffered writes
(sim/restart sim :b)                              ; re-inits from durable state
(sim/add-peer sim :e node cfg)                    ; reachable ≠ authorised
(sim/inject sim :a input)                         ; hand a node an input
```

**`crash` is the one to read before you trust a crash test.** Buffered writes
did not used to be lost, and that blinded every crash test that came before it —
a node that "crashed" kept everything it had merely *scheduled* to write, which
is exactly the data a real crash takes. The docstring models this against POSIX
semantics.

**`add-peer` separates reachability from authority.** A joiner must be reachable
*before* it counts toward a quorum, and a removed validator stays reachable
*after* it stops counting. Getting this backwards makes reconfiguration tests
pass for the wrong reason.

Loss, duplication and delay are drawn per message from the seeded PRNG.
Bandwidth is charged per tick, which is how a state-sync storm becomes visible —
message *counts* cannot see it, because the storm is a few enormous messages.

## Reading the result

```clojure
(sim/committed s :a)      ; what :a decided, in order
(sim/all-committed s)     ; {peer-id [...]}
(sim/node-state s :a)     ; the node's own state map
(sim/agreement? s)        ; THE safety oracle
(sim/quiet? s)            ; nothing in flight, no timers due
(sim/bytes-sent s)        ; and peak-tick-bytes, bandwidth-drops
```

**`agreement?` is a prefix property**, not equality. A node that has decided
`[a b]` while another has decided `[a b c]` is *lagging*, not disagreeing;
a node that decided `[a x]` is disagreeing. Crashed nodes are excluded. Getting
this distinction right is most of what a consensus safety oracle is.

There is deliberately no liveness helper — liveness is asserted structurally,
e.g. `(every? seq (vals (sim/all-committed s)))`.

## Schedules as data

`urd.consensus.schedule` makes a fault schedule a **vector of steps**, so
`test.check` can shrink it:

```clojure
[{:tick 20} {:crash :b} {:tick 10} {:partition [#{:a :b} #{:c :d}]}
 {:tick 30} {:heal true} {:tick 40}]
```

Seeds do not shrink — a "smaller" seed is not a simpler failure. Vectors do,
and what you get back is a minimal counterexample you can read: *this crash,
then this partition, then thirty ticks.* `schedule/describe` prints it.

## Byzantine adversaries

An adversary is an ordinary `Node` that wraps an honest one and rewrites its
outbound effects. That keeps the attack honest in the way that matters: the
Byzantine node really does sign two conflicting messages at the same
`(height, round)`, and it cannot forge another validator's identity.

Two subtleties from `tendermint_byzantine_test.clj`:

- the rewriter must **descend into `persist-then`'s `:then`**, or the adversary
  cannot equivocate at all — every signed message leaves through the barrier;
- a **rewriting** wrapper must declare its own capabilities, while an
  **observing** one reports what it wraps.

## Tracing

`urd.consensus.trace/tracing` wraps a node and records every input and effect;
`summary` reduces that to counts. It is what distinguishes *"this node is
receiving nothing"* from *"it receives and does not act"*.

```clojure
(trace/summary traced-node)
;; {:n 124
;;  :in  {:init 1 :value-ready 2 :persisted 21 :message-received 93 :timer-fired 7}
;;  :out {:log 7 :cancel-timer 39 :set-timer 13 :request-value 2
;;        :persist-then 21 :broadcast 20 :send 3}}
```

Note `:out` shows `:persist-then` and no `:commit`: `summary` does not descend
into `:then`, and for Tendermint every commit is gated behind the barrier. The
node did commit.

## What the simulator does not model

State this plainly to yourself before trusting a green run:

- **No wall clock, no core.async, no threads.** Which means no orphaned timers,
  no scheduler interleaving, no backpressure. The runtime has all three, and
  `urd.consensus.conformance-test` exists because three bugs lived exactly
  there — the simulator structurally could not have found them.
- **Sampling is uniform, not weighted.** Both interpreters pass `(constantly 1)`,
  although `node/sampled` documents multiplicity as vote weight.
- **Storage faults are konserve's job.** `konserve.simulation.crash` models the
  six crash points along a write path; `clj -M:storage-sim` runs urd against it.
- **Nakamoto's `tick` event is never delivered** by either interpreter.

The rule of thumb: the simulator is authoritative about **protocol logic under
adversarial schedules**, and says nothing about **concurrency and time**. Run
`clj -M:integration` for the latter.
