# Portability

urd is Clojure and ClojureScript. This page says exactly what that means,
because a portability claim no job exercises is not a claim — it is a comment.

## How the claim is made falsifiable

`clj -M:cljs-test && node target/cljs-test.js` — **48 tests, 126 assertions**,
run in CI.

The build step matters: it compiles to a *file* and hands it to node, rather
than going through `cljs.main -m`. The latter boots a REPL environment, and once
the runner calls `js/process.exit` — which it must, or node stays alive on
core.async's timers — the JVM side waits forever on a process that has gone. The
suite passed and the command never returned, which is the worst of both: a green
run indistinguishable from a hung one.

The CI job also once ran green *in seconds having executed nothing*, because it
compiled and never invoked node.

## JVM-only, and why

| | reason |
|---|---|
| `urd.consensus.networks.kabel` | a JVM WebSocket server (http-kit, `<!!`). Browser *observers* are therefore not yet possible. |
| `urd.consensus.validator` | a CLI entry point — `clojure.java.io`, konserve.memory, the kabel network |
| `attest/attestations` | throws under cljs, by design (below) |
| `stores.konserve/connect-fs-store!` | a JVM convenience behind a reader conditional; the seam itself is portable |

### `attestations` is JVM-only on purpose

The `sign-vote`/`verify-vote` seam is **synchronous**, because it runs inside
pure state-machine transitions that cannot await anything. ClojureScript has no
synchronous Ed25519: Web Crypto is promise-only, and the `@noble/ed25519`
fallback is used through `verifyAsync`.

So it refuses to build under cljs rather than quietly returning something
weaker. Validators run on the JVM; what a browser or Node client actually needs
is `verify-certificate`, which is asynchronous, portable and tested under both
runners.

Making the seam portable needs a synchronous SHA-512 handed to noble — an
upstream geheimnis change, and a real gap rather than a closed question.

## What the cljs runner does not reach

Seven `.cljc` namespaces are not loaded by `test/urd/cljs_test_runner.cljs`:
`algorithms/round_robin`, `algorithms/tendermint`, `apphash`, `attest`,
`schedule`, `networks/simulation`, `stores/konserve`.

`attest` is the notable one — it is the namespace with a cljs-specific throw and
it has no ClojureScript coverage.

Tendermint *is* exercised under Node by `test/urd/portcheck.cljs`, but that is a
**manual** entry point: not in the runner, not in CI, and its expected
fingerprints are verified by a human pasting a command from a docstring.

And **"loaded" is not "asserted on"**: `substrate_portability_test` says so
itself. Its assertions are `(is (fn? rt/start-runtime!))`-grade; they exist to
force the compiler to load `runtime`, `network`, `store`, `auth` and `trace`
under Node. No runtime is started there.

## Traps this codebase has already paid for

Each of these was a real bug, and together they are the argument for the cljs
job existing at all.

**`(bit-and 0xFFFFFFFF 0xFFFFFFFF)` is `-1` under ClojureScript.** The seeded
PRNG produced `[83 55 7 45 …]` on the JVM and `[83 55 11 49 …]` under Node — so
message delays, drop decisions and sampled peers all differed. Every test that
could have caught it was `.clj`.

**Bit operations are 32-bit**, which is why the replay window is a set rather
than a 64-bit bitmap.

**Numbers are doubles**, exact only to `2^53` — hence the lowered power ceiling
and `urd.consensus.bignat`, one implementation rather than a reader conditional
per expression, with the JVM's `BigInteger` as a property-test oracle.

**UUID ordering differs.** Bullshark digests are strings because JVM
`UUID/compareTo` and cljs `UUID` order differently — a JVM node and a browser
node would have computed different total orders.

**Closure's `decodeStringToByteArray` returns a plain JS Array**, and Web Crypto
refuses one. The same shape bit `auth/digest`'s `into-array`. Both meant every
signed message was JVM-only in a library whose whole reason for verifying at the
async edge is that ClojureScript's crypto is promise-based.

**`superv.async/go-loop-try-` unquotes a channel value into its expansion**,
which the cljs compiler refuses. That single macro use is why the runtime did
not compile at all.

## Running it

```bash
clj -M:cljs-test && node target/cljs-test.js
bin/test-all                    # includes the above
```
