# Security

Three layers, each answering a different question:

| layer | question | namespace |
|---|---|---|
| message authentication | who **sent** this? | `urd.consensus.auth` |
| vote attestations | who **voted**? | `urd.consensus.attest` |
| commit certificates | did height *H* decide *V*? | `urd.consensus.attest` |
| application agreement | do we agree on the **result**? | `urd.consensus.apphash` |

## What was here before

Nothing. `verified-by` was `#{(:sender msg)}` — a field the sender writes. Every
Byzantine property this library proves was therefore conditional on an
authenticated transport that did not exist. That is worth stating plainly,
because it is the kind of gap that reads as present when you skim.

## Message authentication

`urd.consensus.auth/authenticator` builds the verification edge:

```clojure
{:chain       "urd-mainnet-1"   ; REQUIRED — domain separation
 :peer-id     :a
 :private-key <32 bytes>
 :public-keys {:a <32> :b <32> :c <32>}}
```

or the literal `:none`. **There is no default.** A node that cannot verify its
peers should refuse to start, not start and trust them — so opting out is
something you type.

`:none` is not "weak auth", it is *no* auth, and `NoAuth` returns
`verified-by #{}` deliberately: Byzantine algorithms then reject everything
rather than being satisfied by a claim anyone can forge.

### What the signature covers

```clojure
{:chain c :from peer :topic t :to peer-or-nil :seq n :msg m}
```

Each field is there because of what an attacker gains without it:

- **`:chain`** — a message signed on a testnet is otherwise valid on mainnet.
- **`:topic`** — re-deliver a message on a topic its author never used.
- **`:to`** — re-address a directed message, or strip `:to` so a message meant
  for one peer is accepted by every peer on the topic.
- **`:seq`** — replay the same message forever, from any peer, at any later
  time.

### Replay protection

A sliding window of 32 sequence numbers per sender, kept as a **set** rather
than a 64-bit bitmap because ClojureScript's bit operations are 32-bit.

Freshness is checked *before* the signature — the cheap end first — but the
window is only updated *after* verification succeeds, so a forged sequence
number cannot lock a peer out.

The runtime saves the sender counter before transmission and atomically claims
each verified sequence in the receiver's store before delivery. A Konserve
checkpoint preserves these registers. For an application snapshot install,
retain the recovering peer's own registers and signing key. A separately
configured `:auth :replay-store` can keep them outside the replaced WAL.
An in-memory store provides replay protection only for its own lifetime.

When upgrading a cluster whose counters existed only in memory, stop all
old signers and coordinate a new authenticated chain identifier across the
cluster before restarting. Reusing the original chain and keys with empty
registers allows old envelopes to verify again. Use recovery procedures for
the consensus signing state as well.

### One idiom worth copying

```clojure
(true? (<! (sign/verify pk bytes sig)))
```

`true?`, not truthiness. geheimnis follows the superv convention: a malformed
key or signature is **put on the channel**, not thrown. An exception object is
truthy, so the obvious `(when (<! ...))` accepts every malformed signature —
and `:sig ""` then authenticates as any peer whose key you hold. Three bytes on
the wire, no key material, total bypass.

## Vote attestations

Message authentication proves who *sent* a message. It is not enough, because a
vote gets **relayed**: catch-up and vote-bundle messages exist precisely to
carry other nodes' votes, and the peer handing you one is usually not its
author. A bundle of bare names is a claim by the relayer, not evidence about
the voters — one peer could hand you a quorum it invented.

An attestation is what makes a vote transferable through a party nobody trusts.

```clojure
(attest/attestations {:chain "urd-1" :peer-id :v1
                      :private-key <32> :public-keys {...}})
;; => {:sign-vote (fn [voter payload]) :verify-vote (fn [voter payload att])}
```

Drop-in for any algorithm's `test-attestations` — which are labelled **NOT
CRYPTOGRAPHY** in capitals and are a hash anyone can recompute.

**The payload must bind the height.** Tendermint's is `[height round value-id]`;
round-robin's is `[height proposal-id]`. Without the height, an attestation
replays at every later height the same value recurs at — which is reachable,
because a snapshot id is permitted to be a content hash.

**`attestations` is JVM-only** and throws under ClojureScript. The seam is
synchronous because it runs inside pure transitions, and ClojureScript has no
synchronous Ed25519 — Web Crypto is promise-only. Validators run on the JVM;
what a browser needs is `verify-certificate`, which is asynchronous and
portable. Making the seam portable needs a synchronous SHA-512 handed to noble,
an upstream geheimnis change.

## Commit certificates

A portable, third-party-checkable proof that a payload was decided.

```clojure
(attest/certificate {:chain "urd-1" :payload [12 "block-12"] :votes {...}})
(attest/verify-certificate cert public-keys)
;; => channel of {:valid? true :voters #{:v1 :v2 :v3} :quorum 3 :of 4}
```

Not a bare boolean: one signature short of quorum and signed by nobody are
different situations, and a caller that can only see `false` cannot tell them
apart.

**There is no `:height` field, on purpose.** Only `:payload` is covered by the
signatures, so a height beside it is a number an attacker rewrites freely — and
a verifier returning `:valid? true` next to an attacker's height is worse than
one that never mentions the height. The height lives *inside* the payload.

Certificates use the **Byzantine** threshold, not the crash-fault majority the
deciding algorithm may have used: a certificate is a claim made to a stranger
under an adversarial assumption.

And it is genuinely checkable off-platform — `doc/interop/verify_certificate.py`
verifies one in Python with `cbor2` and `cryptography`, sharing no code with
urd, and rejects it replayed a height later, claimed for another chain, and
with a tampered payload.

## The double-sign guard, and what is machine-checked

`urd.consensus.signing` holds the predicate that decides whether a validator
may sign at `(height, round, step)`. CometBFT keeps the same state in a file
whose loss is a slashable offence.

Two properties here are **machine-checked in [ansatz](https://github.com/replikativ/ansatz)**,
and `clj -M:proofs` runs them:

| theorem | says |
|---|---|
| `no-double-sign` | a validator may never re-sign the triple it is already at |
| `same-round-requires-a-later-step` | at one `(height, round)`, only a strictly later step |
| `lower-height-is-never-signable` | never go backwards in height |
| `lower-round-at-same-height-not-signable` | nor in round |
| `quorum-intersection` | two Byzantine quorums share strictly more members than the tolerated faults, hence at least one honest one |

The first four are the **safety** directions ("never allowed"). The liveness
direction ("a higher height is always signable") is stated in the proof file
and **not proved** — it needs a Bool↔Prop bridge for hypotheses that ansatz
does not yet have. Safety, which is what non-slashability means, is covered.

`quorum-intersection` proves the *arithmetic* half: that `2q - n > f` for every
`n`, where `q` is `byzantine-threshold` and `f` is `byzantine-tolerance`. The
counting half — that two subsets of size `q` intersect in at least `2q - n`
members — is inclusion-exclusion over a finite set and is not about these
thresholds. The arithmetic half is the one a typo would break.

### What the proofs do and do not buy

Be clear about this, because it is easy to overread.

**urd does not call the proved functions.** Nothing in `src/` requires
`urd.proofs.*`. Tendermint calls `signing/may-sign?`, which calls
`signing/may-sign` — a **hand-written copy** of the ansatz-emitted definition.
Same for `node/byzantine-threshold` against the proof's `quorum`.

That is structural, not laziness. Ansatz is JVM-only; `urd.consensus.signing`
is `.cljc` and is called from `tendermint.cljc`. A portable library cannot
call a JVM-only artifact, and having the JVM call the emitted function while
ClojureScript calls a copy would be worse — two code paths where there is
currently one.

So what the proofs establish is: **the definition is correct.** What bridges
the proof to the running code is the differential check that `clj -M:proofs`
runs alongside the theorems — 1325 assertions comparing the shipped functions
to the verified ones, exhaustively over `0..3^6` for `may-sign` and over
`n ∈ [1,400)` plus a scatter to 10^6 for the thresholds.

That bridge is only as good as its gating, so it is gated: `bin/test-all` runs
it, and so does CI (`test-proofs`). A change to `signing/may-sign` or
`node/byzantine-threshold` that drifts from the verified definition fails the
build.

**Ansatz is not a runtime dependency and must not become one.** It appears only
in the `:proofs` alias; the published pom does not mention it, and a consumer of
`org.replikativ/urd` never loads it.

The proof alias pins Ansatz 0.2.654. The quorum theorem uses the omega arithmetic tactic.

## Application agreement

Consensus agreeing on a *value* does not mean two nodes agree on the *result*
of applying it. `urd.consensus.apphash` carries a digest of applied state on the
next proposal, so a divergence surfaces one block later instead of never.
`:require?` defaults to **true**.

## Known limitations

- `urd.consensus.rng` is xorshift32 and emphatically **not** cryptographic. A
  seeded runtime is reproducible *and predictable*: one observed sample reveals
  the whole future stream. An unseeded one reseeds per draw from the host
  CSPRNG.
- Tendermint's equivocation evidence carries the conflicting messages but not
  their signatures, because `unseal` drops `:sig`. Evidence is therefore
  detectable locally but not independently verifiable by a third party — enough
  for detection, not yet enough for accountability.
