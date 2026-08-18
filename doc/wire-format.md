# Wire format

A signature covers **canonical CBOR** — RFC 8949 — and nothing urd-specific.
There is no urd hash function, no pre-hash step, and nothing to port.

```
transport   a plain WebSocket
framing     4-byte big-endian codec id, then the payload   (kabel.binary)
codec       14 = CBOR                                       (kabel.binary.table)
keywords    CBOR tag 39 around the printed form, colon included
signing     Ed25519 (RFC 8032) over the canonical encoding
```

In Python, the whole of signing is:

```python
message = cbor2.dumps(payload, canonical=True)
signature = signing_key.sign(message)
```

## Why not `hasch/edn-hash`

Signatures used to cover `hasch/edn-hash` of a Clojure map. That is
deterministic across clj and cljs and was correct — but it is reachable only
from Clojure. A Python or Rust client would have had to reimplement
replikativ's value model, correctly, including sets, maps, keywords and ratios,
before it could sign anything at all. Every bug in that reimplementation is a
client that silently cannot transact.

RFC 8949 is a published specification with an implementation in every language
anyone would write a client in.

## Three properties that make it safe to sign

1. **`:canonical` sorts map keys and set elements.** Clojure's maps and sets
   iterate in hash order, and while that is stable for the same contents on one
   platform, it is not a promise the two platforms make each other. Sorting
   removes the question.
2. **Ed25519 signs arbitrary-length messages**, so nothing needs pre-hashing.
   The bytes *are* the message.
3. **Keywords are CBOR tag 39** — a registered tag, not a boring extension.
   `:chain` is `39(":chain")`, colon included. kabel's own wire already uses it.

## Which canonical

There are two, and they differ.

- **RFC 8949** sorts map keys **bytewise on the encoded key**.
- **RFC 7049** sorted **length-first**.

They disagree whenever a map mixes key lengths, which every urd payload does.
`boring`'s `:profile :canonical` is 8949; urd never signs 7049. Python's
`cbor2.dumps(..., canonical=True)` is 8949 in current releases and was 7049 in
older ones — **if your signatures verify nowhere, check this first.**

## The two signed payloads

**A message**, from `urd.consensus.auth/digest`:

```clojure
{:chain c :from peer :topic t :to peer-or-nil :seq n :msg m}
```

**A vote**, from `urd.consensus.attest/vote-bytes`:

```clojure
{:kind :urd/vote :chain c :voter v :payload p}
```

`:kind` is a discriminator. The two key sets are already disjoint so their
encodings could not collide — but a security property that holds by accident of
field naming is one rename away from not holding.

## The envelope

```clojure
{:msg <payload> :from :a :topic :consensus :to nil :seq 7 :sig "<base64url>"}
```

`:sig` is a **base64url string, not a byte array**, and that is not cosmetic:
kabel's fallback serialisation is EDN, a Java `byte[]` prints as
`#object[[B 0x…]`, and the first authenticated run over WebSockets died with
*"No reader function for tag object"*.

## Framing

```python
def frame(msg):
    return struct.pack(">i", 14) + cbor2.dumps(msg)
```

kabel's CBOR has stringref deliberately off, so `cbor-x`, `fxamacker/cbor` and
`ciborium` all read it. Without a serialisation middleware kabel falls back to
`(.getBytes (pr-str m))` under codec id `:pr-str` — EDN text only a Clojure
reader can parse. urd installs the CBOR middleware explicitly.

## Writing a client

[`doc/interop/`](interop/README.md) has working ones:

- `ws_client.py` — subscribe to a topic and publish, in Python, ~40 lines
- `verify_certificate.py` — verify a commit certificate, with negative controls

Both share no code with urd. `urd.consensus.attest-interop-test` checks the same
fixture from the Clojure side, so it is pinned from both directions — a
certificate only its author can verify is not a certificate.
