# Talking to urd from another language

urd carries messages and proves decisions; what those decisions MEAN is an
application's business (see skuld for one). Everything a client needs here is a
published standard rather than urd-specific code:

| step | standard | Python | Rust | JS |
|---|---|---|---|---|
| encode | RFC 8949 canonical CBOR | `cbor2` | `ciborium` / `serde_cbor` | `cbor-x` |
| sign | Ed25519 (RFC 8032) | `cryptography`, `PyNaCl` | `ed25519-dalek` | `@noble/ed25519` |

There is no urd-specific hash, no pre-hash step, and nothing to port. This was
not true before — signatures used to cover `hasch/edn-hash`, a Clojure-specific
walk over Clojure's value model, and a client had to reimplement it correctly
before it could sign anything at all.

## Talking to a peer over a WebSocket

`ws_client.py` connects to a running urd peer, subscribes to a topic, and
publishes onto it — in Python, with no Clojure anywhere. What a client has to
speak is small and each layer is either a standard or one file:

| layer | what it is |
|---|---|
| transport | a plain WebSocket |
| framing | 4-byte big-endian codec id, then the payload (`kabel.binary`) |
| codec | `14` = CBOR, RFC 8949 (`kabel.binary.table`) |
| keywords | CBOR tag 39 around the printed form, colon included |
| protocol | the message maps in `kabel.pubsub.protocol` |

The demo publishes an **unsigned** message and the peer accepts it, because the
transport is open — kabel moves bytes. Authentication is a layer above, in
`urd.consensus.runtime`, which seals outbound and unseals inbound messages
before the state machine sees them. A validator running `Ed25519Auth` drops an
unsigned envelope without comment. See the script's own docstring for the
signed envelope shape.

## Verifying a commit certificate

The other direction: proving to yourself that a height was decided, without
running a validator. `verify_certificate.py` is that check in one screen, and
`certificate.json` is a real certificate urd produced.

```
python3 doc/interop/verify_certificate.py doc/interop/certificate.json
```

A vote attestation covers

```clojure
{:kind :urd/vote :chain "urd-testnet-1" :voter :v1 :payload [12 "block-12"]}
```

`:payload` is algorithm-defined and opaque to the signature layer: round-robin
signs `[height proposal-id]`, Tendermint `[height round value-id]`, Bullshark a
`header-id` that already digests the author and round.

Two things to note. The certificate has **no height field** — the height is
inside the signed payload, because a height beside the signatures is a number
anyone can rewrite. And the quorum for a certificate is the **Byzantine**
threshold, floor(2n/3)+1, not the crash-fault majority round-robin commits on;
the two coincide at n=4 and diverge from n=5 on.

## What the node does with it

In order, cheapest first, each able to refuse alone:

```
chain -> known sender -> key authorised by genesis -> signature
      -> nonce -> funds -> one speculative transaction
      -> write scope -> invariants -> charge
```

`:sender` is a namespace, and a namespace is the hash of a genesis record — not
of a public key. That indirection is what lets you rotate your operational key
without your identity moving, and it is the difference between urd and the
`did:key` / SSB model where the key *is* the name and rotation is a new
identity. Register the genesis first; the node reads it from the account rather
than from your message, so an unregistered sender is refused as unknown.
