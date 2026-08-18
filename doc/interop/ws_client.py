"""Talk to a running urd peer over a WebSocket. No Clojure, no urd, no JVM.

Everything a client needs is on this page:

  transport   a plain WebSocket
  framing     4-byte big-endian codec id, then the payload (kabel.binary)
  codec       14 = CBOR, RFC 8949 (kabel.binary.table)
  keywords    CBOR tag 39 around the printed form, colon included
  protocol    the message maps in kabel.pubsub.protocol -- subscribe, publish,
              unsubscribe, and the handshake acks

Run it against a peer listening on 47399 and the peer's handler receives a
Clojure map, keywords and byte arrays intact.

## What this demo does NOT show: authentication

It publishes an UNSIGNED message and the peer accepts it, because the transport
itself is open -- kabel moves bytes. Authentication is a layer above, in
`urd.consensus.runtime`: outbound messages go through `auth/seal` and inbound
through `auth/unseal` before the state machine sees them. This script talks to
the network directly and so bypasses that layer entirely.

Against a validator configured with `Ed25519Auth`, a message shaped like the
one below is dropped without comment -- `unseal` requires a `:from` in the
peer's key set and a `:sig` over the digest, and a message that fails is
treated as a packet that never happened. To be heard by a real validator, wrap
the payload in the signed envelope:

    {:msg <payload> :from <peer-id> :topic <topic> :to <peer-or-nil>
     :seq <n> :sig <base64url Ed25519 over the canonical CBOR digest>}

See `urd.consensus.auth/digest` for exactly which fields that signature covers
and why each of them is in there.
"""
import asyncio, struct, cbor2, websockets

CBOR_CODEC = 14   # kabel.binary.table

def kw(s): return cbor2.CBORTag(39, s)

def frame(msg):
    """kabel's wire framing: 4-byte big-endian codec id, then the payload."""
    return struct.pack(">i", CBOR_CODEC) + cbor2.dumps(msg)

def unframe(data):
    codec, = struct.unpack(">i", data[:4])
    assert codec == CBOR_CODEC, f"unexpected codec {codec}"
    return cbor2.loads(data[4:])

async def main():
    async with websockets.connect("ws://localhost:47399") as ws:
        # 1. Subscribe to a topic, exactly as kabel.pubsub.protocol/subscribe-msg does.
        await ws.send(frame({kw(":type"):          kw(":pubsub/subscribe"),
                             kw(":id"):            "python-client",
                             kw(":topics"):        [kw(":votes")],
                             kw(":client-states"): {}}))
        ack = unframe(await asyncio.wait_for(ws.recv(), timeout=10))
        print("ACK:", ack)

        # 2. Publish a vote onto that topic.
        await ws.send(frame({kw(":type"):    kw(":pubsub/publish"),
                             kw(":topic"):   kw(":votes"),
                             kw(":payload"): {kw(":kind"):        kw(":vote"),
                                              kw(":voter"):       "python",
                                              kw(":proposal-id"): "p-42",
                                              kw(":att"):         b"\x01\x02\x03"}}))
        print("PUBLISHED")
        await asyncio.sleep(2)

asyncio.run(main())
