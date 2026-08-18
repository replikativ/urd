"""A urd light client: verify a commit certificate without running a validator.

This is the thing a certificate exists for. A validator checks each vote as it
arrives, synchronously, against keys it already holds. A stranger -- a browser,
a wallet, an indexer, another chain -- holds only the validator set and wants to
know whether height H was really decided. That check is this file, and it needs
no Clojure, no urd, and no network.

    pip install cbor2 cryptography
    python3 doc/interop/verify_certificate.py doc/interop/certificate.json

`certificate.json` was produced by urd (see `urd.consensus.attest-interop-test`,
which verifies the same fixture from the other side).
"""
import cbor2, json, sys
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from cryptography.exceptions import InvalidSignature


def kw(s):
    """A Clojure keyword: CBOR tag 39 around its printed form, colon included."""
    return cbor2.CBORTag(39, s)


def vote_bytes(chain, voter, payload):
    """Exactly what `urd.consensus.attest/vote-bytes` produces.

    `canonical=True` is RFC 8949 -- sorted map keys, shortest encodings. Older
    cbor2 releases implemented RFC 7049's length-first ordering instead, which
    disagrees whenever a map mixes key lengths. If nothing you sign verifies,
    check that first.
    """
    return cbor2.dumps({kw(":kind"):    kw(":urd/vote"),
                        kw(":chain"):   chain,
                        kw(":voter"):   kw(":" + voter),
                        kw(":payload"): payload},
                       canonical=True)


def verify_certificate(chain, payload, votes, validators):
    """The voters whose attestation verifies. Distinct voters, in the set only.

    A voter outside `validators` contributes nothing however well-formed its
    signature -- otherwise anyone who can mint keys can manufacture a quorum.
    """
    good = set()
    for voter, sig in votes.items():
        pk = validators.get(voter)
        if pk is None:
            continue
        try:
            Ed25519PublicKey.from_public_bytes(pk).verify(sig, vote_bytes(chain, voter, payload))
            good.add(voter)
        except InvalidSignature:
            pass
    return good


def byzantine_quorum(n):
    """floor(2n/3)+1 -- the threshold for a claim made to a stranger.

    NOT the crash-fault majority round-robin commits on. The two coincide at
    n=4 and diverge from n=5 on, and the difference is deliberate: a validator
    decides among peers it assumes are merely slow, a certificate is checked
    under an adversarial assumption where two quorums must intersect in more
    than f members.
    """
    return (2 * n) // 3 + 1


def main(path):
    doc = json.load(open(path))
    chain = doc["chain"]
    votes = {k: bytes.fromhex(v) for k, v in doc["votes"].items()}
    validators = {k: bytes.fromhex(v) for k, v in doc["validators"].items()}

    # Round-robin's vote payload is [height proposal-id]. The height lives
    # INSIDE the signed payload, not beside it -- a certificate carries no
    # separate height field, because an unsigned one is a number an attacker
    # rewrites freely.
    payload = [doc["height"], doc["block"]]

    good = verify_certificate(chain, payload, votes, validators)
    need = byzantine_quorum(len(validators))
    print(f"chain={chain} height={doc['height']} block={doc['block']}")
    print(f"verified {sorted(good)} -- {len(good)} of {len(validators)}, need {need}")
    print("VALID" if len(good) >= need else "INVALID")

    # Negative controls. A demo that only ever prints VALID has not shown that
    # it is checking anything.
    replay = verify_certificate(chain, [doc["height"] + 1, doc["block"]], votes, validators)
    other  = verify_certificate("urd-mainnet", payload, votes, validators)
    tamper = verify_certificate(chain, [doc["height"], "block-13"], votes, validators)
    print(f"replayed one height later: {len(replay)} verified (expect 0)")
    print(f"claimed for another chain:  {len(other)} verified (expect 0)")
    print(f"payload tampered:           {len(tamper)} verified (expect 0)")
    ok = len(good) >= need and not (replay or other or tamper)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "doc/interop/certificate.json"))
