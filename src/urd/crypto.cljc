(ns urd.crypto
  "Byte codecs, delegated to geheimnis.

  ## What used to be here, and why it is gone

  484 lines: a BouncyCastle Ed25519 with a ClojureScript branch that threw
  `\"ED25519 not yet implemented\"`, a snapshot-signing layer, a multi-signature
  certificate layer, and a merkle root. Every one of them had ZERO callers --
  each production mention was a comment or a docstring. The live signing path
  is `urd.consensus.auth` and `urd.consensus.attest`, both on geheimnis, and has
  been for some time.

  It was not merely dead, it was a third implementation of something two other
  libraries in this stack already had, and it is where a real bug lived:
  `base64->bytes` used Closure's `decodeStringToByteArray`, which returns a
  plain JS Array. Web Crypto refuses one, so no signature could verify on
  ClojureScript. geheimnis's codec uses `decodeStringToUint8Array` and never
  had the bug. That is the argument for deduplicating in one line.

  ## Base64url, not base64

  The signature field moved from standard base64 to base64url, because that is
  what geheimnis provides and because it is the better choice for a wire
  format: URL- and filename-safe, unpadded, no `+`/`/` to escape. Nothing is
  deployed, so this is free now and would not be later.

  Hex is unchanged, byte for byte -- verified against the old implementation
  including negative bytes. That matters more than it sounds: `bytes->hex` of
  a public key IS the attribute namespace a user owns, so a difference here
  would silently re-address every datom anyone had written."
  (:require [org.replikativ.geheimnis.codec :as codec]))

(def bytes->base64
  "Encode bytes as unpadded base64url."
  codec/bytes->b64url)

(def base64->bytes
  "Decode base64url (padded or not) to bytes.

  `Uint8Array` on ClojureScript, which is what Web Crypto requires."
  codec/b64url->bytes)

(def bytes->hex
  "Lowercase hex. This is what names a key's attribute namespace."
  codec/bytes->hex)

(def hex->bytes
  "Bytes from lowercase hex."
  codec/hex->bytes)
