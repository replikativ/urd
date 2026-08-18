(ns urd.wire
  "The bytes a signature covers.

  ## Why this is a namespace and not two `hasch/edn-hash` calls

  urd signed `hasch/edn-hash` of a Clojure map. That works, and it was
  deterministic across clj and cljs, but it makes every signature in the system
  reachable only from Clojure: `edn-hash` is a replikativ-specific walk over
  Clojure's own value model, and a Python or Rust client wanting to submit a
  transaction would have to reimplement it -- correctly, including its handling
  of sets, maps, keywords and ratios -- before it could sign anything at all.
  That is a large and thankless amount of work to demand of a client, and every
  bug in it is a client that silently cannot transact.

  So a signature covers canonical CBOR instead. The message is
  `(boring/encode payload {:profile :canonical})`: RFC 8949 core deterministic
  encoding, which is a published specification with implementations in every
  language anyone would write a client in. In Python the whole of it is

      cbor2.dumps(payload, canonical=True)   # note: see the caveat below
      signing_key.sign(message)              # ed25519, arbitrary length

  ## The three properties that make this safe to sign

  1. `:canonical` SORTS map keys and set elements (`boring.core/encode-all`
     says so explicitly). This matters more than it looks. Clojure's hash maps
     and sets iterate in an order determined by hashes, and while that order is
     stable for the same contents within one platform, it is not a property the
     two platforms promise each other. Sorting removes the question.

  2. Ed25519 signs arbitrary-length messages, so nothing needs pre-hashing. The
     bytes ARE the message, which is one less thing for a client to get wrong
     and one less place for a length-extension argument to be had.

  3. Keywords encode as CBOR tag 39 (`identifier`) around the printed keyword
     including its leading colon -- `:chain` is `39(\":chain\")`. That is a
     registered tag, not a boring extension, and kabel's own CBOR wire already
     uses it, so a client that can talk to a kabel peer at all already handles
     it. `cbor2.CBORTag(39, \":chain\")` is the Python side.

  ## Caveat for client authors: which canonical

  There are two canonical CBOR orderings. RFC 8949 sorts keys bytewise on their
  ENCODED form; RFC 7049 sorted length-first. They differ whenever a map mixes
  key lengths, which every payload here does. `:profile :canonical` is 8949.
  Python's `cbor2.dumps(..., canonical=True)` is also 8949 in current releases
  but was 7049 in older ones, so a client that produces signatures nothing
  verifies should check that first. boring can emit the old order for
  comparison via `:profile :canonical-rfc7049`; urd never signs it.

  ## What this deliberately does NOT do

  It does not hash. `urd.crypto` and `hasch` remain how urd content-addresses
  values -- a snapshot ref, an invariant's identity -- and those are internal
  identities rather than things a foreign client must reproduce. Signing and
  content-addressing are different jobs and giving them the same encoding by
  accident is how one of them ends up constrained by the other's needs."
  (:require [boring.core :as boring]))

(def ^:private canonical
  "RFC 8949 core deterministic encoding. Bound once: `boring/encode` accepts a
  fresh options map per call and re-resolves it, and this one never varies."
  {:profile :canonical})

(defn signing-bytes
  "The canonical CBOR encoding of `payload`, as bytes to sign or verify.

  Callers build `payload` as a plain map of the fields a signature must cover.
  What belongs in it is the caller's decision and a security-relevant one --
  see `urd.consensus.auth/digest` and `urd.consensus.attest/vote-bytes`, both
  of which document at length which fields they cover and what an attacker can do
  with any field they omit."
  [payload]
  (boring/encode payload canonical))
