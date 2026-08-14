(ns urd.consensus.signing
  "The double-sign guard: the second durability barrier from the protocol
  design, kept deliberately separate from the write-ahead log.

  CometBFT keeps `FilePVLastSignState{Height,Round,Step}` in an atomically
  rewritten file distinct from the WAL (`privval/file.go:74-83`), because it is
  the one thing that must survive even a WAL wipe. A validator that loses its
  WAL can safely re-derive everything else; a validator that loses this file
  can be slashed.

  ## The predicate is machine-checked

  `may-sign` below is the function EMITTED by the ansatz proof in
  `proofs/may_sign.clj`, which proves:

    no-double-sign                            -- (may-sign h r s h r s) = false
    same-round-requires-a-later-step
    lower-height-is-never-signable
    lower-round-at-same-height-not-signable

  Ansatz is JVM-only and urd is portable, so the proof is checked separately
  and the erased definition ships here. Do not edit one without the other.

  CometBFT writes this rule as four clauses (`spec/consensus/signing.md:216-223`)
  only because its wire encoding is not order-compatible: proposal is 0x20 = 32,
  numerically ABOVE prevote = 1. Re-encoded in semantic order the four clauses
  collapse to \"lexicographically greater\", and the whole property becomes
  \"a strict order has no repeats\".")

(def step-rank
  "Semantic order, NOT the wire encoding. See the namespace docstring."
  {:propose 0 :proposal 0 :prevote 1 :precommit 2})

(defn rank
  "The numeric rank of a step keyword, or a throw -- an unknown step must never
  be silently treated as rank 0, which would make it signable at any time."
  [s]
  (or (get step-rank s)
      (throw (ex-info "unknown signing step" {:step s :known (keys step-rank)}))))

(defn may-sign
  "The verified predicate, in the arity the proof states it in.

  True iff (h-new, r-new, s-new) is strictly lexicographically greater than
  (h-last, r-last, s-last)."
  [h-new r-new s-new h-last r-last s-last]
  (or (< h-last h-new)
      (and (= h-new h-last)
           (or (< r-last r-new)
               (and (= r-new r-last) (< s-last s-new))))))

(def genesis
  "The state before anything has ever been signed.

  Height -1 rather than 0, because a validator must be able to sign a proposal
  (step rank 0) at height 0 round 0, and lexicographic strictness would forbid
  that against a last-signed of (0,0,0)."
  {:height -1 :round 0 :step :propose})

(defn may-sign?
  "Map-shaped wrapper: may we sign `candidate` given `last-signed`?

  Both are {:height :round :step}. A nil `last-signed` means nothing has ever
  been signed."
  [candidate last-signed]
  (let [{:keys [height round step]} candidate
        {lh :height lr :round ls :step} (or last-signed genesis)]
    (may-sign height round (rank step) lh lr (rank ls))))
