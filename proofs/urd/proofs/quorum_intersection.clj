(ns urd.proofs.quorum-intersection
  "MACHINE-CHECKED: two Byzantine quorums share an honest member.

  This is the defining property of `node/byzantine-threshold`, and every
  Byzantine algorithm here rests on it. If it were false, two quorums could be
  disjoint in their honest members and two conflicting values could each be
  decided.

  ## The statement

  With `n` validators, `f = floor((n-1)/3)` tolerated faults and a quorum of
  `q = floor(2n/3) + 1`:

      any two quorums intersect in at least  2q - n  members
      and                                    2q - n  >  f

  The first half is inclusion-exclusion over a finite set and is not what is
  proved here -- it is a counting fact about subsets, not about these
  thresholds. What is proved is the ARITHMETIC half, which is where the
  thresholds could actually be wrong: that `2q - n` strictly exceeds `f` for
  every `n`, so the shared members cannot all be faulty.

  That is the half a typo in `byzantine-threshold` would break, and it is the
  half stated over Nat.

  ## Why this file exists

  `node/byzantine-threshold` claimed \"machine-checked in ansatz as
  `quorum-intersection`\" in three places, and no such proof was in the
  repository. A claim of verification with nothing behind it is worse than no
  claim."
  (:require [ansatz.core :as a]))

(a/load-init!)

;; The two thresholds, exactly as `urd.consensus.node` computes them.
(a/defn quorum [n Nat] Nat
  (+ 1 (quot (* 2 n) 3)))

(a/defn tolerated [n Nat] Nat
  (quot (- n 1) 3))

;; The shared members of two quorums: |A| + |B| - n, by inclusion-exclusion.
(a/defn shared [n Nat] Nat
  (- (* 2 (quorum n)) n))

;; ===================================================================
;; THE THEOREM: the members two quorums share are more than the faults
;; that can be tolerated -- so at least one of them is honest.
;; ===================================================================
(a/theorem quorum-intersection [n :- Nat]
  (= Bool (< (tolerated n) (shared n)) true)
  (grind))
