(ns urd.proofs.may-sign
  "MACHINE-CHECKED: a validator cannot double-sign.

  This is the property that keeps a validator's stake safe. It is a total
  function over a 3-tuple, which makes it the ideal first verification target:
  small, pure, and catastrophic if wrong.

  ## What is proved

  A validator keeps the last (height, round, step) it signed and may sign again
  only if the new triple is LEXICOGRAPHICALLY GREATER, with steps ordered
  proposal(0) < prevote(1) < precommit(2).

  CometBFT writes this rule as four clauses (spec/consensus/signing.md:216-223)
  because its wire encoding is not order-compatible -- proposal is 0x20 = 32,
  which is numerically greater than prevote = 1. Re-encoded in SEMANTIC order,
  those four clauses are exactly \"lexicographically greater\", and the whole
  property collapses to: a strict order has no repeats.

  Verified (ansatz, bundled Init tier, no Mathlib):

    no-double-sign                            proved   1.9 s
    same-round-requires-a-later-step          proved   1.2 s
    lower-height-is-never-signable            proved   1.1 s
    lower-round-at-same-height-not-signable   proved   1.0 s
    higher-height-is-always-signable          NOT PROVED -- see below

  The four proved theorems are the SAFETY directions (\"never allowed\"). The
  unproved one is LIVENESS (\"always allowed\"): it needs the Prop hypothesis
  `h2 < h1` to discharge a Bool disjunct, and ansatz currently bridges
  Bool<->Prop for goals but not for hypotheses. Safety -- which is what
  non-slashability means -- is fully covered.

  ## Why this file is not on the classpath

  Ansatz is JVM-only, and urd is a portable clj+cljs library, so ansatz cannot
  be a runtime dependency. It does not need to be: ansatz ERASES proofs and
  emits ordinary Clojure, so the verified definition below compiles to exactly
  the predicate urd ships. This file is the justification, checked separately on
  the JVM; the shipped code is the emitted function.

  Requires ansatz with the Boolean simp set (PR #70 or later). Before that fix
  every Bool-valued formulation timed out -- Lean's Bool `@[simp]` lemmas were
  264-of-301 absent from the bundled store, and `@[simp]` priorities were
  dropped on import, so simp oscillated between two orientations of a Bool
  equality forever."
  (:require [ansatz.core :as a]))

;; The runnable predicate. Compiles to ordinary Clojure; this is the code
;; that ships.
(a/defn may-sign
  [h-new Nat, r-new Nat, s-new Nat, h-last Nat, r-last Nat, s-last Nat] Bool
  (or (< h-last h-new)
      (and (== h-new h-last)
           (or (< r-last r-new)
               (and (== r-new r-last) (< s-last s-new))))))

;; ===================================================================
;; THE THEOREM: a validator may never re-sign the state it is already
;; at. Hence never a second prevote and never a second precommit at the
;; same (height, round) -- which IS non-slashability.
;; ===================================================================
(a/theorem no-double-sign [h :- Nat, r :- Nat, s :- Nat]
  (= Bool (may-sign h r s h r s) false)
  (grind))

;; At the same height and round, signing requires a strictly later step.
(a/theorem same-round-requires-a-later-step [h :- Nat, r :- Nat, x :- Nat, y :- Nat]
  (= Bool (may-sign h r x h r y) (< y x))
  (grind))

;; Never go backwards: a strictly lower height is never signable, whatever
;; the round and step.
(a/theorem lower-height-is-never-signable
  [h1 :- Nat, h2 :- Nat, r1 :- Nat, r2 :- Nat, s1 :- Nat, s2 :- Nat,
   hlt :- (< Nat h1 h2)]
  (= Bool (may-sign h1 r1 s1 h2 r2 s2) false)
  (grind))

;; Same height, strictly lower round: never signable.
(a/theorem lower-round-at-same-height-not-signable
  [h :- Nat, r1 :- Nat, r2 :- Nat, s1 :- Nat, s2 :- Nat,
   rlt :- (< Nat r1 r2)]
  (= Bool (may-sign h r1 s1 h r2 s2) false)
  (grind))

;; NOT PROVED -- liveness, blocked on a Bool<->Prop bridge for HYPOTHESES:
;;
;;   (a/theorem higher-height-is-always-signable
;;     [h1 :- Nat, h2 :- Nat, r1 :- Nat, r2 :- Nat, s1 :- Nat, s2 :- Nat,
;;      hlt :- (< Nat h2 h1)]
;;     (= Bool (may-sign h1 r1 s1 h2 r2 s2) true)
;;     (grind))
;;
;; grind: all strategies failed (544 ms). Left in place, commented, so the gap
;; stays visible rather than quietly forgotten.

(comment
  ;; The predicate runs as ordinary Clojure:
  (may-sign 5 0 0  5 0 0)  ; => false  same state: refused
  (may-sign 5 0 2  5 0 1)  ; => true   precommit after prevote: allowed
  (may-sign 5 0 1  5 0 2)  ; => false  prevote after precommit: refused
  (may-sign 6 0 0  5 9 2)  ; => true   next height: allowed
  (may-sign 4 9 2  5 0 0)  ; => false  going back: refused
  )
