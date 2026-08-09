# Phase 93.29.1 — planarisation coercions and Hessian simp-loop repair

Affected modules:

    HC4/Newton/TerminalTwoZeroPlanarisation.lean
    HC4/Newton/TerminalTwoZeroHessianSquare.lean

No theorem statement or mathematical hypothesis changes.

## Planarisation

1. The `Fin 2 ↪ Fin 4` injectivity proof now gives `congrArg` an explicit
   domain:

       fun x : Fin 4 => x.val

   avoiding the pinned elaborator's inference of the wrong `Fin` type.

2. Before applying `MvPolynomial.mem_vars`, the proof explicitly changes

       i ∈ (↑P.vars : Set (Fin 4))

   to

       i ∈ P.vars.

   It then uses the exact pinned theorem `MvPolynomial.mem_vars i`.

3. Evaluation after rename no longer applies `funext` to an equality of
   `MvPolynomial.eval` homomorphisms.  It first proves the assignment
   equality

       standardJoinPoint (u,v) ∘ standardZeroPairEmbedding = u

   and rewrites by that after `MvPolynomial.eval_rename`.

## Hessian square

The imported reflexive simp lemmas

    standardTwoZero_pderiv_two_eq_A
    standardTwoZero_pderiv_three_eq_C

are disabled locally.  This module unfolds `standardTwoZeroA/C`, and having
the reverse reflexive simp rewrite active at the same time caused the
reported simplifier recursion.

The entrywise matrix proof also uses the stable
`HC4.Polynomial.hessian_apply` theorem rather than unfolding the whole
matrix definition of `hessian`.

No heartbeat or recursion limits are increased: the proof is simplified
rather than giving automation a larger budget.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
