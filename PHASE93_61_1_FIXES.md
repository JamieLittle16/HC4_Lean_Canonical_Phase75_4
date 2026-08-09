# Phase 93.61.1 — Classical quotient / coefficient API fix

The first Phase 93.61 build exposed one root elaboration issue and one
equality-orientation issue.

## Explicit classical quotient

`commonParameterCoefficientQuotient` branches on membership in
`P.support`.  The definition is now explicitly `by classical`, so Lean can
construct the required decidable proposition.

The old coefficient theorem returned an expression containing

    if d ∈ P.support then ... else ...

in the theorem statement itself.  That required a decidability instance
before the proof could enter classical mode.  It has been replaced by two
clean lemmas:

- `coeff_commonParameterFactorFamily_of_mem`
- `coeff_commonParameterFactorFamily_of_not_mem`

All downstream proofs now use these branch-specific lemmas directly.

## Determinant divisibility orientation

The Hessian factorisation equality already has the orientation required by
the divisibility witness, so the proof now uses `hdet`, not `hdet.symm`.

No theorem assumptions or mathematical content are changed.
