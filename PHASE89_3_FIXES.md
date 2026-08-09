# Phase 89.3 — iterated refinement equals one exposed weight

## New module

    HC4/Newton/IteratedRefinement.lean

This phase proves the actual two-stage finite refinement statement needed for
the Newton--Rees globalisation.

### Finite theorem

`isSecondaryMaxOnPrimary_iff_isLexMaxOn` proves that an exponent survives

1. primary maximisation by `w₀`, then
2. secondary maximisation by `w₁` inside the primary face

if and only if it is lexicographically maximal for `(w₀,w₁)`.

### Polynomial theorem

`iteratedInitialForm_eq_lexInitialForm` lifts that equivalence to literal
equality of `MvPolynomial` exposed sums.

Finally,

    scaledInitialForm_eq_iteratedInitialForm

combines Phase 89.2 with the new theorem. Under the finite secondary bound
`w₁ < M` on the original support, the two-stage refinement is literally the
face selected from the original polynomial by the single weight
`M*w₀+w₁`.

This is the finite Rees-to-Newton exposure theorem needed before the
first-rank-entry analysis.

No existing theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
