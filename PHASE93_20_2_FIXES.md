# Phase 93.20.2 — symmetric binary Hessian determinant repair

Affected file:

    HC4/Newton/PreterminalFirstDeparture.lean

The pinned Mathlib build does not expose either of the mixed-partial
coefficient convenience lemmas attempted in Phase 93.20 / 93.20.1.

The restart argument itself does not need a separate commutation theorem.
The binary Hessian determinant for a polynomial potential is intrinsically
the symmetric expression

    P_UU * P_VV - (P_UV)^2.

Phase 93.20.2 therefore defines `binaryDirectionalHessianDet` directly in
that canonical symmetric form.

Consequently, once the preterminal linear Schur source gives

    P_VV = 0,

the determinant identity

    det = -(P_UV)^2

is immediate by ring normalisation.  The unavailable mixed-partial
commutation proof is removed entirely.

The mixed-pivot and affine/separated dichotomy, and all downstream theorem
statements, are unchanged.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
