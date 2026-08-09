# Phase 91.5 — axis-normal homogeneous support form

## New module

    HC4/Newton/AxisHomogeneousNormalForm.lean

This phase proves the characteristic-zero homogeneous normal form after
the fixed kernel has been normalised to a coordinate axis.

If `F` has exact transverse degree `n` in variables `i,j` and

    pderiv i F = 0,

then every nonzero monomial of `F` has

    exponent(i) = 0
    exponent(j) = n.

Thus all transverse support lies on the single monomial direction `X_j^n`;
all remaining coefficient variation occurs only in the other variables.
This is the support-theoretic form of

    F = a(other variables) * X_j^n.

The symmetric left-axis theorem is also proved.

The module additionally identifies the axis directional derivatives
`D_(1,0)` and `D_(0,1)` with the corresponding formal partial derivatives,
so the Phase 91.4 directional-vanishing results can be fed directly into
the axis normal form.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
