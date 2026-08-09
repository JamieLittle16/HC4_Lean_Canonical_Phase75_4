# Phase 93.10 — finite Smith balance closure

## New module

    HC4/Newton/SmithFiniteBalanceClosure.lean

This phase composes the green Phase 93.5--93.9 machinery into one finite
balance theorem.

The remaining first-wall interface is represented by

    HasSurvivingSmithFaceShape.

It requires every old minimum-face grade to be one of:

    (-1,k),
    (l,-1),
    (0,0),

or a nonzero integral first-quadrant grade.

No convex-hull hypothesis is assumed.

Lean proves that if `k*l > 1` and `(0,0)` is absent, then the explicit
Phase 93.6 separator is strictly positive on every old minimum-face term.
Phase 93.9 pole minimality rules this out.

Hence

    poleMinimal_survivingSmithFace_zero_or_product_le_one

proves

    zero grade occurs on the face
      OR
    k*l <= 1.

With positive integral `k,l`, Phase 93.5 collapses the second alternative
to the target extremes

    (-1,1), (1,-1).

Finally, after excluding the `w`-linear zero-grade wall,

    poleMinimal_survivingSmithFace_yz_or_target_extremes

concludes:

    a face exponent is exactly yz
      OR
    the negative-coordinate extremes are exactly
        (-1,1), (1,-1).

This closes the finite Smith balance calculation without importing a
general convex-analysis theorem.  The substantive remaining RS1 theorem is
now the directional first-wall classification establishing
`HasSurvivingSmithFaceShape` and excluding the `w`-linear blocker for the
actual pointed Laurent model.

A separate global adapter is still required to derive
`IsPoleMinimalAgainstSmithSeparators` from the actual pole-minimal
extraction.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
