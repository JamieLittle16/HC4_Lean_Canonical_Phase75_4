# Phase 93.70 — Separated Smith boundary closure

Built over the green Phase 93.69.2 tree.

## Main new observation

A genuine first section wall which is **not simultaneously a coefficient
wall** is a strict defect restart.

If the original special fibre does not already have a primitive zero-grade
source monomial, then every transformed potential coefficient has strictly
positive residual parameter order at such a wall.

Therefore the entire first-wall family has a common factor `X`.

On the single fixed ramified scale this gives

    20*Delta -> 20*Delta - 4

without any fresh ramification, and exact family-gradient collision is
preserved.

## Primitive zero-grade early stop

`HasPrimitiveZeroSmithSource P` records an order-zero coefficient with Smith
derivative zero.

Such a coefficient genuinely survives on the original special fibre and
immediately proves symmetric Smith minimality.

## Pure coefficient wall

If a coefficient wall occurs with no simultaneous section wall, every
transverse transformed marked coordinate is still strictly before its own
wall and hence has zero special value.

Thus the transformed special points remain exactly `0` and `e0`.

With source homogeneity, the transformed special fibre is homogeneous, so
the green symmetric-minimal classifier gives repair/terminal directly.

## No-wall endpoint

The explicit no-wall primitive Smith sections are reconstructed.

Because Phase 93.68 proves all transverse section polynomials are
identically zero, their Smith transforms retain the original canonical
special points.  The no-wall primitive family therefore also enters the
green local classifier directly.

## Only residual geometry: coupled wall

`HasCoupledAlignedSmithWall P a b` means the same genuine first step is both
a coefficient wall and a marked-section wall.

`coupledAlignedSmithWall_finiteArithmetic` extracts:
- an actual supported negative-derivative source coefficient;
- derivative exactly `-4` or `-2`;
- an actual nonzero transverse marked coordinate;
- equality of the coefficient and section wall steps.

This is now the only local geometric endpoint left.

## Headline

`alignedSmith_separatedBoundaryDispatcher` proves, on the fixed
once-ramified defect scale:

    repair/terminal
      OR
    strict defect restart
      OR
    coupled coefficient+section wall.

No free section-boundary branch remains.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
