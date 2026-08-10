# Phase 75.20 — zero common-kernel slope elimination

This phase removes the last exceptional branch left by the Phase 75.19
first-kernel restart collapse.

## New source provenance

`RigidClosingRecenteredSourceData` now records that its retained family is
literally the canonical affine recentering of its original exact-collision
source datum.  This was already true of the unique constructor; the new field
prevents later existential packaging from erasing that fact.

## Aligned Smith margin

For a monomial `d` in a lossless frontier family, the defect-preserving Smith
exposure has residual exponent

    2*d1 + 2*d2 + 4*d3 + 20*v - 4.

The new theorem `oneStepResidualExponent_ge_three` proves that this is at
least `d3`.  If it were smaller, aligned nonnegativity forces

    d1 = d2 = 0, d3 = 1, v = 0,

which is exactly the special-fibre `w`-linear Smith pattern.  The existing
homogeneous exact-axis-collision theorem forbids that pattern.

Therefore `defectSmithExposure_threeSlopeOne` gives coefficientwise integral
kernel slope `1` in coordinate `3` for the complete exposure family.

## Translation stability

The phase also proves the reusable identity

    Translate_a (Inflate Q)
      = Inflate (Translate_(kernelBlowupSection a) Q)

and deduces that integral kernel coefficient divisibility is invariant under
an arbitrary affine source translation.

Applying this to the canonical recentering shows that every recentered rigid
source admits coordinate-3 slope `1`.

## Endgame collapse

Consequently `HasRigidClosingZeroCommonKernelSlopeObstruction` is impossible.
The canonical rigid frontier is sharpened to exactly

    rank-two repair progress
      OR
    concrete strict polynomial-family kernel restart.

The next remaining interface is therefore global restart re-entry/assembly,
not another local slope or Schur branch.
