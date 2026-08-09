# Phase 93.73 — Pointed shear continuation

Built over green Phase 93.72.2.

## What this phase removes

Phase 93.72 named

    HasCanonicalContinuationFromSeparatedRightWall

because a separated right Smith wall moves the right special point from
`e0` to `(1,Y,Z,W)`.

This phase removes that pointed-coordinate interface using determinant-one
unipotent shears.

## Elementary shear

For transverse `k != 0`:

    X_k -> X_k + c X_0

with inverse moving-section change

    a_k -> a_k - c a_0.

The Lean file proves:

- exact evaluation covariance;
- preservation of ordinary source homogeneity;
- first-order source chain rule;
- exact Hessian congruence using transvections;
- determinant-one Hessian determinant preservation;
- exact family-gradient collision preservation.

## Canonical pointed normalisation

Three shears in coordinates `1,2,3` kill the three transverse special
coordinates while leaving the longitudinal coordinate unchanged.

Thus every right special point whose coordinate `0` equals `1` is sent
exactly to `coordinateAxisPoint 0`.

## Separated right wall

After the green Phase-93.72 `X^10` extraction, the left first-wall section
is proved to remain identically zero.

The right section has longitudinal special coordinate `1`.

The three-shear normalisation therefore gives a new family/section with:

- ordinary degree `D`;
- exact defect `20*(Delta-2)`;
- exact collision from the zero section;
- right special point exactly `e0`.

The theorem

    hasCanonicalContinuationFromSeparatedRightWall_of_geometricData

therefore proves the previously named Phase-93.72 continuation proposition
from the actual geometric hypotheses.

## Remaining recursion issue

This patch does **not** claim that `20*(Delta-2)` is already a recursive
defect smaller than `Delta`.

That is a separate scale problem.

To make it finite and explicit, the patch splits the only remaining
separated wall into:

1. `HasSeparatedYZRightSmithSectionWall`;
2. `HasSeparatedWOnlyRightSmithSectionWall`.

The y/z branch has the green `X^20` extraction from Phase 93.72.  The
w-only branch is now the unique exceptional scale branch to be attacked
locally.

No `sorry`, `admit`, `axiom`, or `unsafe` is introduced.
