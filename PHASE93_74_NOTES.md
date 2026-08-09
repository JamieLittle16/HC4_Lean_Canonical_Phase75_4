# Phase 93.74 — separated right-wall scale descent

Built over green Phase 93.73.3.

This patch attacks the entire remaining Smith scale theorem in one file.

## Headline

    separatedRightSmithWall_strictCanonicalGeometricRestart

Every separated right Smith section wall returns a canonical homogeneous
exact-collision family over the original parameter ring with strictly
smaller determinant defect.

The proof has two arithmetic branches.

### Ten-aligned branch

If the first wall step is `10*m` (all y/z walls and even-order w walls),
the once-ramified inequalities divide exactly to an honest unramified
symmetric Smith move of size `m`.

The separated margin gives one unramified common parameter factor, hence

    Delta -> Delta - 4.

### Odd w branch

If the w-coordinate order is odd, write it as `2*l+1`.

Use the smaller honest symmetric Smith move of size `l`.
After that move all three transformed transverse section coordinates still
contain one factor of the parameter.

Inflate y,z,w once and extract a common `X^2` from the potential.
The exact determinant bookkeeping is

    Delta -> Delta + 6 -> Delta - 2.

This gives the strict unramified restart without any repeated denominator
clearing.

Phase 93.73's determinant-one pointed shear then restores the canonical
right special point `e0`.

## Closed zero-slope theorem

The patch also exposes

    alignedSmith_zeroSection_closedGeometricStep

with only two outcomes:

    canonical local repair/terminal
      OR
    strict canonical geometric defect restart.

No separated/coupled/scale Smith wall remains in this statement.

No `sorry`, `admit`, `axiom`, or `unsafe` is introduced.
