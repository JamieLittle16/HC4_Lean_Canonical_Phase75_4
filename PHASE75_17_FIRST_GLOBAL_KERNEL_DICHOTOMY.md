# Phase 75.17 — First Global Kernel Dichotomy

This phase replaces the bare rigid-closing branch by a source-level first
kernel stage on the canonically recentered exact-collision family.

For the chart-independent residual coordinate `3` and the first common
zero-Schur order `e`, finite support gives an exhaustive coefficientwise
alternative:

1. every source coefficient is divisible by the power required for the
   integral coordinate-3 kernel blow-up; or
2. an actual supported monomial has parameter order strictly below the
   required value `e * d(3)`.

In the integral branch the existing certified kernel-blow-up machinery:

- constructs the polynomial family explicitly;
- preserves the exact moving gradient collision;
- preserves the canonical right special point `e0`;
- drops the determinant defect by exactly `2*e`;
- identifies the new defect with the residual zero-Schur clock.

The closing clock therefore splits the integral branch into:

- residual defect zero (direct terminal first stage); or
- positive residual defect (retained second-stage clock).

In the offender branch, the proposed slope `e` is proved non-admissible.
The maximal admissible integral slope is therefore strictly below `e`.
Existing maximal-slope machinery then gives an exhaustive refinement:

- maximal slope zero: retain the explicit zero-common-kernel-slope
  anisotropic obstruction; or
- maximal slope positive: construct a concrete
  `PolynomialFamilyKernelRestartCertificate` for the actual transformed
  family and moving sections, hence a certified strict restart.

The assembled canonical frontier theorem is:

`CanonicalSmithDepartureFrontier.rankTwoProgress_or_firstKernelEndgameResolution`

so a bare rigid-closing proposition no longer appears at this level.

No `sorry`, `admit`, `unsafe`, or new `axiom` is introduced.
