# Phase 93.74.1 — systematic elaboration fix

The first Phase 93.74 build exposed implementation issues rather than a
contradiction in the scale-descent arithmetic.

This patch repairs all diagnostic classes reported in that build:

- let-bound first-wall rewrites;
- `m+m` versus `2*m`;
- controlled polynomial-power reassociation;
- `X` versus `X^1`;
- divisibility witness orientation;
- exact `+2` Hessian defect under one source inflation;
- the actual `IsHomogeneous` coefficient-nonzero API;
- let-bound raw Smith exponent case analysis;
- coordinate-3 Smith source-exponent normalization;
- typed `Fin 4` coordinate rewrites;
- dependent section-divisibility rewrites;
- special-point coordinate-zero transport;
- natural-number parity splitting.

The odd branch is also strengthened internally to carry the *actual*
w-section wall equation.  This is not a new hypothesis of the public
theorem: `separatedRightWall_tenAligned_or_oddW` derives it from the
existing separated-section-wall certificate.  Carrying it explicitly
prevents later proofs from reconstructing a geometric fact indirectly from
the numerical equality `N = 5*(2*l+1)`.

The headline statements are unchanged in meaning:

    separatedRightSmithWall_strictCanonicalGeometricRestart

and

    alignedSmith_zeroSection_closedGeometricStep.

No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
