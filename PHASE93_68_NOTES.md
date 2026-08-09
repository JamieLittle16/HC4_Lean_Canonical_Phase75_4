# Phase 93.68 — Genuine aligned Smith endpoint

Built over the green Phase 93.67.2 tree.

This phase removes the artificial sentinel cap from the mathematical
endpoint statement.

## Genuine first wall

`alignedSmithGenuineWalls` is exactly the union of:
- negative coefficient walls;
- left-section walls;
- right-section walls.

When nonempty, `alignedSmithGenuineFirstWall` is its actual minimum.

The patch proves:
- exact wall membership/witness extraction;
- coefficient aligned order is exactly zero at a coefficient wall;
- section aligned order is exactly zero at a section wall;
- all coefficients and both sections remain integral up to the genuine
  first wall;
- the actual transformed family and marked sections exist;
- pure Hessian defect and exact collision survive there.

## No-wall rigidity

If the genuine wall set is empty:
- every source Smith derivative is nonnegative;
- every transverse coordinate of both moving sections is identically zero.

## General common-factor defect budget

The Phase 93.61 estimate is generalised:

    HasCommonParameterFactor n P
    and det Hess(P) = X^Delta
      => 4*n <= Delta.

## Infinite Smith ray is impossible

If every supported Smith derivative were strictly positive, parity from
Phase 93.66 upgrades it to at least `2`.

At step

    N = 3*Delta + 1

after the one ramification by twenty, every normalised coefficient then has
a common factor `X^(2*N)`.

The general common-factor budget would give

    8*N <= 20*Delta,

contradicting the chosen `N`.

Therefore the no-wall branch contains an actual supported source monomial
of Smith derivative zero.

## Headline endpoint dichotomy

`alignedSmith_genuineEndpoint_dichotomy` says:

- genuine first coefficient/left-section/right-section wall; or
- no walls, both moving sections are exactly axial, and an actual
  zero-Smith-grade source monomial exists.

This is scale-safe and contains no artificial cap.

Remaining local endpoint work:
1. show a coefficient-wall primitive coefficient survives on the transformed
   special fibre, hence gives symmetric Smith minimality directly;
2. in the no-wall zero-grade branch, remove the finite common parameter
   order of a minimal zero-grade coefficient so it survives on the special
   fibre;
3. interpret a section wall as the appropriate next collision/endpoint
   datum.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
