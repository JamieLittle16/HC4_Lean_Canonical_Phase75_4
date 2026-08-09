# Phase 93.54 — Derivative and collision covariance

Built on green Phase 93.53.1.

## Main new identities

For `i != kernel`:

    eval blowup(a) (pderiv i Ptilde)
      =
    eval a (pderiv i P).

For the kernel coordinate:

    tau^slope * eval blowup(a) (pderiv kernel Ptilde)
      =
    eval a (pderiv kernel P).

Both are proved monomial-by-monomial and summed over the exact support of
the original family.

## Full collision transport

`polynomialFamilyExactGradientCollision_integralKernelBlowup`

proves:

    HasPolynomialFamilyExactGradientCollision P a b
      ->
    HasPolynomialFamilyExactGradientCollision
      Ptilde (blowup a) (blowup b).

The kernel component cancels the common nonzero polynomial factor
`tau^slope`; no localisation or Laurent polynomial ring is used.

This closes the derivative/evaluation collision-preservation part of the
concrete integral kernel blow-up.

## Remaining global work

Once this phase is green, Phase 93.51 can specialise the transported
collision to `tau = 0` and package it with any proved positive defect drop
as `GlobalRestartProgress`.

The remaining substantive global theorem is therefore the geometric
one-step extraction: obtain the divisibility/slope/defect data from an
actual nonterminal HC4 restart datum, or classify the zero-slope case into
the already-green Smith/local restart machinery.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
