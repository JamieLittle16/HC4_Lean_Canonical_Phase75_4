# Phase 93.49 — Linear covariance

This phase implements the first item of the safe valuation algebra layer.

## Exact matrix identities
For 4x4 matrices:

    Hess' = D^T Hess D

implies

    det Hess' = det(D)^2 det(Hess).

For the conformally normalised transform

    Hess' = mu^(-1) D^T Hess D,

Lean proves

    det Hess' = mu^(-4) det(D)^2 det(Hess).

Hence if

    det(D)^2 = mu^4

and `mu != 0`, the Hessian determinant is preserved exactly.

## Collision covariance
The module defines the exact evaluated gradient pullback

    x |-> mu^(-1) D^T grad(F)(D x)

and proves that equality of the original gradients transports to equality
of the pulled-back gradients.

`HasNormalizedGradientCovariance mu D F P` records the concrete identity
for a transformed polynomial `P`.

From that identity, an exact gradient collision of `F` at `Dp,Dq`
automatically gives an exact gradient collision of `P` at `p,q`.
A companion theorem also transports distinctness.

## Scope boundary
This phase does not postulate that a kernel blow-up polynomial has the
covariance formula.  Phase 93.50 should prove that for the actual
polynomial-family transformation using the existing valuation/special-fibre
machinery.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
