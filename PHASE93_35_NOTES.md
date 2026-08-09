# Phase 93.35 — one-zero affine recovery

Built against the clean Phase 93.34.3 tree.

Phase 93.34 proves

    S * (-S * Delta23) = 1

for

    S = pderiv 0 (pderiv 1 F).

## Unit slope is constant

The explicit inverse gives `IsUnit S`.

Mathlib's

    MvPolynomial.isUnit_iff_eq_C_of_isReduced

applies because a field is reduced, yielding

    S = C s

for a scalar unit `s`, hence `s != 0`.

This is stronger and cleaner than reducing first to a one-variable
polynomial.

## Affine gradient component

Let

    A = pderiv 1 F
    R = A - C s * X 0.

The Phase 93.34 sparse Hessian identities give the partials of A in
directions 1,2,3 equal to zero, while `S = C s` makes the partial in
direction 0 of R zero.

Thus all four partial derivatives of R vanish.

In characteristic zero, the project-local theorem

    exponent_eq_zero_of_pderiv_eq_zero

forces every supported monomial of R to have zero exponent in all four
coordinates.  Therefore R is constant.

Hence

    pderiv 1 F = C b + C s * X 0,

with `s != 0`.

## Coordinate recovery

If the gradient values at p and q agree in coordinate 1, evaluating the
affine formula gives

    b + s*p0 = b + s*q0.

Cancelling the nonzero scalar s yields

    p0 = q0.

So equal full gradients recover the unique zero-weight source coordinate.

The next one-zero phase can work fibrewise over this now-fixed X0 and
attack only the positive complementary coordinates 2,3; after those are
recovered, gradient coordinate 0 should recover X1.

No theorem from Phase 93.34 is weakened.
The characteristic-zero hypothesis is introduced only where derivative
rigidity genuinely requires it.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
