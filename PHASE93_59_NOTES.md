# Phase 93.59 — Integral Smith conformal covariance

Built over the green Phase 93.58.1 tree.

This phase supplies the missing algebraic realisation of the two-parameter
Smith valuation tilt as an honest polynomial-family transformation.

## Canonical Smith action

For nonnegative integral `(theta1, theta2)` the source diagonal is

    D = diag(1, tau^theta1, tau^theta2, tau^(theta1+theta2))

and the conformal multiplier is

    mu = tau^(theta1+theta2).

The formal normalised action is

    Q(Y) = mu^(-1) P(DY).

No negative powers are formed in Lean.

## Coefficient construction

`HasIntegralSmithConformalCoefficientDivisibility` is precisely the
coefficientwise condition making the normalised transform integral.

`integralSmithConformalFamily` reconstructs the transform explicitly from
chosen quotient coefficients.

The main exact identity is

    smithConformalInflateHom P = C(mu) * Q.

## Connection to the existing Smith valuation package

`smithConformalRawExponent_sub_multiplier_eq_gradeDot` proves that the
parameter-order change of the exact polynomial action is literally

    theta · Gamma

for the already formalised relative Levi grade

    Gamma = (b+d-1, c+d-1).

Thus this file is the algebraic bridge from
`SmithValuationTiltAdapter` to a genuine conformal Rees move.

## Determinant

The chain rule is proved internally.  The determinant of the source diagonal
is `mu^2`, so source inflation contributes `mu^4`.

Multiplication of the potential by `mu` also contributes `mu^4`.

After cancellation:

    det Hess(Q) = Inflate(det Hess(P)).

In particular a pure defect `tau^Delta` is preserved exactly.

## Marked collision

An integral inverse source change is constructed coefficientwise for each
moving section.  The derivative covariance is

    mu * d_i Q(a') = D_i * d_i P(a).

Hence exact equality of the source gradient at two sections survives the
normalised Smith move after cancelling the common nonzero multiplier.

## What remains

This file does not assume or assert pole-minimality.  It proves that once a
denominator-cleared Smith separator satisfies:
- coefficient integrality; and
- marked-section integrality,

the separator is an honest determinant-preserving exact-collision move.

The next adapter should use finite ramification plus pole-depth minimality to
show that any separator forbidden by
`IsPoleMinimalAgainstSmithSeparators` would satisfy exactly these integrality
conditions and produce a strictly better normalisation.  That will connect
the zero-kernel-slope branch to the already-green Smith classifier without a
new saturation axiom.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
