# Phase 93.64 — Binary Smith order extraction

Built over the green Phase 93.63.2 tree.

The fixed symmetric Smith branch only needs a binary coefficient-order
certificate.

## Binary base

`smithBinaryBase P e` is:
- `0` if some family coefficient in projected Smith class `e` has nonzero
  constant coefficient;
- `1` otherwise.

`smithBinaryBase_coefficientOrderLowerBound` proves automatically that

    X^(smithBinaryBase P (projection d)) | coeff_d(P)

for every source monomial.

The base-one case uses Mathlib's exact theorem

    Polynomial.X_dvd_iff.

## Special-fibre support

`smithProjectedSupport_specialFiber_iff` identifies the local
field-valued projected support of `polynomialFamilySpecialFiber P` exactly
with the family projected classes whose binary base is zero.

Thus no abstract valuation-support identification is assumed.

## Strict improvement extension

If the symmetric separator strictly improves every class visible on the
special fibre, then it strictly improves every family class under the
binary base.

- base 0: use the special-fibre hypothesis;
- base 1: the denominator contributes `10`, while
  `smithSeparatorDelta 1 1 e >= -4`, so the tilted value is positive
  automatically.

The theorem is

    strictSymmetricImprovement_specialFiber_extends_family.

## Canonical dichotomy

`specialFiber_symmetricMinimal_or_familyStrictImprovement` gives:

    special fibre symmetric-minimal
      OR
    full family strict symmetric improvement.

The strict branch plugs directly into Phase 93.63 via

    specialFiber_notSymmetricMinimal_exactCollision_and_strictRestart.

This removes the remaining abstract coefficient-order input from the
complementary Smith restart.

The local-minimal branch still needs the actual zero-slope first-wall
normalisation data: homogeneity, axis-normalised special collision, and
nonempty/attained special-fibre support.  Those are the next dispatcher
inputs to extract/connect.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
