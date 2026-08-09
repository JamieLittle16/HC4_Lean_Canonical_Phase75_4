# Phase 93.63 — Strict symmetric Smith improvement restart

Built over the green Phase 93.62 tree.

This phase closes the complementary algebraic branch of the canonical
symmetric Smith dichotomy on one fixed ramification scale.

## Fixed scale

The only Smith separator used by the canonical local classifier is
`(k,l)=(1,1)`, whose:
- integral direction is `(2,2)`;
- clearing denominator is `10`;
- conformal multiplier exponent is `4`.

## Coefficient order package

`HasSmithCoefficientOrderLowerBound base P` records the concrete
coefficientwise lower bound

    tau^(base(projection d)) | coeff_d(P).

After ramification by ten, these orders become `10*base`.

A strict symmetric improvement at old minimum zero gives

    5 <= rawExponent(2,2,d) + 10*base(projection d).

Thus four powers pay for the Smith conformal multiplier and at least one
parameter factor remains.

## Integral Smith action

`strictSymmetricImprovement_integralSmithDivisibility` proves that the
once-ramified family satisfies the exact Phase 93.59 coefficient
divisibility required for the integral `(2,2)` conformal transform.

`strictSymmetricImprovement_commonParameterFactor` then proves the resulting
normalised family has `HasCommonParameterFactor 1`.

## Moving sections

`HasSmithTransverseParameterFactor` asks that the three transverse section
coordinates have one parameter factor before ramification.

After ramification by ten this is enough for the inverse `(2,2)` source
change, including the weight-four `w` coordinate.

## End-to-end restart

`strictSymmetricImprovement_exactCollision_and_strictRestart` proves on the
fixed ramified defect scale:

    source defect = 10*Delta
       -> target defect = 10*Delta - 4,

while preserving exact polynomial-family gradient collision and producing
strict `GlobalRestartProgress`.

The branch is therefore:

    strict symmetric Smith improvement
      -> ramify once by 10
      -> integral (2,2) Smith transform
      -> common parameter factor
      -> exact collision preserved
      -> strict defect restart.

## Remaining global wiring

The canonical Smith dichotomy is now algebraically complete:

- symmetric minimality -> Phase 93.62 local repair/terminal classifier;
- strict symmetric improvement -> this Phase 93.63 strict restart.

The remaining dispatcher must connect an actual zero-kernel-slope
first-wall datum to the concrete natural coefficient-order certificate
`base`, old minimum `0`, and the corresponding special-fibre exact-axis
polynomial consumed by the local Smith classifier.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
