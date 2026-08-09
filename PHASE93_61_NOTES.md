# Phase 93.61 — Common parameter factor strict restart

Built over the green Phase 93.60.4 tree.

This phase formalises the key escape mechanism for a non-pole-minimal Smith
face.

If an integral Smith conformal transform raises every normalised coefficient
valuation, the transformed potential has a common parameter factor.

Rather than treat that as a same-defect conformal normalisation forever, we
extract the common factor.

## Main constructor

`HasCommonParameterFactor n P` means every nonzero source coefficient is
divisible by `tau^n`.

`commonParameterFactorFamily` reconstructs the quotient coefficientwise.

The exact polynomial identity is

    P = C(tau^n) * Q.

## Exact collision

`polynomialFamilyExactGradientCollision_commonParameterFactor` proves that
exact polynomial-family gradient collision survives common-factor extraction
by cancellation of the nonzero power `tau^n`.

## Four-dimensional defect drop

For one common parameter factor,

    P = tau * Q

implies

    det Hess(P) = tau^4 * det Hess(Q).

If the source defect is the pure power `tau^Delta`, Lean derives `4 <= Delta`
from divisibility and proves

    det Hess(Q) = tau^(Delta - 4).

## Global restart

`commonParameterFactor_one_strictGlobalRestart` turns this into strict
`GlobalRestartProgress`.

`commonParameterFactor_one_exactCollision_and_strictRestart` packages the
exact target defect, exact family collision, strict defect decrease, and
global restart in one theorem.

## Remaining adapter

The next step is now very precise:

- define the actual coefficient-order function on the ramified Smith family;
- show a strict denominator-cleared Smith improvement makes every coefficient
  of the integral 93.59 transform divisible by `tau`;
- show the pointed axis sections satisfy the 93.59 section-divisibility
  conditions after the large Phase 93.60 ramification.

Then:

    pole-minimal -> existing Smith local classifier
    not pole-minimal -> this strict defect restart.

No abstract pole-minimal normalisation hypothesis is required by that
dichotomy.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
