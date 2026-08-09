# Phase 93.60 — Parameter ramification and Smith denominator clearing

Built over the green Phase 93.59.1 tree.

The handwritten pole-minimality argument uses a rational small Smith tilt
and then clears its denominator.  This phase formalises that denominator
clearing as the actual coefficient-ring base change

    tau -> s^D.

## Main algebra

`parameterRamificationHom` is polynomial composition with `X^D`.

The phase proves:

- `parameterRamificationHom_X_pow`
- `parameterRamification_pow_dvd`
- `eval_parameterRamificationFamily`
- `polynomialFamilyExactGradientCollision_parameterRamification`
- `hessianDeterminant_parameterRamificationFamily`
- `parameterRamificationFamily_hasHessianDefect`

Thus exact collision survives ramification and the pure defect changes by

    Delta -> D * Delta.

## Divisibility transport

Generic packages

- `HasParameterCoefficientDivisibility`
- `HasParameterSectionDivisibility`

are transported with all required orders multiplied by `D`.

This is the exact bridge needed to convert denominator-cleared Smith
valuation inequalities into the coefficient/section divisibility hypotheses
of Phase 93.59.

## Smith denominator

`smithSeparatorRamificationIndex k l` is exactly

    finiteTiltDenominator (smithExtremeSeparatorBound k l),

and is proved positive.

## Pole-minimality logic

`HasStrictSmithSeparatorImprovement` packages the statement that one
denominator-cleared Smith separator raises every supported rescaled value.

The theorem

    isPoleMinimalAgainstSmithSeparators_iff_no_strictImprovement

shows that the existing finite pole-minimality predicate is exactly the
absence of such a strict denominator-cleared improvement.

## Remaining global step

After this phase, the remaining pole-minimal adapter is no longer an
algebraic covariance problem.  It must identify the actual Laurent/pole
normalisation data with:

1. the `base` valuations and minimum `m`;
2. the coefficient/section divisibility packages above after the Smith
   ramification index;
3. a minimal pole-depth representative, so a strict improvement contradicts
   the chosen minimality.

No `sorry`, `admit`, `axiom`, or `unsafe` declaration is introduced.
