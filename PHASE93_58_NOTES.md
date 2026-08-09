# Phase 93.58 — Maximal integral kernel-slope extraction

Built against the green Phase 93.57 final-extraction checkpoint.

This phase formalises the actual integral Newton-slope choice after
ramification; it does not introduce a restart hypothesis.

## Main construction

For an active kernel coordinate, an integral slope `q` is admissible iff
every source coefficient of kernel degree `r` is divisible by `tau^(q*r)`.

A fixed active coefficient bounds every admissible slope by its polynomial
degree, so the admissible slopes form a nonempty finite set.

`maximalIntegralKernelSlope` is the maximum of this set.

## Main theorems

- `maximalIntegralKernelSlope_divisibility`
- `admissibleIntegralKernelSlope_le_maximal`
- `maximalIntegralKernelSlope_eq_zero_iff`
- `maximalIntegralKernelSlope_zero_or_positive`

Thus the exact global algebraic dichotomy is now:

    q = 0
      <-> no positive admissible integral kernel slope exists,

or

    q > 0
      and coefficient divisibility holds automatically.

## Positive branch

`maximalIntegralKernelSlope_exactDefect_and_strictRestart` plugs the
selected positive slope directly into the green Phase 93.57 theorem and
returns:

- exact target Hessian defect `Delta - 2q`;
- exact special-fibre collision;
- strict numerical defect drop;
- `GlobalRestartProgress`.

No separate slope choice, divisibility theorem, or defect-drop certificate
is required.

## Zero branch

`maximalIntegralKernelSlope_zero_identity` proves the explicit blow-up
family and moving section are literally unchanged. Hence zero slope is not
mistaken for a restart.

## Remaining geometric interface

The remaining global step is now narrower still: starting from the actual
normalised collision datum, choose an active kernel coordinate and prove
either:
- the positive maximal slope retains distinct special marked points; or
- the zero-slope current special fibre satisfies the pole-minimal Smith
  first-wall hypotheses already consumed by `RestartClassification`.

That is the genuine global normalisation/pole-minimality adapter; this file
does not disguise it as an assumption.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
