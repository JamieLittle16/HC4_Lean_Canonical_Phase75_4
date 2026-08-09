# Phase 75.8.5 — Explicit Constant-Coefficient Evaluation Fix

This is a surgical follow-up to Phase 75.8.4.

`FirstSchurDepartureBridge.lean` previously discharged the nonzero constant
coefficient of the left-pivot clearing factor with a `simpa` involving
`Polynomial.C_pow`.  In the pinned Lean/mathlib environment that simplification
can recurse until `maxRecDepth` is reached.

The replacement proof is explicit and nonrecursive:

1. rewrite coefficient zero as evaluation at zero using
   `Polynomial.coeff_zero_eq_eval_zero`;
2. evaluate the product, power and constant polynomial with
   `Polynomial.eval_mul`, `Polynomial.eval_pow`, and `Polynomial.eval_C`;
3. rewrite the remaining evaluation of `activeDet` back to coefficient zero;
4. finish with the already-proved scalar product nonvanishing `hprod`.

No theorem statement, hypothesis, or mathematical content changes.
No `sorry`, `admit`, or `unsafe` is introduced.
