# Phase 93.74.2 — final local elaboration fix

Phase 93.74.1 reduced the scale-descent file to six local elaboration
errors.

This patch changes no mathematical statement.

## Fixes

1. `kernelInflateHom_unit_hasHessianDefect_add_two`

   Instead of rewriting `MvPolynomial.C_pow` and `MvPolynomial.C_mul` in
   one direction inside the target, apply `MvPolynomial.C` to the already
   proved polynomial identity

       X^2 * X^Delta = X^(Delta+2)

   and normalize both the generated equality and the goal with `simpa`.

2. Canonical special coordinate in the ten-aligned branch

   The local name `bQ` is a `let`.  The goal now explicitly changes to

       constantCoeff (integralSmithConformalSection m m b hbDiv 0) = 1

   before applying `integralSmithConformalSection_zeroCoordinate`.

3. Canonical special coordinate in the odd-w branch

   The same explicit unfolding is used for `bS`.

4. Final wall parity splitter

   Remove three `dsimp [hwall] at hstep'` calls which Lean reports make no
   progress.  `hstep'` already has the needed normal form after the
   preceding `simp`; `omega` can consume it directly.

No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
