# Phase 78.1 fixes

Phase 78 failed in `shiftedEuler_X_pow_succ_mul` because the simplifier expanded
`X^(n+1)` via `pow_succ` before `Polynomial.derivative_X_pow_succ` could fire.
The resulting goal contained `derivative (X^n)`, leaving `ring` with derivative
terms it cannot normalise.

Phase 78.1 changes only that proof.  It now:

1. unfolds `shiftedEuler` and `shiftedEulerCore`;
2. rewrites `Polynomial.derivative_mul`;
3. rewrites `Polynomial.derivative_X_pow_succ` while the power is still intact;
4. normalises casts with `push_cast`;
5. closes the remaining commutative-ring identity with `ring`.

No definitions, theorem statements, hypotheses, or downstream proofs changed.
