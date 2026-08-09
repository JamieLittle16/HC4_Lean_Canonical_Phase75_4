# Phase 87.1 fixes

Phase 87.1 is a compile-repair patch for `LogarithmicInfinityCertificate.lean`.
It does not change the mathematical statements introduced in Phase 87.

Repairs:

1. Import the module that actually defines
   `HC4.Polynomial.natDegree_eulerDerivative_le`.
2. Rewrite the reduced-source degree equality into the left top-coefficient
   identity before using it, so both coefficient indices are literally
   `D.natDegree + D.natDegree`.
3. Remove the invalid inference `D ∣ 0 -> D = 0`.  Instead, if `phi = 0`,
   simplify the canonical logarithmic source directly: its reduced denominator
   has degree zero, contradicting the positive-denominator-degree hypothesis.
4. Replace the predecessor/`omega` strict-degree step by a direct argument:
   degree is at most `2d`, but equality would make the leading coefficient equal
   to the already-proved zero coefficient at `2d`; hence equality is impossible.

No `sorry`, `admit`, project `axiom`, or `unsafe` is introduced.
