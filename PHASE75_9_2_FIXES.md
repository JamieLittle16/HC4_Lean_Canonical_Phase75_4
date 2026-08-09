# Phase 75.9.2 — Smith-Rees explicit branch fix

This patch changes only `HC4/Valuation/CanonicalSmithReesSpecialFiber.lean`.

It repairs the four failures reported after Phase 75.9.1 without changing any theorem statement or adding assumptions:

1. Gives both `Polynomial.X` power-factorisation lemmas the explicit type `Polynomial K`, eliminating stuck `HMul` metavariables.
2. In the positive Smith-clock branch, derives the concrete natural-number inequality `raw - 4 ≠ 0` before simplification.
3. Replaces the dependent rewrite through `mem_smithSymmetricBalancedSubface` by explicit separator-zero / separator-nonzero cases and direct subface membership proofs.

No `sorry`, `admit`, or `unsafe` is introduced.
