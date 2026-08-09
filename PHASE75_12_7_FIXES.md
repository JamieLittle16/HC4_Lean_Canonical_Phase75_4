# Phase 75.12.7 — Right-chart normalization and mixed-partial fix

This patch is a compile/performance repair for `RigidPacketZeroSchurBridge.lean`.
It changes no theorem statements or mathematical assumptions.

## Changes

1. `evaluatedFamilyHessian_coeff_zero` now first proves the coefficient identity
   in the mixed-partial order supplied by `polynomialFamilySpecialFiber_gradientComponent`,
   then uses the already-proved commutation theorem `pderiv_comm_commRing` to put
   the Hessian indices in the requested order.

2. Adds four explicit simp lemmas for `rigidRightChartPerm` on `Fin 4`:
   `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 1`, `3 ↦ 3`.

3. The four right-chart coefficient proofs no longer unfold
   `rigidRightChartPerm = Equiv.swap 1 2` inside huge Schur expressions.  They
   simplify using the four tiny permutation lemmas instead.  This is intended
   to eliminate the deterministic timeouts seen in the previous build.

No `sorry`, `admit`, `unsafe`, or axioms are introduced.
