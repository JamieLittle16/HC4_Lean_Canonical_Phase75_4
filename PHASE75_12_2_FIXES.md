# Phase 75.12.2 — directed numeral-derivative normalization

Fixes the three recursion-depth failures in `RigidPacketEvaluatedHessianChart`.

The previous patch put `← MvPolynomial.C_eq_coe_nat` into `simp`; in the pinned
mathlib this can loop with `map_natCast`.  This patch instead proves once, using
directed `rw`, that `pderiv i (2 : MvPolynomial (Fin 4) K) = 0`, and supplies
that lemma to the three explicit Hessian calculations.

No theorem statements or mathematical assumptions change.
