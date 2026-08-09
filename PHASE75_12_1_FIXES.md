# Phase 75.12.1 — explicit constant-derivative normalisation

This patch fixes the first compile pass of `RigidPacketEvaluatedHessianChart.lean`.

Changes:
- prove the three `Fin 4` coordinate inequalities by decidability;
- normalise numeral multivariate polynomials through `MvPolynomial.C_eq_coe_nat`;
- simplify their partial derivatives using `MvPolynomial.pderiv_C`;
- use `ring_nf` after the Hessian entries have actually been evaluated.

No theorem statement or mathematical hypothesis is changed.
