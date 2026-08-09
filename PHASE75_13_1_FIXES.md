# Phase 75.13.1 — Quadratic Hessian API fix

This patch repairs the compile errors in `HC4.Valuation.QuadraticFamilyCollision` without changing its theorem statements or mathematical assumptions.

Changes:

- use the project Hessian definition `HC4.Polynomial.hessian` (the project does not define `MvPolynomial.hessian`);
- unfold the actual Hessian/mapped-matrix definitions in the second-derivative constant-term step instead of relying on `rfl`;
- transport the determinant through `MvPolynomial.constantCoeff` using `RingHom.map_det` applied to `HC4.Polynomial.hessian P`.

No `sorry`, `admit`, `unsafe`, or new axioms are introduced.
