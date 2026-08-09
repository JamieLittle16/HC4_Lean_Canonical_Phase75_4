# Phase 93.56.1 — Lean API / elaboration fixes

The first Phase 93.56 build exposed several proof-shape issues. This patch
keeps all theorem statements and the determinant argument unchanged.

## Fixes

1. `eval_kernelInflateHom`
   - explicitly changes the `eval₂Hom` application to its underlying
     `MvPolynomial.eval₂` form before using `MvPolynomial.eval_assoc`.

2. `pderiv_kernelInflateHom`
   - uses `apply MvPolynomial.induction_on Q`, matching Mathlib's actual
     induction principle `(C, add, mul_X)`.

3. `hessian_kernelInflateHom_entry`
   - applies the first chain rule to the inner derivative index `i`, then
     the second to the outer derivative index `j`, matching HC4's Hessian
     definition.

4. `prod_kernelInflateDerivativeCoefficient`
   - explicitly annotates the target as
     `MvPolynomial (Fin 4) (Polynomial K)` so the source-variable type is
     inferable in the theorem header.

5. Hessian matrix equality
   - uses exactly one level of `Matrix.ext` and then the entry theorem,
     avoiding recursive polynomial extensionality.

6. Determinant scaling
   - records `Matrix.det_mul_row` and `RingHom.map_det` as explicit helper
     equalities before the calculation, avoiding brittle `rw` matching.

No mathematical assumption is added or weakened.
