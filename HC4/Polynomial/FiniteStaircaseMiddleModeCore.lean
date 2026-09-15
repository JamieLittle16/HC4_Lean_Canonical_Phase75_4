import HC4.Polynomial.FiniteStaircasePureModeMixedDeterminant
import Mathlib.Tactic

/-!
# Exponent-Hessian cores on the middle one-fibre diagonal

For `j+1=k`, the common profile can have degree `k-1` or `k`.

* degree `k-1` has top exponent `(k-1,1,1,Vk)` and a nonzero full
  exponent-Hessian determinant;
* degree `k` has top exponent `(k,0,0,V(k-1))`, whose full determinant
  vanishes because two coordinates are missing.

These state-free identities separate the easy fourth-variation middle branch
from the genuinely degenerate top-mode branch.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {K : Type u} [CommRing K]

/-- Middle diagonal, lower degree `k-1`: exact nondegenerate core determinant. -/
theorem det_middleLowerDegreeMode_core
    (V k : K) :
    (fieldExponentHessianCore ![k - 1, 1, 1, V * k]).det =
      -(V * (V + 1) * k ^ 2 * (k - 1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [fieldExponentHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Middle diagonal, upper degree `k`: its top core is degenerate. -/
theorem det_middleUpperDegreeMode_core
    (V k : K) :
    (fieldExponentHessianCore ![k, 0, 0, V * (k - 1)]).det = 0 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [fieldExponentHessianCore, Matrix.det_fin_three, Fin.succAbove]

end

end HC4.Polynomial
