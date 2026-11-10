import HC4.Valuation.QuadraticTransverseCapSourceSections
import HC4.Valuation.QuadraticAxisReverseReesOriginRankTwo
import Mathlib.Tactic

/-!
# Source-origin transverse rank two is genuinely polynomial on the marked axis

The actual quadratic reverse-Rees source has a six-way nonzero transverse
2x2 origin-Hessian minor. The SOURCE-AXIS transverse block C(x) is a
matrix of polynomials, not a pointwise numerical Hessian. Its evaluation
at x=0 is exactly the original source-origin transverse Hessian.

Therefore the genuine source-origin witness gives a NONZERO POLYNOMIAL
2x2 minor of C, and permits a generic rank-two/rank-three split over
the polynomial coefficient domain. No associated-graded rank is confused
with the represented source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Evaluation at the longitudinal origin of the axis-restricted
source Hessian is exactly the original four-variable source-origin
Hessian coefficient. -/
theorem quadraticTransverseCapSource_axisHessian_origin
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    Polynomial.eval (0 : K)
      (((HC4.Polynomial.hessian F).map
        (longitudinalAxisRestrictionRingHom (K := K))) i j) =
      quadraticFamilyHessianMatrix F i j := by
  rw [Matrix.map_apply, longitudinalAxisRestrictionRingHom_apply]
  rw [← eval_finCons_zero_eq_longitudinalAxisRestriction]
  change
    MvPolynomial.eval
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i F)) =
    MvPolynomial.constantCoeff
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i F))
  have hzero :
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext k
    fin_cases k <;> rfl
  rw [hzero, MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]

/-- All entries of the ACTUAL polynomial transverse Hessian block,
evaluated at x=0, equal the corresponding original source-origin
transverse Hessian entries. -/
theorem quadraticTransverseCapSource_axisThreeBlock_origin
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    Polynomial.eval (0 : K)
      ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) =
      quadraticFamilyHessianMatrix F i.succ j.succ := by
  fin_cases i <;> fin_cases j <;>
    simp only [GeneralThreeBlock.matrix, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals
    simpa [quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralThreeBlock.matrix, GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F _ _)

end

end HC4.Valuation
