import HC4.Newton.TerminalTwoZeroHessianSquare
import Mathlib.Tactic

/-!
# A19.2: Hessian square for an arbitrary planar doubling form

The terminal two-zero theorem was originally stated behind weighted
homogeneity because that is how the old terminal endpoint produced the
normal form.  For the final HC4/JC2 interface this is stronger than needed.

Once a polynomial is already known to have the honest doubling form

    F = X₂ A + X₃ C,

with `A,C` supported only in `X₀,X₁`, its positive-positive Hessian block
vanishes directly.  Therefore the same block determinant calculation gives

    det Hess(F) = (A₀ C₁ - A₁ C₀)^2

without any weight assumption.  This is the exact algebraic bridge needed to
embed an arbitrary planar Keller map into the four-dimensional Hessian
problem; no Jacobian-conjecture hypothesis is used here.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- The support part of an honest doubling form already forces the complete
positive-positive Hessian block to vanish. -/
theorem standardTwoZero_positivePositiveHessian_zero_of_doublingForm
    {F : MvPolynomial (Fin 4) K}
    (hform : HasStandardTwoZeroDoublingForm F) :
    MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 2 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 2 F) = 0 ∧
      MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 3 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 3 F) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change MvPolynomial.pderiv 2 (standardTwoZeroA F) = 0
    exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        2 (standardTwoZeroA F)
        (fun m hm => (hform.2.1 m hm).1)
  · change MvPolynomial.pderiv 3 (standardTwoZeroA F) = 0
    exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        3 (standardTwoZeroA F)
        (fun m hm => (hform.2.1 m hm).2)
  · change MvPolynomial.pderiv 2 (standardTwoZeroC F) = 0
    exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        2 (standardTwoZeroC F)
        (fun m hm => (hform.2.2 m hm).1)
  · change MvPolynomial.pderiv 3 (standardTwoZeroC F) = 0
    exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        3 (standardTwoZeroC F)
        (fun m hm => (hform.2.2 m hm).2)

/-- The actual Hessian of any honest doubling form is the standard two-zero
block matrix. -/
theorem standardTwoZero_hessian_eq_model_of_doublingForm
    {F : MvPolynomial (Fin 4) K}
    (hform : HasStandardTwoZeroDoublingForm F) :
    HC4.Polynomial.hessian F =
      standardTwoZeroHessianModel F := by
  have hpp :=
    standardTwoZero_positivePositiveHessian_zero_of_doublingForm hform
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HC4.Polynomial.hessian_apply,
      standardTwoZeroHessianModel,
      twoZeroHessianBlockMatrix,
      standardTwoZeroA,
      standardTwoZeroC,
      hpp.1, hpp.2.1,
      hpp.2.2.1, hpp.2.2.2] <;>
    try rw [pderiv_comm_backport]

/-- **General two-zero Hessian-square identity.**
Weighted homogeneity is not required once the exact doubling form is known. -/
theorem standardTwoZero_hessianDeterminant_eq_crossDet_sq_of_doublingForm
    {F : MvPolynomial (Fin 4) K}
    (hform : HasStandardTwoZeroDoublingForm F) :
    HC4.Polynomial.hessianDeterminant F =
      (standardTwoZeroCrossDet F)^2 := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [standardTwoZero_hessian_eq_model_of_doublingForm hform]
  simpa [standardTwoZeroHessianModel,
    standardTwoZeroCrossDet] using
    (det_twoZeroHessianBlockMatrix
      (MvPolynomial.pderiv 0
        (MvPolynomial.pderiv 0 F))
      (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 0 F))
      (MvPolynomial.pderiv 0
        (MvPolynomial.pderiv 1 F))
      (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 1 F))
      (MvPolynomial.pderiv 0
        (standardTwoZeroA F))
      (MvPolynomial.pderiv 1
        (standardTwoZeroA F))
      (MvPolynomial.pderiv 0
        (standardTwoZeroC F))
      (MvPolynomial.pderiv 1
        (standardTwoZeroC F)))

end

end HC4.Newton
