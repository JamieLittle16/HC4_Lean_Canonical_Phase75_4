import HC4.Newton.TerminalTwoZeroDoublingForm
import HC4.Newton.TwoZeroBlockDeterminant
import HC4.Polynomial.HessianDeterminant
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Hessian determinant square on the two-zero terminal face

For

    F = X₂ A(X₀,X₁) + X₃ C(X₀,X₁),

the Hessian has the exact block form proved in
`TwoZeroBlockDeterminant`.  Therefore

    det Hess(F) = (A₀ C₁ - A₁ C₀)^2.

This is a polynomial identity in the original four-variable ring.  It is
the algebraic heart of the planar Keller reduction.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

/- These two imported reflexive simp lemmas rewrite `pderiv 2 F` to
`standardTwoZeroA F` and `pderiv 3 F` to `standardTwoZeroC F`.  In this
module we deliberately unfold `standardTwoZeroA/C` while expanding a 4x4
matrix, so leaving both directions active makes the simplifier loop. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- Ambient planar cross determinant attached to the two coefficient
polynomials. -/
def standardTwoZeroCrossDet
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv 0 (standardTwoZeroA F) *
      MvPolynomial.pderiv 1 (standardTwoZeroC F) -
    MvPolynomial.pderiv 1 (standardTwoZeroA F) *
      MvPolynomial.pderiv 0 (standardTwoZeroC F)

/-- Explicit Hessian block model for the standard two-zero face. -/
def standardTwoZeroHessianModel
    (F : MvPolynomial (Fin 4) K) :
    Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) K) :=
  twoZeroHessianBlockMatrix
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
      (standardTwoZeroC F))

/-- The actual polynomial Hessian equals the explicit two-zero block model. -/
theorem standardTwoZero_hessian_eq_model
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    HC4.Polynomial.hessian F =
      standardTwoZeroHessianModel F := by
  have hpp :=
    standardTwoZero_positivePositiveHessian_zero
      hd hhom
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

/-- Exact Hessian-determinant square identity on the standard two-zero face. -/
theorem standardTwoZero_hessianDeterminant_eq_crossDet_sq
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    HC4.Polynomial.hessianDeterminant F =
      (standardTwoZeroCrossDet F)^2 := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [standardTwoZero_hessian_eq_model hd hhom]
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
