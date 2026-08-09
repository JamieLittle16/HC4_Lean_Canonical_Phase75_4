import HC4.Polynomial.MaximalHessianInitial
import HC4.MongeAmpere.PolynomialInitial
import HC4.MongeAmpere.InitialFormBridge

/-!
# Constant-Hessian potentials and maximal weighted initial forms

This module removes the compatibility hypothesis introduced in Phase 45.
For an actual maximal exact weighted component, the compatibility is now a
theorem, and a positive determinant weight forces the initial Hessian to be
singular exactly as in Lemma 2.2 of the manuscript.
-/

namespace HC4.MongeAmpere

open scoped BigOperators

noncomputable section

variable {σ K : Type*}
variable [Fintype σ] [DecidableEq σ]
variable [CommRing K] [Nontrivial K]

/-- Maximal weighted initial forms automatically satisfy the Phase-45
compatibility predicate. -/
theorem hasInitialHessianDeterminant_of_isWeightLE
    (w : σ → ℤ) (m : ℤ) (ψ : MvPolynomial σ K)
    (hψ : HC4.Polynomial.IsWeightLE w m ψ) :
    HasInitialHessianDeterminant w
      ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
      ψ (HC4.Polynomial.initialForm w m ψ) := by
  exact HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
    w m ψ hψ

/-- Full Hessian initial-form lemma for constant-Hessian potentials. -/
theorem maximal_initial_hessianDeterminant_eq_zero
    (w : σ → ℤ) (m : ℤ) (ψ : MvPolynomial σ K)
    (hbound : HC4.Polynomial.IsWeightLE w m ψ)
    (hMA : IsPolynomialMongeAmpere ψ)
    (hpos : 0 < (Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm w m ψ) = 0 := by
  rw [← HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
    w m ψ hbound]
  exact initialForm_hessianDeterminant_eq_zero hMA (ne_of_gt hpos)

/-- Further maximal exposed initial forms of a zero-Hessian polynomial remain zero-Hessian. -/
theorem maximal_initial_hessianDeterminant_eq_zero_of_zero
    (w : σ → ℤ) (m : ℤ) (ψ : MvPolynomial σ K)
    (hbound : HC4.Polynomial.IsWeightLE w m ψ)
    (hzero : HC4.Polynomial.hessianDeterminant ψ = 0) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm w m ψ) = 0 := by
  exact HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
    w m ψ hbound hzero

end

end HC4.MongeAmpere
