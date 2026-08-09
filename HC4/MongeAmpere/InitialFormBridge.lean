import HC4.MongeAmpere.PolynomialInitial
import HC4.Newton.FirstContactArithmetic

/-!
# Initial-form bridge for the first-contact Hessian

The remaining geometric compatibility statement in the paper says that a
specific exact weighted component of the full Hessian determinant is the
Hessian determinant of the first-contact form.  This module packages that
compatibility as a precise predicate and proves the complete algebraic
consequence: under `det Hess = 1`, the first-contact Hessian determinant
vanishes.  The final theorem inserts the already verified first-contact
positivity arithmetic.
-/

namespace HC4.MongeAmpere

noncomputable section

variable {σ K : Type*}
variable [Fintype σ] [DecidableEq σ]
variable [CommRing K] [Nontrivial K]

/-- The exact determinant-component compatibility required at first contact. -/
def HasInitialHessianDeterminant
    (w : σ → ℤ) (c : ℤ)
    (ψ H : MvPolynomial σ K) : Prop :=
  HC4.Polynomial.initialForm w c
      (HC4.Polynomial.hessianDeterminant ψ) =
    HC4.Polynomial.hessianDeterminant H

/-- A nonzero-weight compatible initial Hessian determinant vanishes. -/
theorem initial_hessianDeterminant_eq_zero
    {w : σ → ℤ} {c : ℤ} {ψ H : MvPolynomial σ K}
    (hMA : IsPolynomialMongeAmpere ψ)
    (hc : c ≠ 0)
    (hcompat : HasInitialHessianDeterminant w c ψ H) :
    HC4.Polynomial.hessianDeterminant H = 0 := by
  rw [← hcompat]
  exact initialForm_hessianDeterminant_eq_zero hMA hc

/-- At the Newton first-contact weight, compatibility forces a degenerate initial Hessian. -/
theorem first_contact_hessianDeterminant_eq_zero
    {w : σ → ℤ} {m lam : ℕ} {ψ H : MvPolynomial σ K}
    (hm : 3 ≤ m) (hlam : lam ≤ m - 3)
    (hMA : IsPolynomialMongeAmpere ψ)
    (hcompat : HasInitialHessianDeterminant w
      ((4 * m - 8 - 2 * lam : ℕ) : ℤ) ψ H) :
    HC4.Polynomial.hessianDeterminant H = 0 := by
  have hposNat : 0 < 4 * m - 8 - 2 * lam :=
    HC4.Newton.first_contact_determinant_weight_pos hm hlam
  have hc : ((4 * m - 8 - 2 * lam : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hposNat)
  exact initial_hessianDeterminant_eq_zero hMA hc hcompat

end

end HC4.MongeAmpere
