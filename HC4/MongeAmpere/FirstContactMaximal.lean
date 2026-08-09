import HC4.MongeAmpere.MaximalInitial
import HC4.Newton.FirstContactArithmetic

/-!
# First-contact singularity without a compatibility assumption

The manuscript's contact weight is rational.  We therefore formulate the
main result after clearing denominators: `scale` is the common denominator,
`bump` is the extra weight in the omitted coordinate, and `level` is the
scaled contact level.  The inequality

    bump + 3 * scale ≤ level

is exactly the denominator-cleared form of `λ ≤ m - 3` needed to keep the
quadratic part strictly below the contact face.
-/

namespace HC4.MongeAmpere

open scoped BigOperators

noncomputable section

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- Denominator-cleared four-variable first-contact singularity.

If the potential has no monomial above the scaled contact level, the four
variable weights sum to `4*scale + bump`, and the contact lies at least three
base degrees above zero (`bump + 3*scale ≤ level`), then a Hessian-one
potential has singular Hessian on its maximal contact initial form.
-/
theorem first_contact_scaled_hessianDeterminant_eq_zero_of_isWeightLE
    {w : Fin 4 → ℤ} {level scale bump : ℕ} {ψ : MvPolynomial (Fin 4) K}
    (hscale : 0 < scale)
    (hcontact : bump + 3 * scale ≤ level)
    (hbound : HC4.Polynomial.IsWeightLE w (level : ℤ) ψ)
    (hsum : ∑ i : Fin 4, w i = ((4 * scale + bump : ℕ) : ℤ))
    (hMA : IsPolynomialMongeAmpere ψ) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm w (level : ℤ) ψ) = 0 := by
  apply maximal_initial_hessianDeterminant_eq_zero w (level : ℤ) ψ hbound hMA
  rw [hsum]
  norm_num
  have hcontactZ :
      ((bump + 3 * scale : ℕ) : ℤ) ≤ (level : ℤ) := by
    exact_mod_cast hcontact
  have hscaleZ : (0 : ℤ) < (scale : ℤ) := by
    exact_mod_cast hscale
  push_cast at hcontactZ
  push_cast
  omega

/-- Unit-scale form used when the contact slope is already integral. -/
theorem first_contact_hessianDeterminant_eq_zero_of_isWeightLE
    {w : Fin 4 → ℤ} {m lam : ℕ} {ψ : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m) (hlam : lam ≤ m - 3)
    (hbound : HC4.Polynomial.IsWeightLE w (m : ℤ) ψ)
    (hsum : ∑ i : Fin 4, w i = ((4 + lam : ℕ) : ℤ))
    (hMA : IsPolynomialMongeAmpere ψ) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm w (m : ℤ) ψ) = 0 := by
  apply first_contact_scaled_hessianDeterminant_eq_zero_of_isWeightLE
      (w := w) (level := m) (scale := 1) (bump := lam) (ψ := ψ)
  · omega
  · omega
  · exact hbound
  · simpa [Nat.mul_one, Nat.one_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  · exact hMA

end

end HC4.MongeAmpere
