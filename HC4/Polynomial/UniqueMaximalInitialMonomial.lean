import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# Unique maximal initial monomial

A small finite-support helper: if one support exponent is the unique point at
an exact maximal weight, the corresponding initial form is literally that
single monomial with its original coefficient.
-/

namespace HC4.Polynomial

noncomputable section

variable {σ K : Type*} [DecidableEq σ] [CommRing K]

/-- A unique support point on the maximal weight hyperplane gives a literal
monomial initial form. -/
theorem initialForm_eq_monomial_of_unique_max
    (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K)
    (d : σ →₀ ℕ)
    (hd : d ∈ p.support)
    (hdw : Finsupp.weight w d = m)
    (hbound : IsWeightLE w m p)
    (huniq : ∀ e ∈ p.support, Finsupp.weight w e = m → e = d) :
    initialForm w m p = MvPolynomial.monomial d (MvPolynomial.coeff d p) := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [coeff_initialForm]
  by_cases hed : e = d
  · subst e
    rw [hdw]
    simp
  · have hde : d ≠ e := Ne.symm hed
    have hnotTop : Finsupp.weight w e ≠ m ∨ e ∉ p.support := by
      by_contra h
      push_neg at h
      exact hed (huniq e h.2 h.1)
    rcases hnotTop with hweight | hsupp
    · simp [hweight, MvPolynomial.coeff_monomial, hde]
    · have hcoeff : MvPolynomial.coeff e p = 0 :=
        MvPolynomial.notMem_support_iff.mp hsupp
      simp [hcoeff, MvPolynomial.coeff_monomial, hde]

end

end HC4.Polynomial
