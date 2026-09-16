import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# Nonzero maximal weighted initials of singular-Hessian polynomials

For a nonzero finite polynomial and any integer weight, choose a support
monomial of maximal weight.  The corresponding exact initial form is nonzero
and gives a global `IsWeightLE` bound.  If the original Hessian determinant
vanishes, `MaximalHessianInitial` then shows that this maximal component is
Hessian singular as well.

This is the state-free algebraic form of the highest-slice argument used by
the final A19 rank-three branch.
-/

namespace HC4.Polynomial

noncomputable section

open MvPolynomial

variable {σ K : Type*}
variable [Fintype σ] [DecidableEq σ]
variable [CommRing K]

/-- Every nonzero finite polynomial has a nonzero maximal exact component for
an arbitrary integer weight. -/
theorem exists_nonzero_maximal_initial
    (w : σ → ℤ) (G : MvPolynomial σ K) (hG : G ≠ 0) :
    ∃ m : ℤ,
      initialForm w m G ≠ 0 ∧
      IsWeightLE w m G := by
  classical
  have hsupp : G.support.Nonempty := MvPolynomial.support_nonempty.mpr hG
  rcases Finset.exists_max_image G.support
      (fun e => Finsupp.weight w e) hsupp with
    ⟨d, hd, hmax⟩
  let m : ℤ := Finsupp.weight w d
  refine ⟨m, ?_, ?_⟩
  · have hdcoeff : MvPolynomial.coeff d G ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hdtop : d ∈ (initialForm w m G).support := by
      rw [MvPolynomial.mem_support_iff, coeff_initialForm]
      simp [m, hdcoeff]
    exact MvPolynomial.support_nonempty.mp ⟨d, hdtop⟩
  · intro e he
    exact hmax e he

/-- A maximal exact component of a nonzero singular-Hessian polynomial can be
chosen both nonzero and Hessian singular. -/
theorem exists_nonzero_maximal_singular_initial
    (w : σ → ℤ) (G : MvPolynomial σ K)
    (hG : G ≠ 0)
    (hzero : hessianDeterminant G = 0) :
    ∃ m : ℤ,
      initialForm w m G ≠ 0 ∧
      IsWeightLE w m G ∧
      hessianDeterminant (initialForm w m G) = 0 := by
  rcases exists_nonzero_maximal_initial w G hG with
    ⟨m, htop, hbound⟩
  exact ⟨m, htop, hbound,
    hessianDeterminant_initialForm_eq_zero_of_eq_zero
      w m G hbound hzero⟩

end

end HC4.Polynomial
