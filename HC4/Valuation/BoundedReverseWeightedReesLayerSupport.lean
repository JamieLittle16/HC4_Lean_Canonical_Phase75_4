import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# Exact layer support of bounded reverse weighted Rees families

The explicit reverse-Rees coefficient formula makes its parameter support
completely transparent.  Every source coefficient is a single monomial
`X^(D-weight d)`, hence every occurring parameter order is at most `D`, and a
layer above `D` is identically zero.

These elementary facts are kept separate from the Hessian covariance theorem:
they are the finite-support input used by the all-depth staircase argument.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Every supported exponent in an exact reverse-Rees layer has exactly the
corresponding weight drop. -/
theorem reverseWeightedReesFamily_parameterLayer_mem_iff
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F)
    (d : Fin 4 →₀ ℕ) :
    d ∈ (familyParameterLayer (reverseWeightedReesFamily w D F h) n).support ↔
      d ∈ F.support ∧ D - Finsupp.weight w d = n := by
  rw [MvPolynomial.mem_support_iff]
  rw [reverseWeightedReesFamily_parameterLayer_coeff]
  by_cases hcond : d ∈ F.support ∧ D - Finsupp.weight w d = n
  · rw [if_pos hcond]
    have hcoeff : MvPolynomial.coeff d F ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hcond.1
    exact ⟨fun _ => hcond, fun _ => hcoeff⟩
  · rw [if_neg hcond]
    exact ⟨fun hzero => (hzero rfl).elim, fun hpair => (hcond hpair).elim⟩

/-- No reverse-Rees source layer can occur above the chosen level. -/
theorem reverseWeightedReesFamily_parameterLayer_eq_zero_of_level_lt
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F)
    (hDn : D < n) :
    familyParameterLayer (reverseWeightedReesFamily w D F h) n = 0 := by
  ext d
  rw [reverseWeightedReesFamily_parameterLayer_coeff]
  have hne : D - Finsupp.weight w d ≠ n := by
    have hdrop : D - Finsupp.weight w d ≤ D := Nat.sub_le D _
    omega
  simp [hne]

/-- Every actual parameter exponent of a bounded reverse-Rees family is at
most its source level. -/
theorem reverseWeightedReesFamily_actualLayerOrder_le_level
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F)
    {n : ℕ}
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily w D F h)) :
    n ≤ D := by
  rcases (mem_familyParameterLayerOrders_iff
      (reverseWeightedReesFamily w D F h) n).1 hn with
    ⟨d, _hdQ, hcoeff⟩
  rw [reverseWeightedReesFamily_coeff] at hcoeff
  by_cases hdF : d ∈ F.support
  · rw [if_pos hdF] at hcoeff
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow] at hcoeff
    by_cases heq : D - Finsupp.weight w d = n
    · have hdrop : D - Finsupp.weight w d ≤ D := Nat.sub_le D _
      omega
    · simp [Ne.symm heq] at hcoeff
  · rw [if_neg hdF] at hcoeff
    exact (hcoeff rfl).elim

end

end HC4.Valuation