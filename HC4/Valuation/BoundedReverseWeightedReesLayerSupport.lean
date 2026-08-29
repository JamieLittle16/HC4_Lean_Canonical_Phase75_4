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
    exact ⟨fun hcoeff => hcond,
      fun _ => MvPolynomial.mem_support_iff.mp hcond.1⟩
  · rw [if_neg hcond]
    simp [hcond]

/-- No reverse-Rees source layer can occur above the chosen level. -/
theorem reverseWeightedReesFamily_parameterLayer_eq_zero_of_level_lt
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F)
    (hDn : D < n) :
    familyParameterLayer (reverseWeightedReesFamily w D F h) n = 0 := by
  ext d
  rw [reverseWeightedReesFamily_parameterLayer_coeff]
  have hdrop : D - Finsupp.weight w d ≤ D := Nat.sub_le D _
  have hne : D - Finsupp.weight w d ≠ n := by omega
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
    have hnmem : n ∈
        (Polynomial.X ^ (D - Finsupp.weight w d) *
          Polynomial.C (MvPolynomial.coeff d F)).support := by
      exact Polynomial.mem_support_iff.mpr hcoeff
    have hdegree : n ≤ D - Finsupp.weight w d := by
      have hdeg := Polynomial.le_natDegree_of_mem_supp _ hnmem
      have hcoeffF : MvPolynomial.coeff d F ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hdF
      have hnat :
          (Polynomial.X ^ (D - Finsupp.weight w d) *
            Polynomial.C (MvPolynomial.coeff d F)).natDegree =
              D - Finsupp.weight w d := by
        rw [Polynomial.natDegree_mul]
        · simp
        · exact pow_ne_zero _ Polynomial.X_ne_zero
        · simp [hcoeffF]
      rw [hnat] at hdeg
      exact hdeg
    exact hdegree.trans (Nat.sub_le D _)
  · rw [if_neg hdF] at hcoeff
    exact (hcoeff rfl).elim

end

end HC4.Valuation
