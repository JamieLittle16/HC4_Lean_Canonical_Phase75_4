import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Polynomial.DerivativeWeight
import Mathlib.Tactic

/-!
# Associated graded layers of the bounded reverse Rees family

The bounded reverse-Rees construction is already coefficientwise exact.  This
file records the corresponding state-free associated-graded identities: its
parameter layer of order `n` is literally the weighted initial form of the
original source at weight `D - n`, and its Hessian coefficient is the
corresponding shifted initial form of the actual source Hessian.

This is the provenance bridge needed by the final zero-defect ray argument.
It introduces no terminal state, clock comparison, or repair step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Every in-range parameter layer of a bounded reverse Rees family is exactly
an initial form of the original source. -/
theorem reverseWeightedReesFamily_parameterLayer_eq_initialForm
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (hn : n ≤ D) :
    familyParameterLayer (reverseWeightedReesFamily w D F h) n =
      initialForm (fun i => (w i : ℤ)) ((D - n : ℕ) : ℤ) F := by
  ext d
  rw [reverseWeightedReesFamily_parameterLayer_coeff,
    HC4.Polynomial.coeff_initialForm]
  by_cases hd : d ∈ F.support
  · have hle : Finsupp.weight w d ≤ D := h d hd
    have hcast :
        Finsupp.weight (fun i => (w i : ℤ)) d =
          (Finsupp.weight w d : ℤ) := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply]
      push_cast
      rfl
    rw [hcast]
    simp only [hd, true_and]
    have heq :
        D - Finsupp.weight w d = n ↔
          Finsupp.weight w d = D - n := by
      omega
    rw [heq]
    norm_cast
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hcoeff]

/-- Coefficientwise Hessian provenance for the reverse Rees family.  At
parameter order `n`, differentiation merely shifts the associated weight by
the two differentiated coordinate weights. -/
theorem reverseWeightedRees_parameterFirstHessian_coeff_eq_initialForm
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (hn : n ≤ D)
    (i j : Fin 4) :
    (parameterFirstHessian (reverseWeightedReesFamily w D F h) i j).coeff n =
      initialForm (fun k => (w k : ℤ))
        (((D - n : ℕ) : ℤ) - (w i : ℤ) - (w j : ℤ))
        (HC4.Polynomial.hessian F i j) := by
  rw [parameterFirstHessian_coeff]
  rw [reverseWeightedReesFamily_parameterLayer_eq_initialForm w D n F h hn]
  exact HC4.Polynomial.hessian_initialForm_entry
    (fun k => (w k : ℤ)) ((D - n : ℕ) : ℤ) F i j

end

end HC4.Valuation
