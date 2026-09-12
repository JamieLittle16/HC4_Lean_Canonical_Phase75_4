import HC4.Newton.FiniteSupportSingularBoundaryKernelOpening
import HC4.Polynomial.NonlinearSupportHessianRowBreak
import HC4.Valuation.SingularBoundedReverseWeightedRees
import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# Honest reverse-Rees family for a canonical coordinate-max kernel opening

A `CanonicalCoordinateMaxKernelOpeningData` records one exact coordinate-max
initial-form step at which a literal coordinate kernel first appears.  This
file realises that step as the existing bounded reverse weighted Rees family.

The resulting family has all of the source-honest properties needed by the
A19.55 first-break calculation:

* its special fibre is exactly the stored child;
* evaluation of the parameter at `1` recovers the stored parent;
* because the parent is Hessian-singular, the complete Rees family is
  Hessian-singular identically in the parameter;
* if the source support has ordinary degree at least three, the parent kernel
  break produces a genuinely nonzero parameter-first Hessian-row series.

No Smith/blocker clock or repair transition is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Natural coordinate weight corresponding to `coordinateMaxWeight`. -/
def coordinateMaxNatWeight (i : Fin 4) : Fin 4 → ℕ :=
  fun j => if j = i then 1 else 0

/-- Its weight on an exponent is exactly that coordinate. -/
theorem weight_coordinateMaxNatWeight
    (i : Fin 4) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (coordinateMaxNatWeight i) d = d i := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · fin_cases i <;>
      simp [coordinateMaxNatWeight, Fin.sum_univ_four]
  · intro j
    simp

end
end HC4.Valuation

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

/-- The integer coordinate-max support bound is exactly the natural reverse
Rees weight bound required by `reverseWeightedReesFamily`. -/
theorem hasReverseWeightBound :
    HasReverseWeightBound
      (coordinateMaxNatWeight D.extractionCoordinate)
      D.extractionLevel D.parent := by
  intro d hd
  have hle := D.weight_bound hd
  rw [weight_coordinateMaxWeight] at hle
  rw [weight_coordinateMaxNatWeight]
  exact_mod_cast hle

/-- Honest bounded reverse-Rees family attached to this opening. -/
noncomputable def reverseReesFamily :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    (coordinateMaxNatWeight D.extractionCoordinate)
    D.extractionLevel D.parent D.hasReverseWeightBound

/-- Its special fibre is exactly the child initial form retained by the
coordinate-max opening data. -/
theorem specialFiber_reverseReesFamily_eq_child :
    polynomialFamilySpecialFiber D.reverseReesFamily = D.child := by
  rw [reverseReesFamily]
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  rw [D.child_eq_initialForm]
  congr 2
  funext j
  simp [coordinateMaxNatWeight, coordinateMaxWeight]

/-- Evaluating the auxiliary Rees parameter at `1` recovers the parent source
polynomial exactly. -/
theorem map_evalOne_reverseReesFamily :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K)) D.reverseReesFamily =
      D.parent := by
  ext d
  rw [MvPolynomial.coeff_map]
  rw [reverseReesFamily, reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ D.parent.support
  · simp [hd]
  · have hc : MvPolynomial.coeff d D.parent = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hc]

/-- The complete coordinate-max Rees family is Hessian-singular identically. -/
theorem reverseReesFamily_hessianDeterminant_eq_zero :
    HC4.Polynomial.hessianDeterminant D.reverseReesFamily = 0 := by
  rw [reverseReesFamily]
  exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
    (coordinateMaxNatWeight D.extractionCoordinate)
    D.extractionLevel D.parent D.hasReverseWeightBound D.parent_hessian_zero

/-- Every monomial of the opening parent remains nonlinear whenever every
monomial of the original source is nonlinear. -/
theorem parent_support_degree_ge_three
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    ∀ d ∈ D.parent.support, 3 ≤ ordinaryDegree4 d := by
  intro d hd
  exact hnonlinear d (D.parent_support_subset_source hd)

/-- The first-derivative break stored by the opening data is a genuine Hessian
row break on the parent. -/
theorem exists_parent_hessianRow_entry_ne_zero
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    ∃ i : Fin 4,
      HC4.Polynomial.hessian D.parent D.kernelCoordinate i ≠ 0 := by
  rcases
      exists_hessian_entry_ne_zero_of_pderiv_ne_zero_of_support_degree_ge_three
        D.kernelCoordinate D.parent
        (D.parent_support_degree_ge_three hnonlinear)
        D.parent_kernel_ne with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [HC4.Polynomial.hessian_apply] using hi

/-- Hence at least one parameter-first Hessian entry in the kernel row of the
honest Rees family is a nonzero polynomial series. -/
theorem exists_parameterFirstHessian_kernelRow_ne_zero
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    ∃ i : Fin 4,
      parameterFirstHessian D.reverseReesFamily D.kernelCoordinate i ≠ 0 := by
  rcases D.exists_parent_hessianRow_entry_ne_zero hnonlinear with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  intro hzero

  have hfamilyEntry :
      HC4.Polynomial.hessian D.reverseReesFamily D.kernelCoordinate i = 0 := by
    apply (parameterFirstEquiv K).injective
    change
      parameterFirstHessian D.reverseReesFamily D.kernelCoordinate i =
        parameterFirstEquiv K 0
    simpa using hzero

  have hrecovered := congrArg
    (fun P : MvPolynomial (Fin 4) K =>
      HC4.Polynomial.hessian P D.kernelCoordinate i)
    D.map_evalOne_reverseReesFamily

  have hleft :
      HC4.Polynomial.hessian
          (MvPolynomial.map (Polynomial.evalRingHom (1 : K))
            D.reverseReesFamily)
          D.kernelCoordinate i = 0 := by
    rw [HC4.Polynomial.hessian_apply]
    simp [MvPolynomial.pderiv_map, hfamilyEntry,
      HC4.Polynomial.hessian_apply]

  rw [hleft] at hrecovered
  exact hi hrecovered.symm

end CanonicalCoordinateMaxKernelOpeningData

end
end HC4.Newton
