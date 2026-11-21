import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointSourceExposure
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# Honest reverse Rees of the lower-ray facet endpoint

Convert the positive integer endpoint exposure to natural reverse-Rees data.
The resulting family has the endpoint monomial as its literal special fibre
and carries the positive determinant clock obtained from source refinement.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsRayFacetEndpointSourceExposure

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Natural version of the positive source weight. -/
def natWeight (E : QsRayFacetEndpointSourceExposure C) (i : Fin 4) : ℕ :=
  (E.weight i).toNat

/-- Natural version of the positive source level. -/
def natLevel (E : QsRayFacetEndpointSourceExposure C) : ℕ :=
  E.level.toNat

@[simp] theorem natWeight_cast
    (E : QsRayFacetEndpointSourceExposure C) (i : Fin 4) :
    (E.natWeight i : ℤ) = E.weight i := by
  unfold natWeight
  exact Int.toNat_of_nonneg (le_of_lt (E.weight_pos i))

@[simp] theorem natLevel_cast
    (E : QsRayFacetEndpointSourceExposure C) :
    (E.natLevel : ℤ) = E.level := by
  unfold natLevel
  exact Int.toNat_of_nonneg (le_of_lt E.level_pos)

/-- Casted natural monomial weights recover the exact integer exposure. -/
theorem finsupp_weight_natWeight_cast
    (E : QsRayFacetEndpointSourceExposure C)
    (d : Fin 4 →₀ ℕ) :
    (Finsupp.weight E.natWeight d : ℤ) = Finsupp.weight E.weight d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  push_cast
  apply Finsupp.sum_congr
  intro i hi
  simpa using congrArg (fun z : ℤ => d i • z) (E.natWeight_cast i)

/-- Natural reverse-Rees support bound. -/
theorem hasReverseWeightBound
    (E : QsRayFacetEndpointSourceExposure C) :
    HasReverseWeightBound E.natWeight E.natLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro d hd
  have hz := E.source_bound hd
  have hzCast :
      (Finsupp.weight E.natWeight d : ℤ) ≤ (E.natLevel : ℤ) := by
    rw [E.finsupp_weight_natWeight_cast d, E.natLevel_cast]
    exact hz
  exact_mod_cast hzCast

/-- Positive integer Hessian clock gives the natural covariance inequality. -/
theorem hessianClock_nonneg
    (E : QsRayFacetEndpointSourceExposure C) :
    2 * ∑ i : Fin 4, E.natWeight i ≤ 4 * E.natLevel := by
  have hsum :
      (∑ i : Fin 4, (E.natWeight i : ℤ)) =
        ∑ i : Fin 4, E.weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact E.natWeight_cast i
  have hltZ :
      ((2 * ∑ i : Fin 4, E.natWeight i : ℕ) : ℤ) <
        ((4 * E.natLevel : ℕ) : ℤ) := by
    push_cast
    rw [hsum, E.natLevel_cast]
    linarith [E.hessianClock_pos]
  have hlt :
      2 * (∑ i : Fin 4, E.natWeight i : ℕ) < 4 * E.natLevel := by
    exact_mod_cast hltZ
  exact Nat.le_of_lt hlt

/-- Honest bounded reverse-Rees family of the represented determinant-one
source. -/
noncomputable def reverseReesFamily
    (E : QsRayFacetEndpointSourceExposure C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily E.natWeight E.natLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    E.hasReverseWeightBound

/-- Its special fibre is exactly the stored endpoint monomial. -/
theorem reverseReesFamily_specialFiber
    (E : QsRayFacetEndpointSourceExposure C) :
    polynomialFamilySpecialFiber E.reverseReesFamily =
      MvPolynomial.monomial C.ray.facetExponent
        (MvPolynomial.coeff C.ray.facetExponent
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) := by
  unfold reverseReesFamily
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  have hweight : (fun i : Fin 4 => (E.natWeight i : ℤ)) = E.weight := by
    funext i
    exact E.natWeight_cast i
  rw [hweight, E.natLevel_cast]
  exact E.initialForm_eq

/-- Exact determinant clock of the honest endpoint Rees family. -/
theorem reverseReesFamily_hasHessianDefect
    (E : QsRayFacetEndpointSourceExposure C) :
    HasPolynomialFamilyHessianDefect (K := K) E.reverseReesFamily
      (4 * E.natLevel - 2 * ∑ i : Fin 4, E.natWeight i) := by
  unfold reverseReesFamily
  apply reverseWeightedReesFamily_hasHessianDefect
      E.natWeight E.natLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      E.hasReverseWeightBound
  · exact
      T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
        T.presented_zero
  · exact E.hessianClock_nonneg

/-- The determinant clock is genuinely positive. -/
theorem reverseReesFamily_defect_pos
    (E : QsRayFacetEndpointSourceExposure C) :
    0 < 4 * E.natLevel - 2 * ∑ i : Fin 4, E.natWeight i := by
  have hsum :
      (∑ i : Fin 4, (E.natWeight i : ℤ)) =
        ∑ i : Fin 4, E.weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact E.natWeight_cast i
  have hltZ :
      ((2 * ∑ i : Fin 4, E.natWeight i : ℕ) : ℤ) <
        ((4 * E.natLevel : ℕ) : ℤ) := by
    push_cast
    rw [hsum, E.natLevel_cast]
    linarith [E.hessianClock_pos]
  have hlt :
      2 * (∑ i : Fin 4, E.natWeight i : ℕ) < 4 * E.natLevel := by
    exact_mod_cast hltZ
  exact Nat.sub_pos_iff_lt.mpr hlt

end QsRayFacetEndpointSourceExposure
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
