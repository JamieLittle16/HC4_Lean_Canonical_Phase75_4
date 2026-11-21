import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrHighestSliceSourceExposure
import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetSource
import Mathlib.Tactic

/-!
# Honest reverse Rees of the `.pr` highest pair slice

A positive integer source exposure can be converted canonically to natural
weights by `Int.toNat`.  Because every coordinate and the level are strictly
positive, this conversion loses no information.  The bounded reverse weighted
Rees family therefore has the stored highest pair slice as its literal special
fibre.

The represented source has Hessian determinant one, and the combined source
exposure has positive Hessian clock.  Hence the reverse-Rees family carries the
exact positive pure determinant clock supplied by the generic covariance
lemma.  This family is the source-honest input for the pure-axis first-kernel-
row break closure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrHighestSliceSourceExposure

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}

/-- Natural coordinate weight corresponding exactly to the positive combined
integer exposure. -/
def natWeight
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) (i : Fin 4) : ℕ :=
  (prHighestSliceCombinedWeight P E.scale i).toNat

/-- Natural level corresponding exactly to the positive combined level. -/
def natLevel
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) : ℕ :=
  (prHighestSliceCombinedLevel S E.scale).toNat

@[simp]
theorem natWeight_cast
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) (i : Fin 4) :
    (E.natWeight i : ℤ) = prHighestSliceCombinedWeight P E.scale i := by
  unfold natWeight
  exact Int.toNat_of_nonneg (le_of_lt (E.weight_pos i))

@[simp]
theorem natLevel_cast
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    (E.natLevel : ℤ) = prHighestSliceCombinedLevel S E.scale := by
  unfold natLevel
  exact Int.toNat_of_nonneg (le_of_lt E.level_pos)

/-- Natural Finsupp weights cast back to the exact combined integer weight. -/
theorem finsupp_weight_natWeight_cast
    (E : QsOtherFacetPrHighestSliceSourceExposure P S)
    (d : Fin 4 →₀ ℕ) :
    (Finsupp.weight E.natWeight d : ℤ) =
      Finsupp.weight (prHighestSliceCombinedWeight P E.scale) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  push_cast
  apply Finsupp.sum_congr
  intro i hi
  rw [E.natWeight_cast]

/-- The represented source is bounded by the natural form of the combined
highest-slice exposure. -/
theorem hasReverseWeightBound
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    HasReverseWeightBound E.natWeight E.natLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro d hd
  have hz := E.source_bound hd
  have hcast := E.finsupp_weight_natWeight_cast d
  have hlevel := E.natLevel_cast
  exact_mod_cast (show
    Finsupp.weight (prHighestSliceCombinedWeight P E.scale) d ≤
      prHighestSliceCombinedLevel S E.scale from hz)

/-- Positive integer Hessian clock implies the natural covariance inequality
required by `reverseWeightedReesFamily_hasHessianDefect`. -/
theorem hessianClock_nonneg
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    2 * ∑ i : Fin 4, E.natWeight i ≤ 4 * E.natLevel := by
  have hsum :
      ((∑ i : Fin 4, E.natWeight i : ℕ) : ℤ) =
        ∑ i : Fin 4, prHighestSliceCombinedWeight P E.scale i := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [E.natWeight_cast]
  have hlt :
      2 * (∑ i : Fin 4, E.natWeight i : ℕ) < 4 * E.natLevel := by
    exact_mod_cast (show
      2 * ∑ i : Fin 4, prHighestSliceCombinedWeight P E.scale i <
        4 * prHighestSliceCombinedLevel S E.scale by
          linarith [E.hessianClock_pos])
  omega

/-- Honest bounded reverse-Rees family whose special fibre is the stored
highest pair slice. -/
noncomputable def reverseReesFamily
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily E.natWeight E.natLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    E.hasReverseWeightBound

/-- The reverse-Rees special fibre is literally the stored highest pair slice. -/
theorem reverseReesFamily_specialFiber
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    polynomialFamilySpecialFiber E.reverseReesFamily = S.slice := by
  unfold reverseReesFamily
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  have hweight :
      (fun i : Fin 4 => (E.natWeight i : ℤ)) =
        prHighestSliceCombinedWeight P E.scale := by
    funext i
    exact E.natWeight_cast i
  rw [hweight, E.natLevel_cast]
  exact E.initialForm_eq

/-- Exact positive determinant clock of the honest source reverse Rees. -/
theorem reverseReesFamily_hasHessianDefect
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
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

/-- The reverse-Rees determinant clock is genuinely positive. -/
theorem reverseReesFamily_defect_pos
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    0 < 4 * E.natLevel - 2 * ∑ i : Fin 4, E.natWeight i := by
  have hsum :
      ((∑ i : Fin 4, E.natWeight i : ℕ) : ℤ) =
        ∑ i : Fin 4, prHighestSliceCombinedWeight P E.scale i := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [E.natWeight_cast]
  have hposZ :
      (0 : ℤ) <
        4 * (E.natLevel : ℤ) -
          2 * (∑ i : Fin 4, E.natWeight i : ℕ) := by
    rw [E.natLevel_cast, hsum]
    exact E.hessianClock_pos
  exact_mod_cast hposZ

end QsOtherFacetPrHighestSliceSourceExposure
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
