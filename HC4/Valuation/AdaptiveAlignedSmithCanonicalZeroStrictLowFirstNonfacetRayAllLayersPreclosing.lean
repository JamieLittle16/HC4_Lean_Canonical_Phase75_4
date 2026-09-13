import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Tactic

/-!
# A19.107: every source layer of the ray-leading reverse Rees is preclosing

A19.104b deliberately chooses the direct ray exposure so that its pure Hessian
closing order is strictly larger than the reverse-Rees source level.  A19.R6
shows every source parameter order of a bounded reverse Rees is at most that
level.  Hence every actual source deformation occurs strictly before Hessian
closure, not merely the first one.

This is the all-depth triangularity needed by the remaining staircase
extraction: every determinant coefficient indexed by an actual source layer is
zero by the already-green pure-clock coefficient theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Any actual parameter order of the ray-leading reverse-Rees source lies
strictly before its determinant-closing order. -/
theorem QsOtherFacetRayReverseReesPackage.actualLayerOrder_lt_defect
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    {n : ℕ}
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)) :
    n < 4 * R.level - 2 * ∑ i : Fin 4, R.weight i := by
  have hnlevel := reverseWeightedReesFamily_actualLayerOrder_le_level
    R.weight R.level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    R.bound hn
  exact lt_of_le_of_lt hnlevel R.level_lt_defect

/-- Consequently the full Hessian determinant coefficient vanishes at every
actual source-layer order. -/
theorem QsOtherFacetRayReverseReesPackage.determinantLayer_zero_of_actualLayerOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    {n : ℕ}
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound)) n = 0 := by
  exact hessianDefect_parameterLayer_eq_zero_of_lt
    (reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound)
    R.hessianDefect (R.actualLayerOrder_lt_defect hn)

/-- Orders above the source level carry no source potential at all. -/
theorem QsOtherFacetRayReverseReesPackage.sourceLayer_eq_zero_of_level_lt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    {n : ℕ}
    (hn : R.level < n) :
    familyParameterLayer
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound) n = 0 := by
  exact reverseWeightedReesFamily_parameterLayer_eq_zero_of_level_lt
    R.weight R.level n
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    R.bound hn

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
