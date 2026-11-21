import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayAllLayersPreclosing
import Mathlib.Tactic

/-!
# A19.111: the complete quadratic source range is preclosing

A19.110 strengthens the ray-leading reverse Rees so that twice its source
level lies strictly below the pure Hessian determinant clock.  Since no source
parameter layer can occur above that level, every quadratic convolution of two
source layers lies before determinant closure.

For the staircase argument the cleanest statement is slightly stronger: every
determinant coefficient through order `2 * level` vanishes, whether or not that
order itself is an actual source layer.  This is exactly the coefficient range
needed by quadratic profile residuals.
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

/-- Every coefficient of the full Hessian determinant through twice the source
level vanishes. -/
theorem QsOtherFacetRayReverseReesPackage.determinantLayer_zero_of_le_two_level
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    {n : ℕ}
    (hn : n ≤ 2 * R.level) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound)) n = 0 := by
  exact hessianDefect_parameterLayer_eq_zero_of_lt
    (reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound)
    R.hessianDefect (lt_of_le_of_lt hn R.two_level_lt_defect)

/-- The sum of any two actual source-layer orders is strictly preclosing. -/
theorem QsOtherFacetRayReverseReesPackage.actualLayerPairOrder_lt_defect
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    {m n : ℕ}
    (hm : m ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound))
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)) :
    m + n < 4 * R.level - 2 * ∑ i : Fin 4, R.weight i := by
  have hmlevel := reverseWeightedReesFamily_actualLayerOrder_le_level
    R.weight R.level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    R.bound hm
  have hnlevel := reverseWeightedReesFamily_actualLayerOrder_le_level
    R.weight R.level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    R.bound hn
  have hsum : m + n ≤ 2 * R.level := by omega
  exact lt_of_le_of_lt hsum R.two_level_lt_defect

/-- Therefore the full determinant coefficient at the sum of any two actual
source-layer orders is zero. -/
theorem QsOtherFacetRayReverseReesPackage.determinantLayer_zero_of_actualLayerPair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    {m n : ℕ}
    (hm : m ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound))
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound))
      (m + n) = 0 := by
  exact hessianDefect_parameterLayer_eq_zero_of_lt
    (reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound)
    R.hessianDefect (R.actualLayerPairOrder_lt_defect hm hn)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
