import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfile
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesHighestFirstVariation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseLowerHullExposure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofTerminalClosure
import Mathlib.Tactic

/-!
# Exact stationary convolution orders

Nonzero coefficients of the actual stationary carrier profile provide the
bounds needed to add naturally truncated reverse orders. No determinant
vanishing assumption is used.

The pair-Rees highest-end first-variation module, the current finite-staircase
lower-hull exposure, and the cross-roof terminal composition are also imported
here as rooted CI anchors while the final V>1 closure is assembled.  This
ensures the source-honest endpoint and multi-fibre chains are elaborated by
`lake build HC4` rather than merely existing as unimported source.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton HC4.Polynomial HC4.Toric
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
namespace QsOtherFacetPrLeftVContactFrontierData
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
variable {P : QsOtherFacetPlanarCarrierPackage C .pr}
variable {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
variable {R : QsOtherFacetContactQuadraticReesPackage C}

/-- Supported stationary indices never exceed the total reverse weight. -/
theorem stationary_profileIndex_weight_le
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {i : ℕ} (hi : F.stationaryCarrierProfile.coeff i ≠ 0) :
    F.stationaryWeight * i ≤ F.stationaryTotalDegree := by
  have hiDegree : i ≤ F.stationaryCarrierProfile.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hi
  have hiBound := hiDegree.trans
    (F.natDegree_stationaryCarrierProfile_le hthree houtThree)
  exact Nat.mul_le_mul_left F.stationaryWeight hiBound

/-- Exact addition of two supported stationary reverse orders. -/
theorem stationary_profileOrder_add
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {i j : ℕ}
    (hi : F.stationaryCarrierProfile.coeff i ≠ 0)
    (hj : F.stationaryCarrierProfile.coeff j ≠ 0) :
    (F.stationaryTotalDegree - F.stationaryWeight * i) +
        (F.stationaryTotalDegree - F.stationaryWeight * j) =
      2 * F.stationaryTotalDegree - F.stationaryWeight * (i + j) := by
  have hiBound := F.stationary_profileIndex_weight_le hthree houtThree hi
  have hjBound := F.stationary_profileIndex_weight_le hthree houtThree hj
  rw [Nat.mul_add]
  omega

end QsOtherFacetPrLeftVContactFrontierData
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
