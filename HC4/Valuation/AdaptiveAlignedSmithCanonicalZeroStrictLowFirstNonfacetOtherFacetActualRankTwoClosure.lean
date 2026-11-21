import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetActualRankTwo
import Mathlib.Tactic

/-!
# A19 lower-boundary other-facet outcome gives actual rank-two geometry

A19.92 already compresses a lower boundary outcome, once its starting endpoint
is rank three on `.qs`, to an actual outside endpoint on one of the other three
facets.  The cyclic source-pivot adapter now packages every such endpoint as an
actual rank-two Hessian chart on the represented state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- A retained lower-boundary outcome with rank-three `.qs` start already
carries an actual rank-two Hessian chart on the represented state. -/
theorem qs_ray_boundaryOutcome_actualRankTwoHessianChart
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtcome :
      AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.QsLowerBoundaryOutcome C) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases C.qs_ray_boundaryOutcome_otherFacet hthree houtcome with
    ⟨next, hne, houtThree⟩
  exact C.qs_ray_otherFacet_actualRankTwoHessianChart
    hthree hne houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
