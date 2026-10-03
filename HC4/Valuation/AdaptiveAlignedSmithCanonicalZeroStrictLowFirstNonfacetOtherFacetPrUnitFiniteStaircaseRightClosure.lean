import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseRightCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseRightCrossRoofAffineTerminalRealisation
import Mathlib.Tactic

/-!
# Complete right unit finite-staircase closure

A central `(e₁,e₃)=(0,0)` source monomial gives retained actual rank-two
geometry.  Otherwise the exact mirrored cross-roof face is impossible.
Thus the complete right unit branch also yields an actual rank-two Hessian
chart on the represented state.
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

/-- The complete right unit branch yields an actual rank-two Hessian chart on
the represented presented state. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.actualRankTwoHessianChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases F.central_or_exposedCrossRoof hthree houtThree with hcentral | hexposed
  · rcases hcentral with ⟨c, hc, hc1, hc3⟩
    exact ⟨F.central_actualRankTwoHessianChart hthree houtThree hc hc1 hc3⟩
  · rcases hexposed with ⟨E⟩
    exact (E.impossible hthree houtThree).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end
end HC4.Valuation
