import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCrossRoofAffineTerminalRealisation
import Mathlib.Tactic

/-!
# Complete left unit finite-staircase closure

The whole source-honest unit carrier has only two outcomes under the positive
lower-hull split.  A central `(e₁,e₂)=(0,0)` source monomial gives an actual
rank-two Hessian chart on the represented state.  Otherwise the exact exposed
cross-roof face is impossible by the two oriented affine-line terminals.

Thus the complete left unit branch produces retained actual rank-two geometry;
no repair-only progress and no auxiliary-clock identification is used.
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

/-- The complete left unit branch yields an actual rank-two Hessian chart on
the represented presented state. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.actualRankTwoHessianChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases F.central_or_exposedCrossRoof hthree houtThree with
    hcentral | hexposed
  · rcases hcentral with ⟨c, hc, hc1, hc2⟩
    exact ⟨F.central_actualRankTwoHessianChart
      hthree houtThree hc hc1 hc2⟩
  · rcases hexposed with ⟨E⟩
    exact (E.impossible hthree houtThree).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
