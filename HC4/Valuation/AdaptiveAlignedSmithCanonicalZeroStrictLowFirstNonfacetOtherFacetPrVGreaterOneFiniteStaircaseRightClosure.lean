import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofAffineTerminalRealisation
import Mathlib.Tactic

/-!
# Complete the mirrored `(V,1)`, `V > 1` finite-staircase branch

The whole source-honest carrier has exactly the two alternatives already
constructed by the right lower-hull/cross-roof analysis.  A central source
monomial gives an actual rank-two Hessian chart on the represented presented
state.  The exposed cross-roof alternative is impossible by the mirrored
affine terminal theorem.

No repair-only progress and no auxiliary-clock identification is used here.
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

/-- The complete right `(V,1)`, `V > 1` branch yields actual rank-two Hessian
geometry on the represented state. -/
theorem QsOtherFacetPrRightVContactFrontierData.actualRankTwoHessianChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases F.central_or_exposedCrossRoof hthree houtThree with
    hcentral | hexposed
  · rcases hcentral with ⟨c, hc, hc1, hc3⟩
    rcases F.centralRankTwoGeometry_of_point
        hthree houtThree hc hc1 hc3 with ⟨G⟩
    exact ⟨G.actualRankTwoHessianChart⟩
  · rcases hexposed with ⟨E⟩
    exact (E.impossible hthree houtThree).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation