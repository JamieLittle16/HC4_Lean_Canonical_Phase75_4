import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOrder
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberImpossible
import Mathlib.Tactic

/-!
# A19 genuine unit multi-fibre extremal separation

The unit contact and pair-Rees selectors choose the least and greatest
surviving strict-interior pair fibres.  The completed unit one-fibre theorem
rules out equality, so any surviving unit staircase has strictly separated
extrema.
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

namespace QsOtherFacetPrPairReesData

/-- Genuine unit multi-fibre separation. -/
theorem extremalPair_lt_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Alo.k < Ahi.k := by
  have hle := D.extremalPair_le_unitLeft F Alo Ahi hthree houtThree hnot
  exact lt_of_le_of_ne hle fun heq =>
    D.unitLeft_oneFiber_impossible F Alo Ahi hthree houtThree hnot heq

/-- Pair-Rees orders from the highest endpoint are strictly reversed. -/
theorem extremal_pairReesOrder_lt_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    F.highest.n - Ahi.k < F.highest.n - Alo.k := by
  have hlt := D.extremalPair_lt_unitLeft F Alo Ahi hthree houtThree hnot
  omega

/-- Reflected pair-Rees orders from the locked endpoint are strictly ordered
in the same direction as pair degree. -/
theorem extremal_reflectedOrder_lt_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Alo.k - 1 < Ahi.k - 1 := by
  have hlt := D.extremalPair_lt_unitLeft F Alo Ahi hthree houtThree hnot
  omega

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
