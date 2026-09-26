import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseDualExtrema
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberImpossible
import Mathlib.Tactic

/-!
# A19 genuine multi-fibre extremal separation

The two honest Rees families select the lowest and highest surviving strict
interior pair degrees.  The completed one-fibre theorem rules out equality.
Therefore every surviving strict-interior staircase has a genuinely separated
pair of extremal fibres.

This file packages that fact, together with the corresponding strict
separation of the pair-Rees and reflected pair-Rees parameter orders.  It is
the canonical entry point for the remaining finite-staircase coupling.
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

/-- The selected contact-side pair degree is always at most the selected
highest-side pair degree. -/
theorem extremalPair_le
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Alo.k ≤ Ahi.k := by
  have hLne :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨e, he⟩
  have heInterior := D.firstPositiveLayer_pair_strictInterior_left
    F hthree houtThree hnot e he
  have hs := D.parameterLayer_support
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
  have heP : e ∈ P.carrier.support := by
    rw [hs] at he
    exact (Finset.mem_filter.mp he).1
  have hpair :
      (rankThreeQuotientCoordinate 1 F.V e).pair = Ahi.k := by
    have hcoords := (Ahi.coordinates e he).1
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hcoords
  have hlo := Alo.pair_le_of_strictInterior
    hthree houtThree hnot heP
    (by simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using heInterior.1)
    (by simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using heInterior.2)
  simpa [hpair] using hlo

/-- **Genuine multi-fibre separation.**  Once strict-interior support survives,
the selected extremal pair degrees are strictly ordered. -/
theorem extremalPair_lt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Alo.k < Ahi.k := by
  have hle := D.extremalPair_le F Alo Ahi hthree houtThree hnot
  exact lt_of_le_of_ne hle fun heq =>
    D.oneFiber_impossible F Alo Ahi hthree houtThree hnot heq

/-- Pair-Rees orders from the highest endpoint are strictly reversed. -/
theorem extremal_pairReesOrder_lt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    F.highest.n - Ahi.k < F.highest.n - Alo.k := by
  have hlt := D.extremalPair_lt F Alo Ahi hthree houtThree hnot
  omega

/-- Reflected pair-Rees orders from the locked endpoint are strictly ordered
in the same direction as pair degree. -/
theorem extremal_reflectedOrder_lt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Alo.k - 1 < Ahi.k - 1 := by
  have hlt := D.extremalPair_lt F Alo Ahi hthree houtThree hnot
  omega

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
