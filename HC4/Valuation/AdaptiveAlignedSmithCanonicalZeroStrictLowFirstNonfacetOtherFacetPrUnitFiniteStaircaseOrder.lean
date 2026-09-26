import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseExtremalFibers
import Mathlib.Tactic

/-!
# A19 unit finite-staircase extremal order

The locked/contact reverse Rees selects the least surviving strict-interior
pair fibre, while the pair-degree reverse Rees selects the greatest.  This
file packages the resulting comparison between the two source-honest unit
selectors.
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

/-- The selected locked/contact-side unit pair degree is at most the selected
highest-side unit pair degree. -/
theorem extremalPair_le_unitLeft
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
    Alo.k ≤ Ahi.k := by
  have hLloNe :
      familyParameterLayer Dlo.family
        (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero Dlo.family Dlo.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLloNe with ⟨a, ha⟩

  have hLhiNe :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLhiNe with ⟨e, he⟩

  have heInterior := D.firstPositiveLayer_pair_strictInterior_unitLeft
    F hthree houtThree hnot e he
  have hs := D.parameterLayer_support
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
  have heP : e ∈ P.carrier.support := by
    have he' := he
    rw [hs] at he'
    exact (Finset.mem_filter.mp he').1

  have hmin := Dlo.firstPositiveLayer_pair_minimal
    hthree houtThree hnot ha heP
    (by simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using heInterior.1)
    (by simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using heInterior.2)

  have hAlo :
      (rankThreeQuotientCoordinate 1 1 a).pair = Alo.k := by
    have hcoords := (Alo.coordinates a ha).1
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hcoords
  have hAhi :
      (rankThreeQuotientCoordinate 1 1 e).pair = Ahi.k := by
    have hcoords := (Ahi.coordinates e he).1
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hcoords

  simpa [hAlo, hAhi] using hmin

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
