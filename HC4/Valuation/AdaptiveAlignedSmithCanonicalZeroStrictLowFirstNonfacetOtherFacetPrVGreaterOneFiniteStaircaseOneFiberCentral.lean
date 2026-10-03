import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberUpperImpossible
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberLowerImpossible
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberMiddleLowerImpossible
import Mathlib.Tactic

/-!
# A19 surviving one-fibre branch is central

All one-fibre diagonals except the middle top-degree mode have now been
eliminated.  This file packages the exact surviving interface:

* `j+1=k`;
* the honest common profile has natural degree `k`;
* an actual source-carrier monomial has exponent coordinates
  `(k,0,0,V*(k-1))`.

This is not yet a contradiction; it is the sharply reduced central singleton
frontier consumed by the final translated two-mode calculation.
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

/-- Coincident extremal fibres can only lie on the middle staircase diagonal. -/
theorem oneFiber_middle_diagonal
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
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k) :
    Alo.j + 1 = Alo.k := by
  rcases F.oneFiber_three_diagonals Alo Ahi hthree houtThree hext with
    hlo | hmid | hhi
  · exact False.elim <|
      D.oneFiber_lower_diagonal_impossible F Alo Ahi
        hthree houtThree hnot hext hlo
  · exact hmid
  · exact False.elim <|
      D.oneFiber_upper_diagonal_impossible F Alo Ahi
        hthree houtThree hnot hext hhi

/-- The surviving middle one-fibre profile necessarily has its upper ordinary
degree `k`. -/
theorem oneFiber_middle_profile_natDegree_eq_k
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
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k) :
    Alo.coefficientProfile.natDegree = Alo.k := by
  have hdiag := D.oneFiber_middle_diagonal F Alo Ahi
    hthree houtThree hnot hext
  rcases F.oneFiber_middle_degree_dichotomy
      Alo Ahi hthree houtThree hext hdiag with hlo | hhi
  · exact False.elim <|
      D.oneFiber_middle_lower_degree_impossible F Alo Ahi
        hthree houtThree hnot hext hdiag hlo
  · exact hhi

/-- **Central singleton frontier.**  Any surviving one-fibre branch contains
an actual carrier monomial with exponent `(k,0,0,V*(k-1))`. -/
theorem oneFiber_exists_central_carrierExponent
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
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k) :
    ∃ e ∈ P.carrier.support,
      e 0 = Alo.k ∧ e 1 = 0 ∧ e 2 = 0 ∧
      e 3 = F.V * (Alo.k - 1) := by
  have hdiag := D.oneFiber_middle_diagonal F Alo Ahi
    hthree houtThree hnot hext
  have hdeg := D.oneFiber_middle_profile_natDegree_eq_k F Alo Ahi
    hthree houtThree hnot hext
  exact F.exists_middleUpper_central_carrierExponent Alo hdiag hdeg

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
