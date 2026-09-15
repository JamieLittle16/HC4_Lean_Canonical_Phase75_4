import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseExtremalFibers
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorAffineLayer
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorAffineLayer
import Mathlib.Tactic

/-!
# A19 dual extremal affine layers of the finite staircase

This file upgrades the raw extremal-layer statements to the affine packages
used by the two first-variation equations.

For any surviving strict-interior source monomial `e`, the contact-side affine
layer has pair degree at most `pair(e)`, while the pair-Rees affine layer has
pair degree at least `pair(e)`.

A useful immediate consequence is the one-fibre collapse: if the two selected
extremal pair degrees agree, then every strict-interior source monomial has
that pair degree, hence lies in the same normalized quotient fibre.

This is still bookkeeping.  No new determinant identity or recurrence is
asserted here.
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

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- The contact-side affine package records the least surviving interior pair
degree. -/
theorem pair_le_of_strictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair)
    (helt : (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n) :
    A.k ≤ (rankThreeQuotientCoordinate 1 F.V e).pair := by
  have hLne :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨a, ha⟩
  have hmin := D.firstPositiveLayer_pair_minimal
    hthree houtThree hnot ha he hegt helt
  have haPair : a 0 + a 1 = A.k := (A.coordinates a ha).1
  have hminNat : a 0 + a 1 ≤ e 0 + e 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hmin
  have h : A.k ≤ e 0 + e 1 := by omega
  simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using h

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

namespace QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- The pair-Rees affine package records the greatest surviving interior pair
degree. -/
theorem pair_ge_of_strictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair)
    (helt : (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n) :
    (rankThreeQuotientCoordinate 1 F.V e).pair ≤ A.k := by
  have hLne :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨a, ha⟩
  have hmax := D.firstPositiveLayer_pair_maximal_left
    F hthree houtThree hnot ha he hegt helt
  have haPair : a 0 + a 1 = A.k := (A.coordinates a ha).1
  have hmaxNat : e 0 + e 1 ≤ a 0 + a 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hmax
  have h : e 0 + e 1 ≤ A.k := by omega
  simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using h

end QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- Every strict-interior support point lies between the two selected extremal
pair degrees. -/
theorem QsOtherFacetPrLeftVContactFrontierData.strictInterior_pair_between
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair)
    (helt : (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n) :
    Alo.k ≤ (rankThreeQuotientCoordinate 1 F.V e).pair ∧
      (rankThreeQuotientCoordinate 1 F.V e).pair ≤ Ahi.k := by
  exact ⟨
    Alo.pair_le_of_strictInterior hthree houtThree hnot he hegt helt,
    Ahi.pair_ge_of_strictInterior hthree houtThree hnot he hegt helt⟩

/-- If the two extremal selected pair degrees coincide, every strict-interior
source monomial has exactly that pair degree. -/
theorem QsOtherFacetPrLeftVContactFrontierData.strictInterior_pair_eq_of_extrema_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair)
    (helt : (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n) :
    (rankThreeQuotientCoordinate 1 F.V e).pair = Alo.k := by
  rcases F.strictInterior_pair_between
      Alo Ahi hthree houtThree hnot he hegt helt with ⟨hlo, hhi⟩
  rw [← hext] at hhi
  exact Nat.le_antisymm hhi hlo

/-- Under coincident extrema, any two strict-interior source monomials lie in
the same normalized quotient fibre. -/
theorem QsOtherFacetPrLeftVContactFrontierData.strictInterior_quotient_eq_of_extrema_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair)
    (helt : (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n)
    (hfgt : 1 < (rankThreeQuotientCoordinate 1 F.V f).pair)
    (hflt : (rankThreeQuotientCoordinate 1 F.V f).pair < F.highest.n) :
    rankThreeQuotientCoordinate 1 F.V e =
      rankThreeQuotientCoordinate 1 F.V f := by
  have hePair := F.strictInterior_pair_eq_of_extrema_eq
    Alo Ahi hthree houtThree hnot hext he hegt helt
  have hfPair := F.strictInterior_pair_eq_of_extrema_eq
    Alo Ahi hthree houtThree hnot hext hf hfgt hflt
  apply F.support_quotient_eq_of_pair_eq he hf
  exact hePair.trans hfPair.symm

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
