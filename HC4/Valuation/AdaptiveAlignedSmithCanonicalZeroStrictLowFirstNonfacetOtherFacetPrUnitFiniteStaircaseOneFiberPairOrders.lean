import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiber
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseExtremalFibers
import Mathlib.Tactic

/-!
# A19 exact unit pair-Rees orders in the one-fibre branch

When the least and greatest surviving strict-interior unit pair degrees
coincide, every strict-interior source monomial lies on that same pair fibre.
Since the unit pair-degree reverse Rees has parameter order `n - pair`, its
actual parameter support is confined to `0`, `n-k`, and `n-1`.
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

namespace QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData

/-- The first positive unit pair-Rees order is exactly the gap from the
primitive-highest pair degree to the selected interior pair degree. -/
theorem firstPositiveOrder_eq_pairGap
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D) :
    firstPositiveActualParameterOrder D.family D.positiveLayer =
      F.highest.n - A.k := by
  have hLne :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨e, he⟩
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have hs := D.parameterLayer_support q
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    have he' := he
    rw [hs] at he'
    exact Finset.mem_filter.mp he'
  have hpair : e 0 + e 1 = A.k :=
    (A.coordinates e (by simpa [q] using he)).1
  dsimp [q]
  omega

end QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData

namespace QsOtherFacetPrPairReesData

/-- If the selected unit extrema coincide, every surviving strict-interior
carrier monomial lies on their common pair fibre. -/
theorem strictInterior_pair_eq_of_unitLeft_extrema_eq
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
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 1 e).pair)
    (helt : (rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n) :
    (rankThreeQuotientCoordinate 1 1 e).pair = Alo.k := by
  have hLloNe :
      familyParameterLayer Dlo.family
        (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero Dlo.family Dlo.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLloNe with ⟨a, ha⟩
  have hloRaw := Dlo.firstPositiveLayer_pair_minimal
    hthree houtThree hnot ha he hegt helt
  have hpairLo : (rankThreeQuotientCoordinate 1 1 a).pair = Alo.k := by
    have hcoords := (Alo.coordinates a ha).1
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hcoords
  have hlo : Alo.k ≤ (rankThreeQuotientCoordinate 1 1 e).pair := by
    simpa [hpairLo] using hloRaw

  have hLhiNe :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLhiNe with ⟨b, hb⟩
  have hhiRaw := D.firstPositiveLayer_pair_maximal_unitLeft
    F hthree houtThree hnot hb he hegt helt
  have hpairHi : (rankThreeQuotientCoordinate 1 1 b).pair = Ahi.k := by
    have hcoords := (Ahi.coordinates b hb).1
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hcoords
  have hhi : (rankThreeQuotientCoordinate 1 1 e).pair ≤ Ahi.k := by
    simpa [hpairHi] using hhiRaw
  omega

/-- In the unit one-fibre branch every nonzero pair-Rees parameter layer is
one of exactly three orders: highest endpoint, common interior fibre, or
locked endpoint. -/
theorem parameterLayer_order_trichotomy_of_unitLeft_oneFiber
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
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    (q : ℕ)
    (hq : familyParameterLayer D.family q ≠ 0) :
    q = 0 ∨ q = F.highest.n - Alo.k ∨ q = F.highest.n - 1 := by
  rcases MvPolynomial.support_nonempty.mpr hq with ⟨e, he⟩
  have hs := D.parameterLayer_support q
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    have he' := he
    rw [hs] at he'
    exact Finset.mem_filter.mp he'
  let pair := (rankThreeQuotientCoordinate 1 1 e).pair
  have hpairNat : pair = e 0 + e 1 := by rfl
  have hpos := F.support_pair_pos hthree houtThree heFilter.1
  rcases F.support_staircase_classification hthree houtThree heFilter.1 with
    ⟨j, _hj, hle, _hjell, _hj0, _hjellEq⟩
  by_cases htop : pair = F.highest.n
  · left
    rw [← heFilter.2]
    rw [← hpairNat, htop]
    omega
  by_cases hlock : pair = 1
  · right
    right
    rw [← heFilter.2]
    rw [← hpairNat, hlock]
  · have hgt : 1 < pair := by omega
    have hlt : pair < F.highest.n := by omega
    have heq := D.strictInterior_pair_eq_of_unitLeft_extrema_eq
      F Alo Ahi hthree houtThree hnot hext heFilter.1 hgt hlt
    right
    left
    rw [← heFilter.2]
    rw [← hpairNat, heq]

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
