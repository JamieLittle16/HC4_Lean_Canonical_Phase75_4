import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseDualExtrema
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorAffineLayer
import Mathlib.Tactic

/-!
# A19 exact pair-Rees orders in the one-fibre branch

When the lowest and highest selected strict-interior pair degrees coincide,
every source monomial has pair degree `1`, `k`, or `n`.  Since the pair-degree
reverse Rees attaches parameter order `n-pair`, its entire actual parameter
support is therefore confined to

    0,  n-k,  n-1.

This is the exact three-layer bookkeeping needed by the remaining determinant
coefficient argument.  No determinant calculation occurs here.
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

namespace QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- The first positive pair-Rees order is literally the gap from the primitive
highest pair degree to the selected interior pair degree. -/
theorem firstPositiveOrder_eq_pairGap
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) :
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
    rw [hs] at he
    exact Finset.mem_filter.mp he
  have hpair : e 0 + e 1 = A.k := (A.coordinates e (by simpa [q] using he)).1
  dsimp [q]
  omega

end QsOtherFacetPrPairFirstInteriorAffineLayerData

namespace QsOtherFacetPrPairReesData

/-- **Three actual pair-Rees orders in the one-fibre branch.**  Every nonzero
parameter layer is either the primitive-highest zero layer, the unique
strict-interior layer, or the locked pair-degree-one layer. -/
theorem parameterLayer_order_trichotomy_of_oneFiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
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
    (hext : Alo.k = Ahi.k)
    (q : ℕ)
    (hq : familyParameterLayer D.family q ≠ 0) :
    q = 0 ∨ q = F.highest.n - Alo.k ∨ q = F.highest.n - 1 := by
  rcases MvPolynomial.support_nonempty.mpr hq with ⟨e, he⟩
  have hs := D.parameterLayer_support q
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    rw [hs] at he
    exact Finset.mem_filter.mp he
  let pair := (rankThreeQuotientCoordinate 1 F.V e).pair
  have hpairNat : pair = e 0 + e 1 := by
    rfl
  have hpos := F.support_pair_pos hthree houtThree heFilter.1
  have hclass := F.support_staircase_classification
    hthree houtThree heFilter.1
  rcases hclass with ⟨j, _hj, hle, _hjell, _hj0, _hjellEq⟩
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
    have heq := F.strictInterior_pair_eq_of_extrema_eq
      Alo Ahi hthree houtThree hnot hext heFilter.1 hgt hlt
    right
    left
    rw [← heFilter.2]
    rw [← hpairNat, heq]

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
