import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
import Mathlib.Tactic

/-!
# A19 first strict-interior layer from the primitive-highest pair Rees

The pair-degree reverse Rees is oriented from the primitive highest slice.
If strict-interior support survives, its least positive actual parameter layer
cannot already be the locked pair-degree-one endpoint: any surviving interior
source monomial gives an earlier positive parameter exponent.

Consequently every monomial in the selected first positive pair-Rees layer has
pair degree strictly between `1` and the primitive highest degree `n`.  This is
the highest-end companion of the existing locked/contact first-interior layer.
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

/-- The exact support of a pair-Rees parameter layer is the carrier support
filtered by its pair-degree gap from the primitive highest slice. -/
theorem parameterLayer_support
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {n : ℕ}
    (D : QsOtherFacetPrPairReesData C P S n)
    (q : ℕ) :
    (familyParameterLayer D.family q).support =
      P.carrier.support.filter fun e => n - (e 0 + e 1) = q := by
  ext e
  rw [MvPolynomial.mem_support_iff]
  rw [D.parameterLayer_coeff q e]
  simp only [Finset.mem_filter]
  by_cases he : e ∈ P.carrier.support
  · have hc : MvPolynomial.coeff e P.carrier ≠ 0 :=
      MvPolynomial.mem_support_iff.mp he
    by_cases hq : n - (e 0 + e 1) = q
    · simp [he, hq, hc]
    · simp [he, hq]
  · simp [he]

/-- If strict-interior support exists, every exponent in the first positive
pair-Rees layer is itself strict interior. -/
theorem firstPositiveLayer_pair_strictInterior_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support,
      1 < e 0 + e 1 ∧ e 0 + e 1 < F.highest.n := by
  classical
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have hqpos : 0 < q := by
    dsimp [q]
    exact firstPositiveActualParameterOrder_pos D.family D.positiveLayer

  have hinterior :
      ∃ e : Fin 4 →₀ ℕ,
        e ∈ P.carrier.support ∧
        e 0 + e 1 ≠ 1 ∧
        e 0 + e 1 ≠ F.highest.n := by
    simpa [QsOtherFacetPrLeftVContactFrontierData.NoStrictInteriorSupport,
      HC4.Polynomial.rankThreeQuotientCoordinate] using hnot
  rcases hinterior with ⟨ei, hei, hei1, hein⟩
  have heipos : 1 ≤ ei 0 + ei 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using
      F.support_pair_pos hthree houtThree hei
  have heile : ei 0 + ei 1 ≤ F.highest.n := by
    rcases F.support_staircase_classification hthree houtThree hei with
      ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hk
  have heigt : 1 < ei 0 + ei 1 := by omega
  have heilt : ei 0 + ei 1 < F.highest.n := by omega

  let qi := F.highest.n - (ei 0 + ei 1)
  have hqipos : 0 < qi := by
    dsimp [qi]
    omega
  have hqilt : qi < F.highest.n - 1 := by
    dsimp [qi]
    omega
  have heiFamily : ei ∈ D.family.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [D.coeff_eq ei]
    rw [if_pos hei]
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Polynomial.C_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hei))
  have hqiCoeff :
      (MvPolynomial.coeff ei D.family).coeff qi ≠ 0 := by
    rw [D.coeff_eq ei]
    rw [if_pos hei]
    dsimp [qi]
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
    simp [MvPolynomial.mem_support_iff.mp hei]
  have hqiMem : qi ∈ familyParameterLayerOrders D.family :=
    (mem_familyParameterLayerOrders_iff D.family qi).2
      ⟨ei, heiFamily, hqiCoeff⟩
  have hqle : q ≤ qi := by
    dsimp [q]
    exact firstPositiveActualParameterOrder_le
      D.family D.positiveLayer hqiMem hqipos

  intro e he
  have heFilter :
      e ∈ P.carrier.support ∧
        F.highest.n - (e 0 + e 1) = q := by
    have hsupport := D.parameterLayer_support q
    rw [hsupport] at he
    exact Finset.mem_filter.mp he
  have hepos : 1 ≤ e 0 + e 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using
      F.support_pair_pos hthree houtThree heFilter.1
  have hele : e 0 + e 1 ≤ F.highest.n := by
    rcases F.support_staircase_classification
        hthree houtThree heFilter.1 with
      ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hk
  constructor
  · by_contra hnotgt
    have heone : e 0 + e 1 = 1 := by omega
    have hqeq : q = F.highest.n - 1 := by
      rw [← heFilter.2, heone]
    omega
  · omega

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
