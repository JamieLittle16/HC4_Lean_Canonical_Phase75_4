import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitNoInteriorSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInterior
import Mathlib.Tactic

/-!
# A19 first strict-interior layer in the unit PR pair Rees

The reverse pair-degree family itself is independent of the non-unit
inequality.  If endpoint-only support fails in either unit orientation, an
actual strict-interior source monomial appears before the locked pair-degree-one
layer.  Therefore the first positive actual pair-Rees layer has pair degree
strictly between `1` and the primitive highest degree `n`.

This is a source/support statement only; no first-variation or determinant
coefficient is consumed here.
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

/-- Left unit orientation: failure of endpoint-only support forces the first
positive pair-Rees layer strictly between pair degrees `1` and `n`. -/
theorem firstPositiveLayer_pair_strictInterior_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
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
    simpa [QsOtherFacetPrUnitLeftContactFrontierData.NoStrictInteriorSupport,
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
    rcases F.support_staircase_classification hthree houtThree heFilter.1 with
      ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hk
  constructor
  · by_contra hnotgt
    have heone : e 0 + e 1 = 1 := by omega
    have hqeq : q = F.highest.n - 1 := by
      rw [← heFilter.2, heone]
    omega
  · omega

/-- Right unit orientation: the same strict-interior conclusion. -/
theorem firstPositiveLayer_pair_strictInterior_unitRight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
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
    simpa [QsOtherFacetPrUnitRightContactFrontierData.NoStrictInteriorSupport,
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
    rcases F.support_staircase_classification hthree houtThree heFilter.1 with
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