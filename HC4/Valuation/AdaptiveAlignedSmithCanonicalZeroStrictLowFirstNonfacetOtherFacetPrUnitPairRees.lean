import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseClassification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairRees
import Mathlib.Tactic

/-!
# A19 source-honest unit PR pair-degree reverse Rees

The pair-degree reverse-Rees package is independent of the strict inequality
`1 < V`: it only needs the global pair-degree bound, the primitive highest
slice, and the locked pair-degree-one endpoint.  The unit staircase
classification supplies those facts at direction `(1,-1,-1,-1)`.

This file therefore reuses the exact generic `QsOtherFacetPrPairReesData`
record.  Its zero layer is the literal highest slice, its determinant is
identically zero by reverse-Rees covariance, and the locked source endpoint
provides a genuine positive actual layer.
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

private theorem unit_highest_pairLevel_eq_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) :
    S.pairLevel = (F.highest.n : ℤ) := by
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hp := (S.support_parent_and_pairLevel he0S).2
  simpa [qsOtherFacetPairDegree, F.highest.e0_zero, F.highest.e0_one] using hp.symm

private theorem unit_highest_pairLevel_eq_right
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    S.pairLevel = (F.highest.n : ℤ) := by
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hp := (S.support_parent_and_pairLevel he0S).2
  simpa [qsOtherFacetPairDegree, F.highest.e0_zero, F.highest.e0_one] using hp.symm

private theorem unit_pair_rees_specialFiber_eq_slice
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (n : ℕ)
    (hlevel : S.pairLevel = (n : ℤ))
    (hbound : HasReverseWeightBound qsPrPairNatWeight n P.carrier) :
    polynomialFamilySpecialFiber
        (reverseWeightedReesFamily qsPrPairNatWeight n P.carrier hbound) =
      S.slice := by
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  rw [cast_qsPrPairNatWeight_eq_pairWeight]
  rw [← hlevel]
  exact S.slice_eq_initialForm.symm

/-- Unit left orientation: source-honest pair-Rees package. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.pairRees
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrPairReesData C P S F.highest.n) := by
  let n := F.highest.n
  have hlevel : S.pairLevel = (n : ℤ) := by
    simpa [n] using unit_highest_pairLevel_eq_left F
  have hbound : HasReverseWeightBound qsPrPairNatWeight n P.carrier := by
    intro e he
    have hc := F.support_staircase_classification hthree houtThree he
    rcases hc with ⟨j, _hj, hkN, _hjell, _hj0, _hjellEq⟩
    simpa [n, HC4.Polynomial.rankThreeQuotientCoordinate] using hkN
  let Q := reverseWeightedReesFamily qsPrPairNatWeight n P.carrier hbound
  have hspecial : polynomialFamilySpecialFiber Q = S.slice := by
    dsimp [Q]
    exact unit_pair_rees_specialFiber_eq_slice S n hlevel hbound
  have hdet : HC4.Polynomial.hessianDeterminant Q = 0 := by
    dsimp [Q]
    exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
      qsPrPairNatWeight n P.carrier hbound P.hessian_zero
  have hpos : HasPositiveActualParameterLayer Q := by
    classical
    let e := C.ray.facetExponent
    have he : e ∈ P.carrier.support := F.locked.facet_provenance.carrier_mem
    have hpair : e 0 + e 1 = 1 := by
      dsimp [e]
      rw [F.locked.facet_zero, F.locked.facet_one]
    have htwo : 2 ≤ n := by
      simpa [n] using F.highest.n_two_le
    have hn : 0 < n - 1 := by omega
    have hcoeff :
        (MvPolynomial.coeff e Q).coeff (n - 1) ≠ 0 := by
      dsimp [Q]
      rw [reverseWeightedReesFamily_coeff]
      simp only [weight_qsPrPairNatWeight, he, if_true]
      rw [hpair]
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
      simp [MvPolynomial.mem_support_iff.mp he]
    have hmem : n - 1 ∈ familyParameterLayerOrders Q :=
      (mem_familyParameterLayerOrders_iff Q (n - 1)).2
        ⟨e, by
          dsimp [Q]
          apply MvPolynomial.mem_support_iff.mpr
          rw [reverseWeightedReesFamily_coeff]
          simp only [weight_qsPrPairNatWeight, he, if_true]
          rw [hpair]
          exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
            (Polynomial.C_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)),
          hcoeff⟩
    exact ⟨n - 1, Finset.mem_filter.mpr ⟨hmem, hn⟩⟩
  exact ⟨{
    n_two_le := F.highest.n_two_le
    slice_pairLevel_eq := by simpa [n] using hlevel
    bound := hbound
    family := Q
    family_eq := rfl
    specialFiber_eq_slice := hspecial
    hessian_zero := hdet
    positiveLayer := hpos
  }⟩

/-- Unit right orientation: the same pair-Rees package with transverse highest
endpoint swapped. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.pairRees
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrPairReesData C P S F.highest.n) := by
  let n := F.highest.n
  have hlevel : S.pairLevel = (n : ℤ) := by
    simpa [n] using unit_highest_pairLevel_eq_right F
  have hbound : HasReverseWeightBound qsPrPairNatWeight n P.carrier := by
    intro e he
    have hc := F.support_staircase_classification hthree houtThree he
    rcases hc with ⟨j, _hj, hkN, _hjell, _hj0, _hjellEq⟩
    simpa [n, HC4.Polynomial.rankThreeQuotientCoordinate] using hkN
  let Q := reverseWeightedReesFamily qsPrPairNatWeight n P.carrier hbound
  have hspecial : polynomialFamilySpecialFiber Q = S.slice := by
    dsimp [Q]
    exact unit_pair_rees_specialFiber_eq_slice S n hlevel hbound
  have hdet : HC4.Polynomial.hessianDeterminant Q = 0 := by
    dsimp [Q]
    exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
      qsPrPairNatWeight n P.carrier hbound P.hessian_zero
  have hpos : HasPositiveActualParameterLayer Q := by
    classical
    let e := C.ray.facetExponent
    have he : e ∈ P.carrier.support := F.locked.facet_provenance.carrier_mem
    have hpair : e 0 + e 1 = 1 := by
      dsimp [e]
      rw [F.locked.facet_zero, F.locked.facet_one]
    have htwo : 2 ≤ n := by
      simpa [n] using F.highest.n_two_le
    have hn : 0 < n - 1 := by omega
    have hcoeff :
        (MvPolynomial.coeff e Q).coeff (n - 1) ≠ 0 := by
      dsimp [Q]
      rw [reverseWeightedReesFamily_coeff]
      simp only [weight_qsPrPairNatWeight, he, if_true]
      rw [hpair]
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
      simp [MvPolynomial.mem_support_iff.mp he]
    have hmem : n - 1 ∈ familyParameterLayerOrders Q :=
      (mem_familyParameterLayerOrders_iff Q (n - 1)).2
        ⟨e, by
          dsimp [Q]
          apply MvPolynomial.mem_support_iff.mpr
          rw [reverseWeightedReesFamily_coeff]
          simp only [weight_qsPrPairNatWeight, he, if_true]
          rw [hpair]
          exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
            (Polynomial.C_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)),
          hcoeff⟩
    exact ⟨n - 1, Finset.mem_filter.mpr ⟨hmem, hn⟩⟩
  exact ⟨{
    n_two_le := F.highest.n_two_le
    slice_pairLevel_eq := by simpa [n] using hlevel
    bound := hbound
    family := Q
    family_eq := rfl
    specialFiber_eq_slice := hspecial
    hessian_zero := hdet
    positiveLayer := hpos
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
