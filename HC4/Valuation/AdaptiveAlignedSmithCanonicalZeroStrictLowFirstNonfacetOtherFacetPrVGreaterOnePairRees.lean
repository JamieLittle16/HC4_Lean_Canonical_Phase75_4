import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import HC4.Valuation.SingularBoundedReverseWeightedRees
import HC4.Valuation.ActualParameterLayer
import Mathlib.Tactic

/-!
# A19 pair-degree reverse Rees of the non-unit PR planar carrier

The whole-carrier support classification proves that every actual monomial has
`.pr` pair degree between `1` and the primitive highest degree `n`.  Therefore
we may form the bounded reverse Rees family for the natural pair weight

    (1,1,0,0).

Its parameter exponent is exactly `n-(e0+e1)`.  The zero layer is therefore
the already-retained highest pair slice `S.slice`; no new initial form or copy
of the source is introduced.  Since the planar carrier has identically zero
Hessian determinant, the whole pair-Rees family is Hessian-singular by the
existing singular reverse-Rees covariance theorem.

The locked source endpoints have pair degree one and `n>=2`, so the family has
a genuine positive actual layer.  This is the honest first-deformation family
used by the forthcoming determinant linearisation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Natural form of the `.pr` pair weight. -/
def qsPrPairNatWeight : Fin 4 → ℕ := ![1, 1, 0, 0]

@[simp] theorem weight_qsPrPairNatWeight
    (e : Fin 4 →₀ ℕ) :
    Finsupp.weight qsPrPairNatWeight e = e 0 + e 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [qsPrPairNatWeight]
  · intro i
    simp

/-- Casting the natural pair weight gives exactly the integer pair weight used
by the planar carrier. -/
theorem cast_qsPrPairNatWeight_eq_pairWeight :
    (fun i : Fin 4 => (qsPrPairNatWeight i : ℤ)) =
      AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.qsOtherFacetPairWeight .pr := by
  funext i
  fin_cases i <;>
    simp [qsPrPairNatWeight,
      AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.qsOtherFacetPairWeight]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Source-honest pair-degree Rees package common to either non-unit
orientation.  The orientation-specific frontier is used only to prove the
support bound and identify the same primitive highest degree `n`. -/
structure QsOtherFacetPrPairReesData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (n : ℕ) where
  n_two_le : 2 ≤ n
  slice_pairLevel_eq : S.pairLevel = (n : ℤ)
  bound : HasReverseWeightBound qsPrPairNatWeight n P.carrier
  family : MvPolynomial (Fin 4) (Polynomial K)
  family_eq :
    family = reverseWeightedReesFamily qsPrPairNatWeight n P.carrier bound
  specialFiber_eq_slice : polynomialFamilySpecialFiber family = S.slice
  hessian_zero : HC4.Polynomial.hessianDeterminant family = 0
  positiveLayer : HasPositiveActualParameterLayer family

namespace QsOtherFacetPrPairReesData

/-- Exact coefficient of the pair-Rees family at a source monomial. -/
theorem coeff_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {n : ℕ}
    (D : QsOtherFacetPrPairReesData C P S n)
    (e : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff e D.family =
      if e ∈ P.carrier.support then
        Polynomial.X ^ (n - (e 0 + e 1)) *
          Polynomial.C (MvPolynomial.coeff e P.carrier)
      else 0 := by
  rw [D.family_eq, reverseWeightedReesFamily_coeff]
  simp only [weight_qsPrPairNatWeight]

/-- Exact parameter layer: order `q` is precisely pair degree `n-q`. -/
theorem parameterLayer_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {n : ℕ}
    (D : QsOtherFacetPrPairReesData C P S n)
    (q : ℕ) (e : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff e (familyParameterLayer D.family q) =
      if e ∈ P.carrier.support ∧ n - (e 0 + e 1) = q then
        MvPolynomial.coeff e P.carrier
      else 0 := by
  rw [D.family_eq, reverseWeightedReesFamily_parameterLayer_coeff]
  simp only [weight_qsPrPairNatWeight]

end QsOtherFacetPrPairReesData

private theorem highest_pairLevel_eq_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    S.pairLevel = (F.highest.n : ℤ) := by
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hp := (S.support_parent_and_pairLevel he0S).2
  simpa [qsOtherFacetPairDegree, F.highest.e0_zero, F.highest.e0_one] using hp.symm

private theorem highest_pairLevel_eq_right
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) :
    S.pairLevel = (F.highest.n : ℤ) := by
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hp := (S.support_parent_and_pairLevel he0S).2
  simpa [qsOtherFacetPairDegree, F.highest.e0_zero, F.highest.e0_one] using hp.symm

private theorem pair_rees_specialFiber_eq_slice
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
  rw [hlevel]
  exact S.slice_eq_initialForm.symm

/-- Build the pair-Rees package in the left `(1,V)` orientation. -/
theorem QsOtherFacetPrLeftVContactFrontierData.pairRees
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrPairReesData C P S F.highest.n) := by
  let n := F.highest.n
  have hlevel : S.pairLevel = (n : ℤ) := by
    simpa [n] using highest_pairLevel_eq_left F
  have hbound : HasReverseWeightBound qsPrPairNatWeight n P.carrier := by
    intro e he
    have hc := F.support_staircase_classification hthree houtThree he
    rcases hc with ⟨j, _hj, hkN, _hjell, _hj0, _hjellEq⟩
    simpa [n, HC4.Polynomial.rankThreeQuotientCoordinate] using hkN
  let Q := reverseWeightedReesFamily qsPrPairNatWeight n P.carrier hbound
  have hspecial : polynomialFamilySpecialFiber Q = S.slice := by
    dsimp [Q]
    exact pair_rees_specialFiber_eq_slice S n hlevel hbound
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
      omega
    have hn : 0 < n - 1 := by
      dsimp [n]
      omega
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

/-- Build the same pair-Rees package in the swapped `(V,1)` orientation. -/
theorem QsOtherFacetPrRightVContactFrontierData.pairRees
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrPairReesData C P S F.highest.n) := by
  let n := F.highest.n
  have hlevel : S.pairLevel = (n : ℤ) := by
    simpa [n] using highest_pairLevel_eq_right F
  have hbound : HasReverseWeightBound qsPrPairNatWeight n P.carrier := by
    intro e he
    have hc := F.support_staircase_classification hthree houtThree he
    rcases hc with ⟨j, _hj, hkN, _hjell, _hj0, _hjellEq⟩
    simpa [n, HC4.Polynomial.rankThreeQuotientCoordinate] using hkN
  let Q := reverseWeightedReesFamily qsPrPairNatWeight n P.carrier hbound
  have hspecial : polynomialFamilySpecialFiber Q = S.slice := by
    dsimp [Q]
    exact pair_rees_specialFiber_eq_slice S n hlevel hbound
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
      omega
    have hn : 0 < n - 1 := by
      dsimp [n]
      omega
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
