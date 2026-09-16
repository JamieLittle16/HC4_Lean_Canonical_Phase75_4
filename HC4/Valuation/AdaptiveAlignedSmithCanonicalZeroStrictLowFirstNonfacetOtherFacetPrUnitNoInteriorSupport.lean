import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPairRees
import Mathlib.Tactic

/-!
# A19 endpoint-only support in the unit PR branch

The unit quotient has the same finite staircase endpoint structure as the
non-unit branch.  This file isolates the exact endpoint-only alternative before
we attack surviving strict-interior unit fibres.

If every carrier monomial has pair degree either `1` or the primitive highest
pair degree `n`, quotient-fibre rigidity identifies the pair-degree-one fibre
with the two literal locked source exponents, while the pair-degree-`n` fibre
is exactly the primitive highest slice.  Hence the whole carrier has precisely
four source monomials.

No determinant argument is used here.
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

/-- Endpoint-only support in the left unit orientation. -/
def QsOtherFacetPrUnitLeftContactFrontierData.NoStrictInteriorSupport
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) : Prop :=
  ∀ {e : Fin 4 →₀ ℕ}, e ∈ P.carrier.support →
    (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = 1 ∨
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = F.highest.n

/-- Endpoint-only support in the right unit orientation. -/
def QsOtherFacetPrUnitRightContactFrontierData.NoStrictInteriorSupport
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) : Prop :=
  ∀ {e : Fin 4 →₀ ℕ}, e ∈ P.carrier.support →
    (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = 1 ∨
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = F.highest.n

private theorem unit_left_highest_pairLevel_eq
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

private theorem unit_right_highest_pairLevel_eq
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

/-- Endpoint-only left unit support is exactly the two locked and two primitive
highest source monomials. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_eq_locked_highest_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) :
    P.carrier.support =
      {C.ray.facetExponent, C.ray.outsideExponent,
        F.highest.e0, F.highest.e1} := by
  classical
  have hlevel : S.pairLevel = (F.highest.n : ℤ) :=
    unit_left_highest_pairLevel_eq F
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    rcases hno he with hlocked | hhighest
    · have hpairNat : e 0 + e 1 = 1 := by
        simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hlocked
      have hpairE : qsOtherFacetPairDegree .pr e = (1 : ℤ) := by
        exact_mod_cast hpairNat
      have hpairF :
          qsOtherFacetPairDegree .pr C.ray.facetExponent = (1 : ℤ) := by
        simp [qsOtherFacetPairDegree,
          F.locked.facet_zero, F.locked.facet_one]
      have hqEF :
          HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e =
            HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent :=
        F.quotient.pair_fiber he F.locked.facet_provenance.carrier_mem
          (hpairE.trans hpairF.symm)
      have hpairO :
          qsOtherFacetPairDegree .pr C.ray.outsideExponent = (1 : ℤ) := by
        simp [qsOtherFacetPairDegree,
          F.locked.outside_zero, F.locked.outside_one]
      have hqFO :
          HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent =
            HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.outsideExponent :=
        F.quotient.pair_fiber
          F.locked.facet_provenance.carrier_mem
          F.locked.outside_provenance.carrier_mem
          (hpairF.trans hpairO.symm)
      have he0cases : e 0 = 0 ∨ e 0 = 1 := by omega
      rcases he0cases with he0 | he0
      · have heq : e = C.ray.facetExponent :=
          HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 1 e C.ray.facetExponent hqEF (by
              rw [he0, F.locked.facet_zero])
        exact Or.inl heq
      · have heq : e = C.ray.outsideExponent :=
          HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 1 e C.ray.outsideExponent (hqEF.trans hqFO) (by
              rw [he0, F.locked.outside_zero])
        exact Or.inr (Or.inl heq)
    · have hpairNat : e 0 + e 1 = F.highest.n := by
        simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hhighest
      have hpairE :
          qsOtherFacetPairDegree .pr e = (F.highest.n : ℤ) := by
        exact_mod_cast hpairNat
      have hweight :
          Finsupp.weight (qsOtherFacetPairWeight .pr) e = S.pairLevel := by
        rw [finsupp_weight_qsOtherFacetPairWeight, hpairE, hlevel]
      have hcoeffS : MvPolynomial.coeff e S.slice ≠ 0 := by
        rw [S.slice_eq_initialForm, HC4.Polynomial.coeff_initialForm,
          if_pos hweight]
        exact MvPolynomial.mem_support_iff.mp he
      have heS : e ∈ S.slice.support :=
        MvPolynomial.mem_support_iff.mpr hcoeffS
      rw [F.highest.slice_support_eq] at heS
      simp only [Finset.mem_insert, Finset.mem_singleton] at heS
      rcases heS with heq | heq
      · exact Or.inr (Or.inr (Or.inl heq))
      · exact Or.inr (Or.inr (Or.inr heq))
  · intro he
    rcases he with he | he | he | he
    · simpa [he] using F.locked.facet_provenance.carrier_mem
    · simpa [he] using F.locked.outside_provenance.carrier_mem
    · simpa [he] using F.highest.e0_provenance.carrier_mem
    · simpa [he] using F.highest.e1_provenance.carrier_mem

/-- The transverse-swapped unit orientation has the identical endpoint-only
support statement. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_eq_locked_highest_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) :
    P.carrier.support =
      {C.ray.facetExponent, C.ray.outsideExponent,
        F.highest.e0, F.highest.e1} := by
  classical
  have hlevel : S.pairLevel = (F.highest.n : ℤ) :=
    unit_right_highest_pairLevel_eq F
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    rcases hno he with hlocked | hhighest
    · have hpairNat : e 0 + e 1 = 1 := by
        simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hlocked
      have hpairE : qsOtherFacetPairDegree .pr e = (1 : ℤ) := by
        exact_mod_cast hpairNat
      have hpairF :
          qsOtherFacetPairDegree .pr C.ray.facetExponent = (1 : ℤ) := by
        simp [qsOtherFacetPairDegree,
          F.locked.facet_zero, F.locked.facet_one]
      have hqEF :
          HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e =
            HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent :=
        F.quotient.pair_fiber he F.locked.facet_provenance.carrier_mem
          (hpairE.trans hpairF.symm)
      have hpairO :
          qsOtherFacetPairDegree .pr C.ray.outsideExponent = (1 : ℤ) := by
        simp [qsOtherFacetPairDegree,
          F.locked.outside_zero, F.locked.outside_one]
      have hqFO :
          HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent =
            HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.outsideExponent :=
        F.quotient.pair_fiber
          F.locked.facet_provenance.carrier_mem
          F.locked.outside_provenance.carrier_mem
          (hpairF.trans hpairO.symm)
      have he0cases : e 0 = 0 ∨ e 0 = 1 := by omega
      rcases he0cases with he0 | he0
      · have heq : e = C.ray.facetExponent :=
          HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 1 e C.ray.facetExponent hqEF (by
              rw [he0, F.locked.facet_zero])
        exact Or.inl heq
      · have heq : e = C.ray.outsideExponent :=
          HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 1 e C.ray.outsideExponent (hqEF.trans hqFO) (by
              rw [he0, F.locked.outside_zero])
        exact Or.inr (Or.inl heq)
    · have hpairNat : e 0 + e 1 = F.highest.n := by
        simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hhighest
      have hpairE :
          qsOtherFacetPairDegree .pr e = (F.highest.n : ℤ) := by
        exact_mod_cast hpairNat
      have hweight :
          Finsupp.weight (qsOtherFacetPairWeight .pr) e = S.pairLevel := by
        rw [finsupp_weight_qsOtherFacetPairWeight, hpairE, hlevel]
      have hcoeffS : MvPolynomial.coeff e S.slice ≠ 0 := by
        rw [S.slice_eq_initialForm, HC4.Polynomial.coeff_initialForm,
          if_pos hweight]
        exact MvPolynomial.mem_support_iff.mp he
      have heS : e ∈ S.slice.support :=
        MvPolynomial.mem_support_iff.mpr hcoeffS
      rw [F.highest.slice_support_eq] at heS
      simp only [Finset.mem_insert, Finset.mem_singleton] at heS
      rcases heS with heq | heq
      · exact Or.inr (Or.inr (Or.inl heq))
      · exact Or.inr (Or.inr (Or.inr heq))
  · intro he
    rcases he with he | he | he | he
    · simpa [he] using F.locked.facet_provenance.carrier_mem
    · simpa [he] using F.locked.outside_provenance.carrier_mem
    · simpa [he] using F.highest.e0_provenance.carrier_mem
    · simpa [he] using F.highest.e1_provenance.carrier_mem

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation