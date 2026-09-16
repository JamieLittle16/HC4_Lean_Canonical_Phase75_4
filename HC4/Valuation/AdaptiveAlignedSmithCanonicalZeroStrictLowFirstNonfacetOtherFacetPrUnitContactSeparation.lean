import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrAffineCarrier
import Mathlib.Tactic

/-!
# A19 source-honest unit PR contact separation

At the genuine unit quotient the locked source endpoint has ordinary degree

    2 * (ell + 1) + 1,

while the primitive highest endpoint has degree

    2 * n + 1.

The source bound gives `n ≤ ell + 1`.  Equality would put the literal highest
source coefficient in contact layer zero, hence on the actual `.pr` contact
face, where the already-verified contact-face bound forces pair degree at most
one.  This contradicts the retained primitive-highest fact `2 ≤ n`.

Thus `n < ell + 1` in both transverse unit orientations.  No auxiliary clock
is identified with the zero blocker.
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

/-- Exact source top degree in the left unit contact frontier. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.topFace_degree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) :
    T.topFace.degree = 2 * (F.locked.ell + 1) + 1 := by
  have hdeg := C.qs_ray_facet_degree_eq_topFace
  rw [HC4.Polynomial.ordinaryDegree4] at hdeg
  simp [F.locked.facet_zero, F.locked.facet_one,
    F.locked.facet_two, F.locked.facet_three] at hdeg
  ring_nf at hdeg ⊢ <;> omega

/-- Exact source top degree in the right unit contact frontier. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.topFace_degree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    T.topFace.degree = 2 * (F.locked.ell + 1) + 1 := by
  have hdeg := C.qs_ray_facet_degree_eq_topFace
  rw [HC4.Polynomial.ordinaryDegree4] at hdeg
  simp [F.locked.facet_zero, F.locked.facet_one,
    F.locked.facet_two, F.locked.facet_three] at hdeg
  ring_nf at hdeg ⊢ <;> omega

private theorem unit_highest_weight_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) :
    HC4.Polynomial.ordinaryDegree4 F.highest.e0 = 2 * F.highest.n + 1 := by
  simp [HC4.Polynomial.ordinaryDegree4,
    F.highest.e0_zero, F.highest.e0_one,
    F.highest.e0_two, F.highest.e0_three,
    F.highest_V_eq_one]
  ring

private theorem unit_highest_weight_right
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    HC4.Polynomial.ordinaryDegree4 F.highest.e0 = 2 * F.highest.n + 1 := by
  simp [HC4.Polynomial.ordinaryDegree4,
    F.highest.e0_zero, F.highest.e0_one,
    F.highest.e0_two, F.highest.e0_three,
    F.highest_V_eq_one]
  ring

/-- In the left unit orientation the primitive highest fibre is strictly below
the locked source height. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.highest_n_lt_locked_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.highest.n < F.locked.ell + 1 := by
  have hbound := R.source_weight_le F.highest.e0_provenance.source_mem
  rw [F.highest.e0_zero, Nat.mul_zero, add_zero,
    unit_highest_weight_left F] at hbound
  rw [F.topFace_degree_eq] at hbound
  have hnle : F.highest.n ≤ F.locked.ell + 1 := by omega
  apply lt_of_le_of_ne hnle
  intro heq
  have hq :
      qsOtherFacetPrQuotientContactOrder (T := T) 1 1 F.highest.e0 = 0 := by
    rw [F.highest_contactOrder, F.topFace_degree_eq, heq]
    simp
  have hc := P.contactFamily_coeff_at_quotientContactOrder
    F.quotient R hthree houtThree F.highest.e0_provenance.carrier_mem
  rw [hq, familyParameterLayer_zero_eq_polynomialFamilySpecialFiber,
    R.contactFamily_specialFiber_eq_face] at hc
  have hface : F.highest.e0 ∈ C.face.support :=
    MvPolynomial.mem_support_iff.mpr hc.2
  have hpair := C.pr_contact_support_pair_le_one hthree houtThree hface
  rw [F.highest.e0_zero, F.highest.e0_one] at hpair
  have hn2 : 2 ≤ F.highest.n := F.highest.n_two_le
  omega

/-- Transverse-swapped unit orientation: the same strict source/contact
separation. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.highest_n_lt_locked_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.highest.n < F.locked.ell + 1 := by
  have hbound := R.source_weight_le F.highest.e0_provenance.source_mem
  rw [F.highest.e0_zero, Nat.mul_zero, add_zero,
    unit_highest_weight_right F] at hbound
  rw [F.topFace_degree_eq] at hbound
  have hnle : F.highest.n ≤ F.locked.ell + 1 := by omega
  apply lt_of_le_of_ne hnle
  intro heq
  have hq :
      qsOtherFacetPrQuotientContactOrder (T := T) 1 1 F.highest.e0 = 0 := by
    rw [F.highest_contactOrder, F.topFace_degree_eq, heq]
    simp
  have hc := P.contactFamily_coeff_at_quotientContactOrder
    F.quotient R hthree houtThree F.highest.e0_provenance.carrier_mem
  rw [hq, familyParameterLayer_zero_eq_polynomialFamilySpecialFiber,
    R.contactFamily_specialFiber_eq_face] at hc
  have hface : F.highest.e0 ∈ C.face.support :=
    MvPolynomial.mem_support_iff.mpr hc.2
  have hpair := C.pr_contact_support_pair_le_one hthree houtThree hface
  rw [F.highest.e0_zero, F.highest.e0_one] at hpair
  have hn2 : 2 ≤ F.highest.n := F.highest.n_two_le
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation