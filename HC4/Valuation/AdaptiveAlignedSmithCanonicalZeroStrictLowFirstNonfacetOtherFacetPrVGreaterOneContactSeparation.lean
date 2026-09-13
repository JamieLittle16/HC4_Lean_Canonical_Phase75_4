import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneWallSlopeConsequences
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrAffineCarrier
import Mathlib.Tactic

/-!
# A19 the non-unit highest PR fibre lies strictly above contact

The locked source facet is an actual top-face exponent.  In either non-unit
orientation its ordinary degree is

    (V + 1) * (ell + 1) + 1,

so this is exactly the source top degree `D`.

The primitive highest pair has source weight

    (V + 1) * n + 1.

The honest contact bound gives `n <= ell + 1`.  Equality is impossible: in
that case the two highest coefficients occur in contact parameter layer zero,
therefore on the actual `.pr` contact face.  But the already-proved contact
face bound says `e0 + e1 <= 1`, while the highest pair has pair degree
`n >= 2`.

Hence

    n < ell + 1.

This is the first genuinely contact-theoretic exclusion in the normalized
carrier classification.  It uses literal source coefficients and the actual
contact special fibre; no clocks are identified.
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

private theorem le_from_scaled_degree_bound
    (V n m : ℕ) (h : (V + 1) * n + 1 ≤ (V + 1) * m + 1) : n ≤ m := by
  by_contra hnm
  have hmn : m < n := Nat.lt_of_not_ge hnm
  have hVZ : (0 : ℤ) < (V : ℤ) + 1 := by positivity
  have hdiffZ : (0 : ℤ) < (n : ℤ) - (m : ℤ) := by
    exact_mod_cast hmn
  have hprod :
      (0 : ℤ) < ((V : ℤ) + 1) * ((n : ℤ) - (m : ℤ)) :=
    mul_pos hVZ hdiffZ
  have hz :
      (((V + 1) * n + 1 : ℕ) : ℤ) ≤
        (((V + 1) * m + 1 : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at hz
  nlinarith

/-- Exact source top degree in the `(1,V)` contact frontier. -/
theorem QsOtherFacetPrLeftVContactFrontierData.topFace_degree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    T.topFace.degree = (F.V + 1) * (F.locked.ell + 1) + 1 := by
  have hdeg := C.qs_ray_facet_degree_eq_topFace
  rw [HC4.Polynomial.ordinaryDegree4] at hdeg
  simp [F.locked.facet_zero, F.locked.facet_one,
    F.locked.facet_two, F.locked.facet_three] at hdeg
  omega

/-- Exact source top degree in the swapped `(V,1)` frontier. -/
theorem QsOtherFacetPrRightVContactFrontierData.topFace_degree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) :
    T.topFace.degree = (F.V + 1) * (F.locked.ell + 1) + 1 := by
  have hdeg := C.qs_ray_facet_degree_eq_topFace
  rw [HC4.Polynomial.ordinaryDegree4] at hdeg
  simp [F.locked.facet_zero, F.locked.facet_one,
    F.locked.facet_two, F.locked.facet_three] at hdeg
  omega

private theorem highest_weight_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    HC4.Polynomial.ordinaryDegree4 F.highest.e0 =
      (F.V + 1) * F.highest.n + 1 := by
  simp [HC4.Polynomial.ordinaryDegree4,
    F.highest.e0_zero, F.highest.e0_one,
    F.highest.e0_two, F.highest.e0_three,
    F.highest_V_eq]
  ring

private theorem highest_weight_right
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) :
    HC4.Polynomial.ordinaryDegree4 F.highest.e0 =
      (F.V + 1) * F.highest.n + 1 := by
  simp [HC4.Polynomial.ordinaryDegree4,
    F.highest.e0_zero, F.highest.e0_one,
    F.highest.e0_two, F.highest.e0_three,
    F.highest_V_eq]
  ring

/-- The primitive highest pair is strictly below the locked top degree in the
left non-unit orientation. -/
theorem QsOtherFacetPrLeftVContactFrontierData.highest_n_lt_locked_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.highest.n < F.locked.ell + 1 := by
  have hbound := R.source_weight_le F.highest.e0_provenance.source_mem
  rw [F.highest.e0_zero, Nat.mul_zero, add_zero, highest_weight_left F] at hbound
  rw [F.topFace_degree_eq] at hbound
  have hnle : F.highest.n ≤ F.locked.ell + 1 :=
    le_from_scaled_degree_bound F.V F.highest.n (F.locked.ell + 1) hbound
  apply lt_of_le_of_ne hnle
  intro heq
  have hq :
      qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V F.highest.e0 = 0 := by
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
  omega

/-- Swapped non-unit orientation: the same strict source/contact separation. -/
theorem QsOtherFacetPrRightVContactFrontierData.highest_n_lt_locked_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.highest.n < F.locked.ell + 1 := by
  have hbound := R.source_weight_le F.highest.e0_provenance.source_mem
  rw [F.highest.e0_zero, Nat.mul_zero, add_zero, highest_weight_right F] at hbound
  rw [F.topFace_degree_eq] at hbound
  have hnle : F.highest.n ≤ F.locked.ell + 1 :=
    le_from_scaled_degree_bound F.V F.highest.n (F.locked.ell + 1) hbound
  apply lt_of_le_of_ne hnle
  intro heq
  have hq :
      qsOtherFacetPrQuotientContactOrder (T := T) F.V 1 F.highest.e0 = 0 := by
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
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
