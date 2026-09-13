import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseContactOrder
import HC4.Valuation.SingularBoundedReverseWeightedRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactRees
import Mathlib.Tactic

/-!
# A19 singular contact Rees of the non-unit planar carrier

The represented determinant-one source has its own contact Rees.  For the
remaining carrier classification we instead apply the *same integral contact
weight* to the already-singular planar carrier `P.carrier` itself.

This is a distinct auxiliary family and no clock is identified with the zero
blocker.  Its advantages are exactly the ones needed for the strict-interior
problem:

* every planar-carrier monomial satisfies the inherited source contact bound;
* the highest primitive pair occurs at a strictly positive parameter order;
* because `P.carrier` has identically zero Hessian determinant, the whole
  bounded reverse-Rees family also has identically zero Hessian determinant.

Thus the least positive actual layer of this family is a canonical first
staircase departure from the locked fibre.
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

/-- Source-independent data of the singular reverse Rees attached to the
actual left-oriented planar carrier. -/
structure QsOtherFacetPrLeftVPlanarContactReesData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) where
  bound : HasReverseWeightBound
    (qsIntegralContactWeight (F.V + 1)) T.topFace.degree P.carrier
  hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (reverseWeightedReesFamily
        (qsIntegralContactWeight (F.V + 1)) T.topFace.degree
        P.carrier bound) = 0
  hasPositiveLayer :
    HasPositiveActualParameterLayer
      (reverseWeightedReesFamily
        (qsIntegralContactWeight (F.V + 1)) T.topFace.degree
        P.carrier bound)

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The actual singular planar-contact family. -/
noncomputable def family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    (qsIntegralContactWeight (F.V + 1)) T.topFace.degree P.carrier D.bound

/-- The highest primitive pair occurs at this explicit positive order. -/
def highestOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (_D : QsOtherFacetPrLeftVPlanarContactReesData F) : ℕ :=
  (F.V + 1) * (F.locked.ell + 1 - F.highest.n)

end QsOtherFacetPrLeftVPlanarContactReesData

/-- **Singular planar-contact Rees package.** -/
theorem QsOtherFacetPrLeftVContactFrontierData.planarContactRees
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrLeftVPlanarContactReesData F) := by
  have hgap := F.quotient.contactGap_eq_sum R hthree houtThree
  have hbound : HasReverseWeightBound
      (qsIntegralContactWeight (F.V + 1)) T.topFace.degree P.carrier := by
    intro e he
    rw [qsIntegralContactWeight_finsupp]
    have hs := R.source_weight_le (P.support_source he)
    rw [hgap] at hs
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs
  let Q := reverseWeightedReesFamily
    (qsIntegralContactWeight (F.V + 1)) T.topFace.degree P.carrier hbound
  have hzero : HC4.Polynomial.hessianDeterminant Q = 0 := by
    dsimp [Q]
    exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
      (K := K) (qsIntegralContactWeight (F.V + 1))
      T.topFace.degree P.carrier hbound P.hessian_zero
  have hsep := F.highest_n_lt_locked_height hthree houtThree
  have hqpos :
      0 < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) := by
    have hV : 0 < F.V + 1 := by omega
    have hdiff : 0 < F.locked.ell + 1 - F.highest.n := by omega
    exact Nat.mul_pos hV hdiff
  let q : ℕ := (F.V + 1) * (F.locked.ell + 1 - F.highest.n)
  have hweightHighest :
      T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) F.highest.e0 = q := by
    rw [qsIntegralContactWeight_finsupp]
    rw [F.highest.e0_zero, Nat.mul_zero, add_zero]
    have hdeg : HC4.Polynomial.ordinaryDegree4 F.highest.e0 =
        (F.V + 1) * F.highest.n + 1 := by
      simp [HC4.Polynomial.ordinaryDegree4,
        F.highest.e0_zero, F.highest.e0_one,
        F.highest.e0_two, F.highest.e0_three,
        F.highest_V_eq]
      ring
    rw [hdeg, F.topFace_degree_eq]
    dsimp [q]
    have hcancel :
        ((F.V + 1) * (F.locked.ell + 1) + 1) -
            ((F.V + 1) * F.highest.n + 1) =
          (F.V + 1) * (F.locked.ell + 1) -
            (F.V + 1) * F.highest.n := by
      omega
    rw [hcancel]
    exact (Nat.mul_sub_left_distrib
      (F.V + 1) (F.locked.ell + 1) F.highest.n).symm
  have hfamilyCoeff :
      MvPolynomial.coeff F.highest.e0 Q =
        Polynomial.X ^ q * Polynomial.C
          (MvPolynomial.coeff F.highest.e0 P.carrier) := by
    dsimp [Q]
    rw [reverseWeightedReesFamily_coeff]
    rw [if_pos F.highest.e0_provenance.carrier_mem]
    rw [hweightHighest]
  have hfamilyCoeffNe : MvPolynomial.coeff F.highest.e0 Q ≠ 0 := by
    rw [hfamilyCoeff]
    exact mul_ne_zero
      (pow_ne_zero q Polynomial.X_ne_zero)
      (Polynomial.C_ne_zero.mpr F.highest.e0_provenance.carrier_coeff_ne)
  have heSupport : F.highest.e0 ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr hfamilyCoeffNe
  have heCoeffQ :
      (MvPolynomial.coeff F.highest.e0 Q).coeff q ≠ 0 := by
    rw [hfamilyCoeff]
    simp [F.highest.e0_provenance.carrier_coeff_ne]
  have hqMem : q ∈ familyParameterLayerOrders Q :=
    (mem_familyParameterLayerOrders_iff Q q).2
      ⟨F.highest.e0, heSupport, heCoeffQ⟩
  have hpositive : HasPositiveActualParameterLayer Q := by
    refine ⟨q, Finset.mem_filter.mpr ⟨hqMem, ?_⟩⟩
    simpa [q] using hqpos
  exact ⟨{
    bound := hbound
    hessian_zero := by simpa [Q] using hzero
    hasPositiveLayer := by simpa [Q] using hpositive
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
