import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseContactOrder
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitNoInteriorSupport
import HC4.Valuation.SingularBoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# A19 singular locked-side contact Rees for the unit PR carrier

This is the `V = 1` specialization of the source-honest planar contact Rees
used in the non-unit finite staircase.  It applies the same integral source
contact weight to the already singular planar carrier, without identifying
this auxiliary parameter with the zero blocker.
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

structure QsOtherFacetPrUnitLeftPlanarContactReesData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) where
  bound : HasReverseWeightBound
    (qsIntegralContactWeight 2) T.topFace.degree P.carrier
  hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (reverseWeightedReesFamily
        (qsIntegralContactWeight 2) T.topFace.degree P.carrier bound) = 0
  hasPositiveLayer :
    HasPositiveActualParameterLayer
      (reverseWeightedReesFamily
        (qsIntegralContactWeight 2) T.topFace.degree P.carrier bound)

namespace QsOtherFacetPrUnitLeftPlanarContactReesData

/-- Namespace-local compatibility alias used by the unit first-interior layer. -/
abbrev rankThreeQuotientCoordinate
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) :
    HC4.Polynomial.RankThreeQuotientCoordinate :=
  HC4.Polynomial.rankThreeQuotientCoordinate alpha beta e

noncomputable def family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    (qsIntegralContactWeight 2) T.topFace.degree P.carrier D.bound

def highestOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (_D : QsOtherFacetPrUnitLeftPlanarContactReesData F) : ℕ :=
  2 * (F.locked.ell + 1 - F.highest.n)

end QsOtherFacetPrUnitLeftPlanarContactReesData

/-- The singular unit planar carrier admits the honest locked-side contact Rees
and the primitive highest endpoint supplies a positive actual layer. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.planarContactRees
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrUnitLeftPlanarContactReesData F) := by
  have hgap := F.quotient.contactGap_eq_sum R hthree houtThree
  have hbound : HasReverseWeightBound
      (qsIntegralContactWeight 2) T.topFace.degree P.carrier := by
    intro e he
    rw [qsIntegralContactWeight_finsupp]
    have hs := R.source_weight_le (P.support_source he)
    rw [hgap] at hs
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs
  let Q := reverseWeightedReesFamily
    (qsIntegralContactWeight 2) T.topFace.degree P.carrier hbound
  have hzero : HC4.Polynomial.hessianDeterminant Q = 0 := by
    dsimp [Q]
    exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
      (K := K) (qsIntegralContactWeight 2)
      T.topFace.degree P.carrier hbound P.hessian_zero
  have hsep := F.highest_n_lt_locked_height hthree houtThree
  let q : ℕ := 2 * (F.locked.ell + 1 - F.highest.n)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.mul_pos (by omega) (by omega)
  have hweightHighest :
      T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight 2) F.highest.e0 = q := by
    rw [qsIntegralContactWeight_finsupp]
    rw [F.highest.e0_zero, Nat.mul_zero, add_zero]
    have hdeg : HC4.Polynomial.ordinaryDegree4 F.highest.e0 =
        2 * F.highest.n + 1 := by
      simp [HC4.Polynomial.ordinaryDegree4,
        F.highest.e0_zero, F.highest.e0_one,
        F.highest.e0_two, F.highest.e0_three,
        F.highest_V_eq_one]
      ring
    rw [hdeg, F.topFace_degree_eq]
    dsimp [q]
    omega
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
  have heCoeffQ : (MvPolynomial.coeff F.highest.e0 Q).coeff q ≠ 0 := by
    rw [hfamilyCoeff]
    simp [F.highest.e0_provenance.carrier_coeff_ne]
  have hqMem : q ∈ familyParameterLayerOrders Q :=
    (mem_familyParameterLayerOrders_iff Q q).2
      ⟨F.highest.e0, heSupport, heCoeffQ⟩
  have hpositive : HasPositiveActualParameterLayer Q := by
    refine ⟨q, Finset.mem_filter.mpr ⟨hqMem, ?_⟩⟩
    exact hqpos
  exact ⟨{
    bound := hbound
    hessian_zero := by simpa [Q] using hzero
    hasPositiveLayer := by simpa [Q] using hpositive
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation