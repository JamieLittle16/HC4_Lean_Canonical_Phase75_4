import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileEndpoints
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# A19 stationary profile rigidity adapter for the non-unit PR branch

The source-honest stationary profile already has the two endpoint coefficients
needed by the generic finite staircase theorem.  This file records the last
purely algebraic adapter:

* the outer stationary profile has exact degree `highest.n - 1`;
* after embedding its polynomial coefficients in their fraction field, degree
  and the nonzero constant endpoint are preserved;
* a zero stationary staircase residual therefore forces degree at most one;
* since `highest.n >= 2`, this gives `highest.n = 2`;
* the existing exhaustive staircase bounds then leave no strict interior pair
  degree.

Thus the remaining geometric task is exactly to produce the displayed
stationary residual.  No determinant implication is assumed here, and no
auxiliary clock is identified with the zero blocker.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVContactFrontierData

/-- The source-honest stationary profile has exact outer degree `n-1`: the
locked endpoint supplies the top nonzero coefficient and positivity of every
carrier pair degree supplies the matching upper bound. -/
theorem stationaryCarrierProfile_natDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryCarrierProfile.natDegree = F.highest.n - 1 := by
  apply le_antisymm
  · exact F.natDegree_stationaryCarrierProfile_le hthree houtThree
  · exact Polynomial.le_natDegree_of_ne_zero
      (F.stationaryCarrierProfile_coeff_top_ne_zero hthree houtThree)

/-- Embed the inner coefficient polynomial into its fraction field.  This is
only the coefficient-field enlargement required by the generic staircase
rigidity theorem; the outer stationary index is unchanged. -/
noncomputable def stationaryCarrierProfileFraction
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (FractionRing (Polynomial K)) :=
  F.stationaryCarrierProfile.map
    (algebraMap (Polynomial K) (FractionRing (Polynomial K)))

/-- The fraction-field embedding preserves the exact stationary degree. -/
theorem stationaryCarrierProfileFraction_natDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryCarrierProfileFraction.natDegree = F.highest.n - 1 := by
  let ι : Polynomial K →+* FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  unfold stationaryCarrierProfileFraction
  rw [Polynomial.natDegree_map_eq_of_injective hι]
  exact F.stationaryCarrierProfile_natDegree_eq hthree houtThree

/-- The primitive highest endpoint remains a nonzero constant coefficient
inside the fraction field. -/
theorem stationaryCarrierProfileFraction_coeff_zero_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryCarrierProfileFraction.coeff 0 ≠ 0 := by
  let ι : Polynomial K →+* FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have h0 := F.stationaryCarrierProfile_coeff_zero_ne_zero hthree houtThree
  intro hz
  apply h0
  apply hι
  simpa [stationaryCarrierProfileFraction, ι] using hz

/-- **Stationary residual closes the strict-interior branch.**

This is the exact consumer requested by the final-sprint handoff.  Once the
source-honest Schur/profile algebra supplies the stationary residual, generic
staircase rigidity gives outer degree at most one.  The two retained endpoint
coefficients make that degree exactly `highest.n - 1`, hence `highest.n = 2`,
and the already-proved staircase classification leaves only pair degrees one
and two. -/
theorem noStrictInteriorSupport_of_stationaryResidual
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hres :
      binaryStaircaseProfileResidual
        F.stationaryTotalDegree F.stationaryWeight
        F.stationaryCarrierProfileFraction = 0) :
    F.NoStrictInteriorSupport := by
  have hdeg := F.stationaryCarrierProfileFraction_natDegree_eq
    hthree houtThree
  have hsupport :
      F.stationaryCarrierProfileFraction.natDegree * F.stationaryWeight ≤
        F.stationaryTotalDegree := by
    rw [hdeg]
    unfold stationaryTotalDegree
    simpa [Nat.mul_comm]
  have hrigid : F.stationaryCarrierProfileFraction.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      F.stationaryTotalDegree F.stationaryWeight
      (F.two_le_stationaryWeight hthree houtThree)
      F.stationaryCarrierProfileFraction
      (F.stationaryCarrierProfileFraction_coeff_zero_ne_zero
        hthree houtThree)
      hsupport hres
  rw [hdeg] at hrigid
  have hn : F.highest.n = 2 := by
    have htwo := F.highest.n_two_le
    omega
  intro e he
  have hpos := F.support_pair_pos hthree houtThree he
  rcases F.support_staircase_classification hthree houtThree he with
    ⟨j, hj, hle, hjle, hzero, hlocked⟩
  rw [hn]
  omega

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
