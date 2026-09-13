import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileEndpoints
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# A19 stationary rigidity closes strict-interior support

The source-honest outer stationary profile records pair-distance from the
primitive highest slice.  Its constant coefficient is the literal highest
source endpoint, while its coefficient at degree `n-1` is the literal locked
source endpoint.  Hence, after the injective fraction-field map, the profile
has degree exactly `n-1`.

Once the exact stationary residual is known to vanish, the existing finite
staircase rigidity theorem forces this degree to be at most one.  Since the
primitive highest pair has degree at least two, necessarily `n = 2`.  The
already-proved whole-carrier staircase bounds then leave only pair degree one
or pair degree `n`, exactly `NoStrictInteriorSupport`.

This file contains no new determinant argument.  The sole remaining geometric
input is the displayed stationary residual hypothesis.
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

/-- **Stationary residual implies absence of strict-interior carrier support.**

All representation and endpoint facts are source-honest.  The residual is the
only hypothesis not already supplied by the planar-contact carrier package. -/
theorem QsOtherFacetPrLeftVContactFrontierData.noStrictInteriorSupport_of_stationaryResidual
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
          (Polynomial.map
            (algebraMap (Polynomial K) (FractionRing (Polynomial K)))
            F.stationaryCarrierProfile) = 0) :
    F.NoStrictInteriorSupport := by
  let ι : Polynomial K →+* FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K))
  let h : Polynomial (FractionRing (Polynomial K)) :=
    Polynomial.map ι F.stationaryCarrierProfile

  have h0base : F.stationaryCarrierProfile.coeff 0 ≠ 0 :=
    F.stationaryCarrierProfile_coeff_zero_ne_zero hthree houtThree
  have h0 : h.coeff 0 ≠ 0 := by
    intro hz
    apply h0base
    apply IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
    simpa [h, ι] using hz

  have htopbase :
      F.stationaryCarrierProfile.coeff (F.highest.n - 1) ≠ 0 :=
    F.stationaryCarrierProfile_coeff_top_ne_zero hthree houtThree
  have htop : h.coeff (F.highest.n - 1) ≠ 0 := by
    intro hz
    apply htopbase
    apply IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
    simpa [h, ι] using hz

  have hmapDegree :
      h.natDegree = F.stationaryCarrierProfile.natDegree := by
    dsimp [h, ι]
    exact Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)))
      F.stationaryCarrierProfile

  have hdegree : h.natDegree = F.highest.n - 1 := by
    apply Nat.le_antisymm
    · rw [hmapDegree]
      exact F.natDegree_stationaryCarrierProfile_le hthree houtThree
    · exact Polynomial.le_natDegree_of_ne_zero htop

  have hsupport :
      h.natDegree * F.stationaryWeight ≤ F.stationaryTotalDegree := by
    rw [hdegree]
    unfold QsOtherFacetPrLeftVContactFrontierData.stationaryTotalDegree
    exact le_of_eq (Nat.mul_comm _ _)

  have hrigid : h.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      (K := FractionRing (Polynomial K))
      F.stationaryTotalDegree F.stationaryWeight
      (F.two_le_stationaryWeight hthree houtThree)
      h h0 hsupport (by simpa [h, ι] using hres)

  have hn2 : F.highest.n = 2 := by
    rw [hdegree] at hrigid
    have hnlo := F.highest.n_two_le
    omega

  intro e he
  have hpos := F.support_pair_pos hthree houtThree he
  rcases F.support_staircase_classification hthree houtThree he with
    ⟨j, hj, hle, hjle, hzero, hlocked⟩
  have hcases :
      (rankThreeQuotientCoordinate 1 F.V e).pair = 1 ∨
        (rankThreeQuotientCoordinate 1 F.V e).pair = 2 := by
    rw [hn2] at hle
    omega
  rcases hcases with hpair | hpair
  · exact Or.inl hpair
  · exact Or.inr (by simpa [hn2] using hpair)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
