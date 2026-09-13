import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileEndpoints
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19 stationary residual closes strict-interior support

This is the final arithmetic consumer of the source-honest stationary outer
profile.  Its primitive-highest endpoint is the nonzero constant coefficient,
while the locked endpoint is the nonzero coefficient at outer degree `n-1`.

After mapping the coefficient ring `K[T]` injectively to its fraction field,
the generic stationary staircase rigidity theorem applies verbatim.  A zero
stationary residual forces ordinary degree at most one, but the locked endpoint
forces degree at least `n-1`; since the primitive highest degree already
satisfies `n >= 2`, necessarily `n = 2`.  The exhaustive staircase
classification then leaves only pair degrees `1` and `n`.

Thus the sole remaining geometric input to `NoStrictInteriorSupport` is the
stationary residual itself.
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

namespace QsOtherFacetPrLeftVContactFrontierData

/-- **Stationary closure of the strict-interior branch.**  Once the mapped
outer stationary profile satisfies the existing staircase residual, the
primitive highest pair has degree exactly two and strict-interior support is
impossible. -/
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
        (Polynomial.map
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)))
          F.stationaryCarrierProfile) = 0) :
    F.NoStrictInteriorSupport := by
  let L := FractionRing (Polynomial K)
  let ι : Polynomial K →+* L := algebraMap (Polynomial K) L
  let h : Polynomial L := Polynomial.map ι F.stationaryCarrierProfile
  have hι : Function.Injective ι :=
    IsFractionRing.injective (Polynomial K) L
  have hzero : h.coeff 0 ≠ 0 := by
    rw [h, Polynomial.coeff_map]
    intro hz
    apply F.stationaryCarrierProfile_coeff_zero_ne_zero hthree houtThree
    apply hι
    simpa [ι] using hz
  have htop : h.coeff (F.highest.n - 1) ≠ 0 := by
    rw [h, Polynomial.coeff_map]
    intro hz
    apply F.stationaryCarrierProfile_coeff_top_ne_zero hthree houtThree
    apply hι
    simpa [ι] using hz
  have hdegBase :=
    F.natDegree_stationaryCarrierProfile_le hthree houtThree
  have hdeg : h.natDegree ≤ F.highest.n - 1 := by
    rw [h, Polynomial.natDegree_map_eq_of_injective hι]
    exact hdegBase
  have hsupport : h.natDegree * F.stationaryWeight ≤ F.stationaryTotalDegree := by
    calc
      h.natDegree * F.stationaryWeight ≤
          (F.highest.n - 1) * F.stationaryWeight :=
        Nat.mul_le_mul_right F.stationaryWeight hdeg
      _ = F.stationaryTotalDegree := by
        simp [stationaryTotalDegree, Nat.mul_comm]
  have hres' :
      binaryStaircaseProfileResidual
        F.stationaryTotalDegree F.stationaryWeight h = 0 := by
    simpa [h, ι, L] using hres
  have hdegOne : h.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      (K := L)
      F.stationaryTotalDegree F.stationaryWeight
      (F.two_le_stationaryWeight hthree houtThree)
      h hzero hsupport hres'
  have htopdeg : F.highest.n - 1 ≤ h.natDegree :=
    Polynomial.le_natDegree_of_ne_zero htop
  have hn : F.highest.n = 2 := by
    have hnTwo := F.highest.n_two_le
    omega
  intro e he
  have hkpos := F.support_pair_pos hthree houtThree he
  rcases F.support_staircase_classification hthree houtThree he with
    ⟨j, hj, hkle, hjle, hzeroiff, hlockediff⟩
  rw [hn] at hkle ⊢
  omega

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
