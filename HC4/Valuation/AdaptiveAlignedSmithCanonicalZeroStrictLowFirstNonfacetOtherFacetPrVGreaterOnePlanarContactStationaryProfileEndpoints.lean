import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfile
import Mathlib.Tactic

/-!
# A19 source-honest endpoints of the stationary planar profile

The outer stationary profile keeps the literal source coefficient of every
carrier monomial at the pair-distance index `n-(e₀+e₁)` and the inner index
`e₀`.  The quotient-fibre injectivity already proved for the planar carrier
shows that no distinct source monomial can collide at both indices.

Consequently the primitive highest endpoint gives a nonzero outer constant
coefficient, while the locked endpoint gives a nonzero coefficient at outer
degree `n-1`.  These are exactly the endpoint hypotheses needed by the finite
stationary staircase rigidity theorem.
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

/-- The nested stationary profile preserves the literal coefficient of every
actual carrier monomial at its two canonical indices. -/
theorem coeff_coeff_stationaryCarrierProfile_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.stationaryCarrierProfile.coeff
        (F.highest.n - (e 0 + e 1))).coeff (e 0) =
      MvPolynomial.coeff e P.carrier := by
  classical
  rw [F.coeff_stationaryCarrierProfile, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d hd hde
    by_cases horder :
        F.highest.n - (d 0 + d 1) = F.highest.n - (e 0 + e 1)
    · have hdle : d 0 + d 1 ≤ F.highest.n := by
        rcases F.support_staircase_classification hthree houtThree hd with
          ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
        simpa [rankThreeQuotientCoordinate] using hk
      have hele : e 0 + e 1 ≤ F.highest.n := by
        rcases F.support_staircase_classification hthree houtThree he with
          ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
        simpa [rankThreeQuotientCoordinate] using hk
      have hpair : d 0 + d 1 = e 0 + e 1 := by omega
      by_cases hzero : d 0 = e 0
      · have hpairZ :
          qsOtherFacetPairDegree .pr d = qsOtherFacetPairDegree .pr e := by
          simp [qsOtherFacetPairDegree, hpair]
        have hq :
            rankThreeQuotientCoordinate 1 F.V d =
              rankThreeQuotientCoordinate 1 F.V e :=
          F.quotient.pair_fiber hd he hpairZ
        have hEq : d = e :=
          eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 F.V d e hq hzero
        exact (hde hEq).elim
      · simp [horder, Polynomial.coeff_monomial, hzero]
    · simp [horder]
  · exact he

/-- The primitive highest pair survives as a nonzero constant coefficient of
the outer stationary profile. -/
theorem stationaryCarrierProfile_coeff_zero_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryCarrierProfile.coeff 0 ≠ 0 := by
  have hcoeff := F.coeff_coeff_stationaryCarrierProfile_of_mem
    hthree houtThree F.highest.e0_provenance.carrier_mem
  simp [F.highest.e0_zero, F.highest.e0_one] at hcoeff
  intro hz
  have hz0 := congrArg (fun p : Polynomial K => p.coeff 0) hz
  rw [hcoeff] at hz0
  exact F.highest.e0_provenance.carrier_coeff_ne hz0

/-- The locked pair survives at the opposite endpoint `n-1` of the outer
stationary staircase. -/
theorem stationaryCarrierProfile_coeff_top_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryCarrierProfile.coeff (F.highest.n - 1) ≠ 0 := by
  have hcoeff := F.coeff_coeff_stationaryCarrierProfile_of_mem
    hthree houtThree F.locked.facet_provenance.carrier_mem
  simp [F.locked.facet_zero, F.locked.facet_one] at hcoeff
  intro hz
  have hz0 := congrArg (fun p : Polynomial K => p.coeff 0) hz
  rw [hcoeff] at hz0
  exact F.locked.facet_provenance.carrier_coeff_ne hz0

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
