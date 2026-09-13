import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryIndex
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# A19 source-honest stationary profile of the planar carrier

The stationary staircase variable is not the omitted-coordinate line variable.
It records distance from the primitive highest pair:

    m = n - (e₀ + e₁).

For each actual planar-carrier monomial we retain its omitted-coordinate index
`e₀` as an inner polynomial variable.  Thus the whole carrier is encoded by a
single finite nested polynomial

    h : K[T][Z] = Polynomial (Polynomial K),

whose outer coefficient at `Z^m` is the honest affine-line profile on pair
degree `n-m`.

This is representation plumbing only.  In particular no Hessian residual or
degree-one conclusion is asserted here.  The next adapter identifies the
straightened Schur block with the stationary Hessian of this exact profile.
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

/-- The whole left-oriented planar carrier, reindexed from the primitive
highest pair.  The outer variable records `n-pairDegree`; the inner variable
records the actual omitted-coordinate exponent `e₀`. -/
noncomputable def stationaryCarrierProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (Polynomial K) :=
  P.carrier.sum fun e c =>
    Polynomial.monomial
      (F.highest.n - (e 0 + e 1))
      (Polynomial.monomial (e 0) c)

/-- Exact outer-coefficient formula.  No coefficient is recreated: the
stationary profile is the literal finite sum of carrier coefficients grouped
by distance from the highest pair. -/
theorem coeff_stationaryCarrierProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (m : ℕ) :
    F.stationaryCarrierProfile.coeff m =
      ∑ e ∈ P.carrier.support,
        if F.highest.n - (e 0 + e 1) = m then
          Polynomial.monomial (e 0) (MvPolynomial.coeff e P.carrier)
        else 0 := by
  classical
  unfold stationaryCarrierProfile
  rw [MvPolynomial.sum_def, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Polynomial.coeff_monomial]
  split <;> simp_all

/-- The finite stationary profile has no outer support above `n-1`.  This is
an exact consequence of positivity of every actual pair degree, not an added
profile hypothesis. -/
theorem natDegree_stationaryCarrierProfile_le
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryCarrierProfile.natDegree ≤ F.highest.n - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [F.coeff_stationaryCarrierProfile]
  apply Finset.sum_eq_zero
  intro e he
  have hkpos : 1 ≤ e 0 + e 1 := by
    have h := F.support_pair_pos hthree houtThree he
    simpa [rankThreeQuotientCoordinate] using h
  have hkle : e 0 + e 1 ≤ F.highest.n := by
    rcases F.support_staircase_classification hthree houtThree he with
      ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
    simpa [rankThreeQuotientCoordinate] using hk
  have hlt : F.highest.n - (e 0 + e 1) < m := by
    omega
  have hne : F.highest.n - (e 0 + e 1) ≠ m := by omega
  simp [hne]

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
