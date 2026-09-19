import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryActivePivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import HC4.Polynomial.LogarithmicInitialSlope
import Mathlib.Tactic

/-!
# A19 stationary weighted-Euler bridge for the ramified planar contact family

After the denominator-clearing ramification, every actual source monomial at
pair degree `k = e₀+e₁` occurs at the exact stationary parameter order

    q = D - r(n-k) = r(k-1).

Consequently

    q + r = r(e₀+e₁).

This is the source-honest weighted Euler equation relating the ramified family
parameter to the two complementary `.pr` source directions.  It is the exact
identity needed to straighten the complementary Hessian block before taking
the active `(2,3)` Schur quotient.

No localization, new clock, or degree hypothesis is introduced.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The stationary exponent of a source monomial is exactly `r(k-1)`, where
`k=e₀+e₁` is its pair degree. -/
theorem stationary_order_eq_weight_mul_pair_pred
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    F.stationaryTotalDegree -
        F.stationaryWeight * (F.highest.n - (e 0 + e 1)) =
      F.stationaryWeight * ((e 0 + e 1) - 1) := by
  have hkpos : 1 ≤ e 0 + e 1 := by
    have h := F.support_pair_pos hthree houtThree he
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using h
  have hkle : e 0 + e 1 ≤ F.highest.n := by
    rcases F.support_staircase_classification hthree houtThree he with
      ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hk
  have hdecomp :
      F.highest.n - 1 =
        (F.highest.n - (e 0 + e 1)) + ((e 0 + e 1) - 1) := by
    omega
  have hmul :
      F.stationaryWeight * (F.highest.n - 1) =
        F.stationaryWeight * (F.highest.n - (e 0 + e 1)) +
          F.stationaryWeight * ((e 0 + e 1) - 1) := by
    rw [hdecomp, Nat.mul_add]
  unfold QsOtherFacetPrLeftVContactFrontierData.stationaryTotalDegree
  rw [hmul]
  simp

/-- Adding one stationary weight to the exact parameter order gives the
weighted pair degree.  This is the scalar Euler relation used below. -/
theorem stationary_order_add_weight_eq_weight_mul_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    (F.stationaryTotalDegree -
        F.stationaryWeight * (F.highest.n - (e 0 + e 1))) +
      F.stationaryWeight =
        F.stationaryWeight * (e 0 + e 1) := by
  rw [D.stationary_order_eq_weight_mul_pair_pred hthree houtThree he]
  have hkpos : 1 ≤ e 0 + e 1 := by
    have h := F.support_pair_pos hthree houtThree he
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using h
  calc
    F.stationaryWeight * ((e 0 + e 1) - 1) + F.stationaryWeight =
        F.stationaryWeight * (((e 0 + e 1) - 1) + 1) := by
          rw [Nat.mul_add]
          simp
    _ = F.stationaryWeight * (e 0 + e 1) := by
      rw [Nat.sub_add_cancel hkpos]

/-- **Stationary weighted Euler equation.**  On the ramified singular contact
family, parameter Euler plus one stationary weight equals stationary weight
times the sum of the two complementary `.pr` source Euler directions:

`Eτ Q + r Q = r E₀ Q + r E₁ Q`.

The proof is coefficientwise on the literal source family and uses the exact
stationary ramification exponent; no reconstructed support is used. -/
theorem stationaryRamifiedFamily_weightedEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterEuler D.stationaryRamifiedFamily +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          HC4.Polynomial.mvEuler (0 : Fin 4) D.stationaryRamifiedFamily +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          HC4.Polynomial.mvEuler (1 : Fin 4) D.stationaryRamifiedFamily := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_mvEuler]
  by_cases he : e ∈ P.carrier.support
  · let q := F.stationaryTotalDegree -
      F.stationaryWeight * (F.highest.n - (e 0 + e 1))
    have hcoeff := D.coeff_stationaryRamifiedFamily_of_carrier_mem
      hthree houtThree he
    have hcoeffq :
        MvPolynomial.coeff e D.stationaryRamifiedFamily =
          Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier) := by
      simpa [q] using hcoeff
    rw [hcoeffq]
    have hEuler := HC4.Polynomial.eulerDerivative_X_pow_mul
      (Polynomial.C (MvPolynomial.coeff e P.carrier)) q
    have hparam :
        Polynomial.X * Polynomial.derivative
            (Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier)) =
          Polynomial.X ^ q *
            (Polynomial.C (q : K) *
                Polynomial.C (MvPolynomial.coeff e P.carrier)) := by
      simpa [HC4.Polynomial.eulerDerivative] using hEuler
    rw [hparam]
    have hnat := D.stationary_order_add_weight_eq_weight_mul_pair
      hthree houtThree he
    have hq : q + F.stationaryWeight =
        F.stationaryWeight * (e 0 + e 1) := by
      simpa [q] using hnat
    have hK :
        (q : K) + (F.stationaryWeight : K) =
          (F.stationaryWeight : K) * ((e 0 : K) + (e 1 : K)) := by
      exact_mod_cast hq
    have hP := congrArg Polynomial.C hK
    simp only [map_add, map_mul, map_natCast] at hP ⊢
    linear_combination
      (Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier)) * hP
  · have hcoeff0 :
        MvPolynomial.coeff e D.stationaryRamifiedFamily = 0 := by
      unfold stationaryRamifiedFamily parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      unfold QsOtherFacetPrLeftVPlanarContactReesData.family
      rw [reverseWeightedReesFamily_coeff]
      rw [if_neg he]
      simp
    rw [hcoeff0]
    simp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
