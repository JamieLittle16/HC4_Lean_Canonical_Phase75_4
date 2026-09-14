import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryLayerBridge
import HC4.Valuation.ParameterRamification
import Mathlib.Tactic

/-!
# A19 stationary ramification of the singular planar-contact Rees

The honest planar-contact Rees is indexed by the integral contact order `q`.
The stationary staircase is indexed by pair-depth

    m = n - (e₀ + e₁),

and the already-verified contact interpolation gives

    (n-1) q = D - r m,

with `D = stationaryTotalDegree` and `r = stationaryWeight`.

This module performs exactly that denominator-clearing ramification on the
actual source family.  No new clock or support is introduced: parameter
ramification is ordinary base change `tau |-> tau^(n-1)`, so source Hessian
singularity is preserved by the existing covariance theorem.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The honest contact family after the denominator-clearing ramification
`tau |-> tau^(n-1)`. -/
noncomputable def stationaryRamifiedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  parameterRamificationFamily (K := K) (F.highest.n - 1) D.family

/-- Ramification preserves the global source Hessian singularity exactly. -/
theorem stationaryRamifiedFamily_hessianDeterminant_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    HC4.Polynomial.hessianDeterminant D.stationaryRamifiedFamily = 0 := by
  unfold stationaryRamifiedFamily
  rw [hessianDeterminant_parameterRamificationFamily]
  simp [D.hessian_zero]

/-- Source-wide stationary order formula.  This is the monomial form of the
exact-layer theorem `stationary_scaledOrder_eq`, avoiding any choice of a
layer package at later coefficient extractions. -/
theorem stationary_scaledOrder_eq_of_carrier_mem
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
    (F.highest.n - 1) *
        (T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e) =
      F.stationaryTotalDegree -
        F.stationaryWeight * (F.highest.n - (e 0 + e 1)) := by
  let q := T.topFace.degree -
    Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e
  have heq : e ∈ (familyParameterLayer D.family q).support := by
    simpa [q] using D.parameterLayer_mem_of_carrier_mem he
  have hinterp := D.parameterLayer_contactOrder_interpolation
    hthree houtThree heq
  change (F.highest.n - 1) * q =
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((e 0 + e 1) - 1) at hinterp
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
  have hcontact :
      (F.highest.n - 1) * q =
        F.stationaryWeight * ((e 0 + e 1) - 1) := by
    simpa [QsOtherFacetPrLeftVContactFrontierData.stationaryWeight] using hinterp
  change (F.highest.n - 1) * q = _
  calc
    (F.highest.n - 1) * q =
        F.stationaryWeight * ((e 0 + e 1) - 1) := hcontact
    _ = F.stationaryTotalDegree -
        F.stationaryWeight * (F.highest.n - (e 0 + e 1)) := by
      unfold QsOtherFacetPrLeftVContactFrontierData.stationaryTotalDegree
      rw [hmul]
      simp

/-- Every actual source coefficient of the ramified family is a *single*
parameter monomial at the exact stationary weighted order. -/
theorem coeff_stationaryRamifiedFamily_of_carrier_mem
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
    MvPolynomial.coeff e D.stationaryRamifiedFamily =
      Polynomial.X ^
          (F.stationaryTotalDegree -
            F.stationaryWeight * (F.highest.n - (e 0 + e 1))) *
        Polynomial.C (MvPolynomial.coeff e P.carrier) := by
  unfold stationaryRamifiedFamily parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  unfold QsOtherFacetPrLeftVPlanarContactReesData.family
  rw [reverseWeightedReesFamily_coeff]
  rw [if_pos he]
  rw [map_mul, parameterRamificationHom_X_pow]
  rw [parameterRamificationHom_apply]
  simp
  rw [D.stationary_scaledOrder_eq_of_carrier_mem hthree houtThree he]

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
