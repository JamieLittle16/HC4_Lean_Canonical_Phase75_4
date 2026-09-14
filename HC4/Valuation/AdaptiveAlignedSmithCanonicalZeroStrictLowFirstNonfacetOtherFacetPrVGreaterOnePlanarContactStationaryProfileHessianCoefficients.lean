import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileHessianFamily
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryRamification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import Mathlib.Tactic

/-!
# A19 stationary profile-Hessian source coefficients

The stationary ramified family is source-honest: every carrier monomial has a
single parameter coefficient at the exact stationary order.  This module
records the resulting coefficient formulas for the three family-level
stationary Hessian entries.

No determinant, Schur, degree, or rigidity conclusion is used here.  These
lemmas are representation plumbing for the final coefficient extraction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem stationaryParameterEuler_X_pow_mul_C
    (q : ℕ) (a : K) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a) =
      Polynomial.C (q : K) *
        ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a) := by
  cases q with
  | zero => simp
  | succ q =>
      rw [Polynomial.derivative_mul, Polynomial.derivative_C]
      simp only [mul_zero, add_zero]
      rw [Polynomial.derivative_X_pow_succ]
      rw [pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

private theorem stationaryParameterEuler_C_mul_X_pow_mul_C
    (m : K) (q : ℕ) (a : K) :
    Polynomial.X * Polynomial.derivative
        (Polynomial.C m *
          ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a)) =
      Polynomial.C (q : K) * Polynomial.C m *
        ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a) := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_C]
  simp only [zero_mul, zero_add]
  calc
    Polynomial.X *
          (Polynomial.C m * Polynomial.derivative
            ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a)) =
        Polynomial.C m *
          (Polynomial.X * Polynomial.derivative
            ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a)) := by
      ring
    _ = Polynomial.C m *
          (Polynomial.C (q : K) *
            ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a)) := by
      rw [stationaryParameterEuler_X_pow_mul_C]
    _ = Polynomial.C (q : K) * Polynomial.C m *
          ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a) := by
      ring

private theorem stationaryParameterSecondEuler_X_pow_mul_C
    (q : ℕ) (a : K) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a)) =
      Polynomial.C ((q : K) * ((q : K) - 1)) *
        ((Polynomial.X : Polynomial K) ^ q * Polynomial.C a) := by
  let p : Polynomial K :=
    (Polynomial.X : Polynomial K) ^ q * Polynomial.C a
  have hEuler :
      Polynomial.X * Polynomial.derivative p =
        Polynomial.C (q : K) * p := by
    simpa [p] using stationaryParameterEuler_X_pow_mul_C q a
  have hDeriv := congrArg Polynomial.derivative hEuler
  have hDeriv' :
      Polynomial.derivative p +
          Polynomial.X * Polynomial.derivative (Polynomial.derivative p) =
        Polynomial.C (q : K) * Polynomial.derivative p := by
    simpa [Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_C] using hDeriv
  have hSecond :
      Polynomial.X * Polynomial.derivative (Polynomial.derivative p) =
        (Polynomial.C (q : K) - 1) * Polynomial.derivative p := by
    linear_combination hDeriv'
  change Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative p) =
    Polynomial.C ((q : K) * ((q : K) - 1)) * p
  calc
    Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative p) =
        Polynomial.X *
          (Polynomial.X * Polynomial.derivative (Polynomial.derivative p)) := by
      ring
    _ = Polynomial.X *
          ((Polynomial.C (q : K) - 1) * Polynomial.derivative p) := by
      rw [hSecond]
    _ = (Polynomial.C (q : K) - 1) *
          (Polynomial.X * Polynomial.derivative p) := by
      ring
    _ = (Polynomial.C (q : K) - 1) *
          (Polynomial.C (q : K) * p) := by
      rw [hEuler]
    _ = Polynomial.C ((q : K) * ((q : K) - 1)) * p := by
      rw [Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_1]
      ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- Exact source coefficient of the stationary parameter/parameter Hessian
entry. -/
theorem stationaryProfileHessian00Family_coeff_of_carrier_mem
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
    let q := F.stationaryTotalDegree -
      F.stationaryWeight * (F.highest.n - (e 0 + e 1))
    MvPolynomial.coeff e D.stationaryProfileHessian00Family =
      Polynomial.C ((q : K) * ((q : K) - 1)) *
        MvPolynomial.coeff e D.stationaryRamifiedFamily := by
  dsimp
  rw [stationaryProfileHessian00Family, coeff_familyParameterSecondEuler]
  rw [D.coeff_stationaryRamifiedFamily_of_carrier_mem hthree houtThree he]
  exact stationaryParameterSecondEuler_X_pow_mul_C _ _

/-- Exact source coefficient of the stationary mixed parameter/depth Hessian
entry, in the source-honest affine depth scalar. -/
theorem stationaryProfileHessian01Family_coeff_of_carrier_mem
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
    let q := F.stationaryTotalDegree -
      F.stationaryWeight * (F.highest.n - (e 0 + e 1))
    MvPolynomial.coeff e D.stationaryProfileHessian01Family =
      Polynomial.C (q : K) *
        Polynomial.C
          ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) *
        MvPolynomial.coeff e D.stationaryRamifiedFamily := by
  dsimp
  rw [stationaryProfileHessian01Family, coeff_familyParameterEuler]
  rw [D.coeff_stationaryDepthEuler]
  rw [D.coeff_stationaryRamifiedFamily_of_carrier_mem hthree houtThree he]
  exact stationaryParameterEuler_C_mul_X_pow_mul_C _ _ _

/-- Exact source coefficient of the stationary depth/depth Hessian entry. -/
theorem stationaryProfileHessian11Family_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (e : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff e D.stationaryProfileHessian11Family =
      Polynomial.C
          ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) *
        (Polynomial.C
            ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) - 1) *
        MvPolynomial.coeff e D.stationaryRamifiedFamily := by
  exact D.coeff_stationaryDepthSecondEuler D.stationaryRamifiedFamily e

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
