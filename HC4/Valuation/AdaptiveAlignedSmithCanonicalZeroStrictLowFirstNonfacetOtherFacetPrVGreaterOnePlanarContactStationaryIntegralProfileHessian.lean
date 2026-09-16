import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileHessianClosure
import HC4.Polynomial.AutonomousODEReconstruction
import Mathlib.Tactic

/-!
# A19 canonical integral stationary profile Hessian

The source-honest stationary profile has coefficient ring `Polynomial K`, so
before localization its Hessian block lives over the integral domain
`Polynomial K`.  This module packages the three canonical Euler-normalised
entries directly over that ring and proves the exact coefficient formulas
consumed by `impossible_of_stationary_coeffwise_hessian`.

After this file, the live left-`V > 1` geometric obligation is a single
identity: the determinant of this canonical integral block is zero.
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

/-- Falling second Euler operator on the integral stationary profile. -/
noncomputable def stationaryIntegralProfileSecondEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (Polynomial K) :=
  eulerDerivative (eulerDerivative F.stationaryCarrierProfile) -
    eulerDerivative F.stationaryCarrierProfile

@[simp] theorem coeff_stationaryIntegralProfileSecondEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (m : ℕ) :
    F.stationaryIntegralProfileSecondEuler.coeff m =
      (m : Polynomial K) * ((m : Polynomial K) - 1) *
        F.stationaryCarrierProfile.coeff m := by
  unfold stationaryIntegralProfileSecondEuler
  simp only [Polynomial.coeff_sub, coeff_eulerDerivative]
  ring

/-- Integral parameter/parameter stationary Hessian entry. -/
noncomputable def stationaryIntegralProfileHessian00
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (Polynomial K) :=
  Polynomial.C
      ((F.stationaryTotalDegree : Polynomial K) *
        ((F.stationaryTotalDegree : Polynomial K) - 1)) *
      F.stationaryCarrierProfile +
    Polynomial.C
      ((F.stationaryWeight : Polynomial K) *
        ((F.stationaryWeight : Polynomial K) -
          2 * (F.stationaryTotalDegree : Polynomial K) + 1)) *
      eulerDerivative F.stationaryCarrierProfile +
    Polynomial.C ((F.stationaryWeight : Polynomial K) ^ 2) *
      F.stationaryIntegralProfileSecondEuler

/-- Integral mixed stationary Hessian entry. -/
noncomputable def stationaryIntegralProfileHessian01
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (Polynomial K) :=
  Polynomial.C
      ((F.stationaryTotalDegree : Polynomial K) -
        (F.stationaryWeight : Polynomial K)) *
      eulerDerivative F.stationaryCarrierProfile -
    Polynomial.C (F.stationaryWeight : Polynomial K) *
      F.stationaryIntegralProfileSecondEuler

/-- Integral depth/depth stationary Hessian entry. -/
noncomputable def stationaryIntegralProfileHessian11
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (Polynomial K) :=
  F.stationaryIntegralProfileSecondEuler

@[simp] theorem coeff_stationaryIntegralProfileHessian00
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (m : ℕ) :
    F.stationaryIntegralProfileHessian00.coeff m =
      (((F.stationaryTotalDegree : Polynomial K) -
          (F.stationaryWeight : Polynomial K) * (m : Polynomial K)) *
        ((F.stationaryTotalDegree : Polynomial K) -
          (F.stationaryWeight : Polynomial K) * (m : Polynomial K) - 1)) *
        F.stationaryCarrierProfile.coeff m := by
  unfold stationaryIntegralProfileHessian00
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    coeff_eulerDerivative, coeff_stationaryIntegralProfileSecondEuler]
  ring

@[simp] theorem coeff_stationaryIntegralProfileHessian01
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (m : ℕ) :
    F.stationaryIntegralProfileHessian01.coeff m =
      (m : Polynomial K) *
        ((F.stationaryTotalDegree : Polynomial K) -
          (F.stationaryWeight : Polynomial K) * (m : Polynomial K)) *
        F.stationaryCarrierProfile.coeff m := by
  unfold stationaryIntegralProfileHessian01
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    coeff_eulerDerivative, coeff_stationaryIntegralProfileSecondEuler]
  ring

@[simp] theorem coeff_stationaryIntegralProfileHessian11
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (m : ℕ) :
    F.stationaryIntegralProfileHessian11.coeff m =
      (m : Polynomial K) * ((m : Polynomial K) - 1) *
        F.stationaryCarrierProfile.coeff m := by
  exact F.coeff_stationaryIntegralProfileSecondEuler m

/-- Determinant of the canonical integral stationary Hessian block. -/
noncomputable def stationaryIntegralProfileHessianDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Polynomial (Polynomial K) :=
  F.stationaryIntegralProfileHessian00 *
      F.stationaryIntegralProfileHessian11 -
    F.stationaryIntegralProfileHessian01 *
      F.stationaryIntegralProfileHessian01

/-- **Canonical determinant closes the left non-unit branch.** -/
theorem impossible_of_stationaryIntegralProfileHessianDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hdet : F.stationaryIntegralProfileHessianDet = 0) : False := by
  apply F.impossible_of_stationary_coeffwise_hessian
    hthree houtThree
    F.stationaryIntegralProfileHessian00
    F.stationaryIntegralProfileHessian01
    F.stationaryIntegralProfileHessian11
  · exact F.coeff_stationaryIntegralProfileHessian00
  · exact F.coeff_stationaryIntegralProfileHessian01
  · exact F.coeff_stationaryIntegralProfileHessian11
  · simpa [stationaryIntegralProfileHessianDet] using hdet

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
