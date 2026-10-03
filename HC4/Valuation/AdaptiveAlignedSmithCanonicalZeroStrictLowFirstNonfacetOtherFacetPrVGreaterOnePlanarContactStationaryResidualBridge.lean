import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryIntegralProfileHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19 stationary integral Hessian / staircase-residual bridge

The canonical integral stationary profile Hessian was deliberately written in
Euler form.  Its determinant is therefore not a new obstruction: it is
literally the generic binary staircase residual already consumed by the
finite-staircase rigidity theorem.

This file records that identity in the coefficient ring `Polynomial K`.  It
introduces no geometric implication from the source Hessian; in particular it
does **not** identify the raw/source Schur determinant with the profile
residual.  The remaining geometric obligation is still to obtain vanishing of
this canonical determinant (or equivalently this residual) by a source-honest
argument.
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

/-- The determinant of the canonical integral stationary profile Hessian is
exactly the generic finite-staircase residual, over the integral coefficient
ring `Polynomial K`.

This is a purely algebraic identity.  It is intentionally separated from the
still-geometric assertion that the determinant vanishes. -/
theorem stationaryIntegralProfileHessianDet_eq_binaryStaircaseProfileResidual
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    F.stationaryIntegralProfileHessianDet =
      binaryStaircaseProfileResidual
        F.stationaryTotalDegree F.stationaryWeight
        F.stationaryCarrierProfile := by
  unfold stationaryIntegralProfileHessianDet
  unfold stationaryIntegralProfileHessian00
  unfold stationaryIntegralProfileHessian01
  unfold stationaryIntegralProfileHessian11
  unfold stationaryIntegralProfileSecondEuler
  unfold binaryStaircaseProfileResidual
  unfold binaryStaircaseProfileSecondEuler
  ring

/-- Equivalent zero form, convenient for the final geometric splice. -/
theorem stationaryIntegralProfileHessianDet_eq_zero_iff_residual_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    F.stationaryIntegralProfileHessianDet = 0 ↔
      binaryStaircaseProfileResidual
        F.stationaryTotalDegree F.stationaryWeight
        F.stationaryCarrierProfile = 0 := by
  rw [F.stationaryIntegralProfileHessianDet_eq_binaryStaircaseProfileResidual]

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
