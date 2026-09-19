import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinaryHomogenization
import HC4.Polynomial.AutonomousODEReconstruction
import Mathlib.Tactic

/-!
# A19 binary Hessian profile of the singular planar carrier

The preceding binary homogenization turns the singular planar-contact family
into the pure weighted two-variable grading

    tau-degree = D - (V + 2) * n,

where `n` is source coordinate `0` and `D = T.topFace.degree`.

This file packages the corresponding symbolic longitudinal profile over the
honest transverse coefficient ring `MvPolynomial (Fin 3) K` and exposes the
three canonical stationary Hessian entries

    H00[n] = (D-rn)(D-rn-1) h[n],
    H01[n] = n(D-rn) h[n],
    H11[n] = n(n-1) h[n],

with `r = V+2`.  These are exactly the coefficient hypotheses consumed by the
existing stationary staircase-profile recognition and rigidity machinery.
No localization and no determinant cancellation occurs in this module.
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

/-- Weighted parameter-Euler operator `(D-rE)h` on the singular planar
carrier's honest longitudinal profile. -/
noncomputable def carrierProfileParameterEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  Polynomial.C (T.topFace.degree : MvPolynomial (Fin 3) K) *
      D.carrierLongitudinalProfile -
    Polynomial.C (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
      eulerDerivative D.carrierLongitudinalProfile

/-- Parameter-parameter entry `(D-rE-1)(D-rE)h`. -/
noncomputable def carrierProfileHessian00
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  Polynomial.C
      ((T.topFace.degree : MvPolynomial (Fin 3) K) - 1) *
      D.carrierProfileParameterEuler -
    Polynomial.C (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
      eulerDerivative D.carrierProfileParameterEuler

/-- Mixed parameter/longitudinal entry `E(D-rE)h`. -/
noncomputable def carrierProfileHessian01
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  eulerDerivative D.carrierProfileParameterEuler

/-- Longitudinal-longitudinal falling Euler entry `(E^2-E)h`. -/
noncomputable def carrierProfileHessian11
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  eulerDerivative (eulerDerivative D.carrierLongitudinalProfile) -
    eulerDerivative D.carrierLongitudinalProfile

/-- Determinant of the integral binary profile Hessian. -/
noncomputable def carrierProfileHessianDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  D.carrierProfileHessian00 * D.carrierProfileHessian11 -
    D.carrierProfileHessian01 * D.carrierProfileHessian01

/-- Exact coefficient formula for `(D-rE)h`. -/
theorem coeff_carrierProfileParameterEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    D.carrierProfileParameterEuler.coeff n =
      ((T.topFace.degree : MvPolynomial (Fin 3) K) -
        (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
          (n : MvPolynomial (Fin 3) K)) *
        D.carrierLongitudinalProfile.coeff n := by
  simp [carrierProfileParameterEuler, coeff_eulerDerivative]
  ring

/-- Exact stationary coefficient formula for `H00`. -/
theorem coeff_carrierProfileHessian00
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    D.carrierProfileHessian00.coeff n =
      (((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) - 1)) *
        D.carrierLongitudinalProfile.coeff n := by
  unfold carrierProfileHessian00
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, coeff_eulerDerivative,
    D.coeff_carrierProfileParameterEuler]
  ring

/-- Exact stationary coefficient formula for `H01`. -/
theorem coeff_carrierProfileHessian01
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    D.carrierProfileHessian01.coeff n =
      (n : MvPolynomial (Fin 3) K) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) *
        D.carrierLongitudinalProfile.coeff n := by
  simp [carrierProfileHessian01, coeff_eulerDerivative,
    D.coeff_carrierProfileParameterEuler]
  ring

/-- Exact stationary coefficient formula for `H11`. -/
theorem coeff_carrierProfileHessian11
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    D.carrierProfileHessian11.coeff n =
      (n : MvPolynomial (Fin 3) K) *
        ((n : MvPolynomial (Fin 3) K) - 1) *
        D.carrierLongitudinalProfile.coeff n := by
  simp [carrierProfileHessian11, coeff_eulerDerivative]
  ring

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
