import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLongitudinalProfile
import HC4.Polynomial.AutonomousODEReconstruction
import Mathlib.Tactic

/-!
# A19.R18: integral binary profile Hessian

The final R19 consumer deliberately accepts its three Hessian entries over the
honest transverse coefficient ring `MvPolynomial (Fin 3) K`.  This module
constructs those entries directly from the raw longitudinal profile by Euler
operators, without passing through the fraction field and without duplicating
the field-valued staircase package.

For a profile coefficient `a_n`, put `E = z d/dz`.  The weighted parameter
Euler operator is

    P = D - r E.

The three entries are then

    H00 = (P - 1) P h,
    H01 = E P h,
    H11 = (E^2 - E) h.

Their coefficients are exactly

    (D-rn)(D-rn-1) a_n,
    n(D-rn) a_n,
    n(n-1) a_n.

Everything remains integral in the transverse polynomial coefficient ring.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- The integral weighted parameter-Euler operator `(D-rE)h` on the honest
longitudinal profile. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.profileParameterEuler
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  Polynomial.C (T.topFace.degree : MvPolynomial (Fin 3) K) * R.profile -
    Polynomial.C (P.profileWeight : MvPolynomial (Fin 3) K) *
      eulerDerivative R.profile

/-- Parameter-parameter entry `(D-rE-1)(D-rE)h`. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian00
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  Polynomial.C
      ((T.topFace.degree : MvPolynomial (Fin 3) K) - 1) *
      R.profileParameterEuler -
    Polynomial.C (P.profileWeight : MvPolynomial (Fin 3) K) *
      eulerDerivative R.profileParameterEuler

/-- Mixed parameter/longitudinal entry `E(D-rE)h`. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian01
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  eulerDerivative R.profileParameterEuler

/-- Longitudinal-longitudinal falling Euler entry `(E^2-E)h`. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian11
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  eulerDerivative (eulerDerivative R.profile) - eulerDerivative R.profile

/-- Determinant of the integral binary profile Hessian. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  R.profileHessian00 * R.profileHessian11 -
    R.profileHessian01 * R.profileHessian01

/-- Exact coefficient formula for the weighted parameter-Euler profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.coeff_profileParameterEuler
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    R.profileParameterEuler.coeff n =
      ((T.topFace.degree : MvPolynomial (Fin 3) K) -
        (P.profileWeight : MvPolynomial (Fin 3) K) *
          (n : MvPolynomial (Fin 3) K)) *
        R.profile.coeff n := by
  simp [QsOtherFacetContactRawLongitudinalProfilePackage.profileParameterEuler,
    coeff_eulerDerivative]
  ring

/-- Exact coefficient formula for `H00`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.coeff_profileHessian00
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    R.profileHessian00.coeff n =
      (((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) - 1)) *
        R.profile.coeff n := by
  simp [QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian00,
    coeff_eulerDerivative, R.coeff_profileParameterEuler]
  ring

/-- Exact coefficient formula for `H01`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.coeff_profileHessian01
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    R.profileHessian01.coeff n =
      (n : MvPolynomial (Fin 3) K) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) *
        R.profile.coeff n := by
  simp [QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian01,
    coeff_eulerDerivative, R.coeff_profileParameterEuler]
  ring

/-- Exact coefficient formula for `H11`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.coeff_profileHessian11
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    R.profileHessian11.coeff n =
      (n : MvPolynomial (Fin 3) K) *
        ((n : MvPolynomial (Fin 3) K) - 1) *
        R.profile.coeff n := by
  simp [QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian11,
    coeff_eulerDerivative]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
