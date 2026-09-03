import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfile
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryDeterminantCancellation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryCouplingCorrection
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessianFractionRecognition
import Mathlib.Tactic

/-!
# A19.119 / R19: contact fraction-profile rigidity

A19.114 constructs the exact symbolic longitudinal profile of the represented
source, and A19.115 injects it into the fraction field of the transverse
coefficient domain without losing its constant coefficient or degree.

At that point every input of the already-green finite staircase rigidity
theorem is present except one equation:

    binaryStaircaseProfileResidual D profileWeight profile = 0.

The first theorem below freezes that final field-valued interface.  R19 then
composes the integral fraction-field recognition theorem with this endpoint:
a caller may remain entirely in the honest transverse polynomial coefficient
ring and supply only three staircase Hessian entries, their coefficient
formulas, and a zero determinant.  Localization and the final finite staircase
contradiction are discharged here once and for all.

No transverse evaluation, planar JC2 hypothesis, or division in the geometric
coefficient ring is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The A19.115 fraction-field profile is impossible as soon as the honest
contact/Schur calculation supplies the stationary residual equation. -/
theorem QsOtherFacetContactFractionProfilePackage.impossible_of_residual
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (H : QsOtherFacetContactFractionProfilePackage C P)
    (hres :
      binaryStaircaseProfileResidual
        T.topFace.degree P.profileWeight H.profile = 0) : False := by
  have hle : H.profile.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      (K := qsContactProfileField K)
      T.topFace.degree P.profileWeight P.profileWeight_two_le H.profile
      H.coeff_zero_ne H.support_bound hres
  have htwo : 2 ≤ H.profile.natDegree := H.degree_two_le
  omega

/-- **A19.R19 integral closing interface.**

The final binary Schur adapter no longer needs to mention the transverse
fraction field.  If it produces an integral symmetric binary Hessian block
whose three entries have the canonical staircase coefficients and whose
2-by-2 determinant vanishes, A19.R15 maps that equation injectively to the
fraction field and A19.119 immediately gives the contradiction. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_coeffwise_hessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (H00 H01 H11 : Polynomial (MvPolynomial (Fin 3) K))
    (h00 : ∀ n : ℕ,
      H00.coeff n =
        (((T.topFace.degree : MvPolynomial (Fin 3) K) -
            (P.profileWeight : MvPolynomial (Fin 3) K) *
              (n : MvPolynomial (Fin 3) K)) *
          ((T.topFace.degree : MvPolynomial (Fin 3) K) -
            (P.profileWeight : MvPolynomial (Fin 3) K) *
              (n : MvPolynomial (Fin 3) K) - 1)) *
          R.profile.coeff n)
    (h01 : ∀ n : ℕ,
      H01.coeff n =
        (n : MvPolynomial (Fin 3) K) *
          ((T.topFace.degree : MvPolynomial (Fin 3) K) -
            (P.profileWeight : MvPolynomial (Fin 3) K) *
              (n : MvPolynomial (Fin 3) K)) *
          R.profile.coeff n)
    (h11 : ∀ n : ℕ,
      H11.coeff n =
        (n : MvPolynomial (Fin 3) K) *
          ((n : MvPolynomial (Fin 3) K) - 1) *
          R.profile.coeff n)
    (hdet : H00 * H11 - H01 * H01 = 0) : False := by
  let H : QsOtherFacetContactFractionProfilePackage C P :=
    Classical.choice R.fractionProfilePackage
  have hres :
      binaryStaircaseProfileResidual T.topFace.degree P.profileWeight
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
          R.profile) = 0 :=
    binaryStaircaseProfileResidual_fraction_eq_zero_of_coeffwise_hessian
      T.topFace.degree P.profileWeight R.profile H00 H01 H11
      h00 h01 h11 hdet
  have hprofile :
      H.profile =
        Polynomial.map
          (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
          R.profile := by
    rw [H.profile_eq, qsContactFractionLongitudinalProfile, ← R.profile_eq]
  apply H.impossible_of_residual
  rw [hprofile]
  exact hres

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation