import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianEulerReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactWeightedSchurShear
import Mathlib.Tactic

/-!
# A19.R18.21: exact `.pr` parameter-residual obstruction

The `.pr` weighted-Euler straightening is now explicit enough that the final
local obstruction can be named without referring to any Schur quotient or
binary/contact filtration comparison.

The raw complementary determinant is *not* the contact profile-Hessian core.
Their exact difference is `contactProfileParameterResidual`.  Recording that
identity here prevents the final extremal calculation from silently treating a
contact parameter order as a binary parameter order after transverse
inflation.

This module is algebraic plumbing only.  It proves no vanishing statement and
introduces no new geometric hypothesis, pivot cancellation, or global clock.
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
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18.21 exact PR obstruction.**  The straightened raw complementary
binary determinant differs from the contact-native longitudinal profile
Hessian determinant by exactly the parameter-differentiation residual. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contactWeightedEulerShear_rawComplementDet_eq_profileReduction_add_residual
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    (P.contactWeightedEulerShear qsPrContactSchurPermutation).x *
        (P.contactWeightedEulerShear qsPrContactSchurPermutation).z -
      (P.contactWeightedEulerShear qsPrContactSchurPermutation).y *
        (P.contactWeightedEulerShear qsPrContactSchurPermutation).y =
      P.contactProfileHessianDetReduction +
        P.contactProfileParameterResidual := by
  have h := P.pr_contactWeightedEulerShear_rawComplementDet
  dsimp at h
  rw [h]
  unfold QsOtherFacetContactQuadraticReesPackage.contactProfileHessianDetReduction
  ring

/-- Subtractive form of the exact PR obstruction.  This is the form consumed
by the extremal coefficient calculation. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contactWeightedEulerShear_rawComplementDet_sub_profileReduction
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    (P.contactWeightedEulerShear qsPrContactSchurPermutation).x *
          (P.contactWeightedEulerShear qsPrContactSchurPermutation).z -
        (P.contactWeightedEulerShear qsPrContactSchurPermutation).y *
          (P.contactWeightedEulerShear qsPrContactSchurPermutation).y -
      P.contactProfileHessianDetReduction =
        P.contactProfileParameterResidual := by
  rw [P.pr_contactWeightedEulerShear_rawComplementDet_eq_profileReduction_add_residual]
  ring

/-- Keeping the active pivot attached introduces no further correction: the
entire discrepancy from the active-pivot/profile product is precisely the
active pivot times the parameter residual. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contactWeightedEulerShear_activeDet_mul_rawComplementDet_sub_profileReduction
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    (P.contactWeightedEulerShear qsPrContactSchurPermutation).activeDet *
        ((P.contactWeightedEulerShear qsPrContactSchurPermutation).x *
            (P.contactWeightedEulerShear qsPrContactSchurPermutation).z -
          (P.contactWeightedEulerShear qsPrContactSchurPermutation).y *
            (P.contactWeightedEulerShear qsPrContactSchurPermutation).y) -
      (P.contactWeightedEulerShear qsPrContactSchurPermutation).activeDet *
        P.contactProfileHessianDetReduction =
      (P.contactWeightedEulerShear qsPrContactSchurPermutation).activeDet *
        P.contactProfileParameterResidual := by
  rw [P.pr_contactWeightedEulerShear_rawComplementDet_eq_profileReduction_add_residual]
  ring

-- CI anchor: verify the exact residual obstruction after inventory refresh.

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
