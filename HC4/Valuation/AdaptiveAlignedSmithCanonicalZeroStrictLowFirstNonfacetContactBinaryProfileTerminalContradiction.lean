import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDeterminantExtraction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileRigidityClosure
import Mathlib.Tactic

/-!
# A19.R18: binary profile layers to terminal contradiction

The whole-family binary profile Hessian has already been recognized and its
exact quadratic parameter layers extract the integral profile-Hessian
determinant coefficient by coefficient.  R19 already proves that the resulting
integral determinant cannot vanish for the honest noncancelling longitudinal
profile.

This module closes that interface: once the Schur clock supplies zero binary
profile-Hessian determinant layers at every order `2D-r*n`, no additional
localization, profile algebra, or rigidity argument remains.
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

/-- **R18/R19 terminal splice.**  Vanishing of every exact quadratic layer of
the honest binary parameter/longitudinal Hessian determinant is impossible. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_binaryProfileHessianDetFamily_layers
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (hlayers : ∀ n : ℕ,
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * T.topFace.degree - P.profileWeight * n) = 0) : False := by
  apply R.impossible_of_profileHessianDet
  exact R.profileHessianDet_eq_zero_of_binaryFamily_layers hlayers

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
