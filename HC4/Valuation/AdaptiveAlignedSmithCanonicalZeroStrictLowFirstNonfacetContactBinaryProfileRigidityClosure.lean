import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfileRigidity
import Mathlib.Tactic

/-!
# A19.R18: integral profile Hessian to R19 rigidity

R18 now owns a canonical integral binary profile Hessian.  R19 already owns the
fraction-field transport and finite staircase contradiction once three
coefficient formulas and a zero determinant are supplied.  This module splices
those interfaces literally: after the determinant equation is known, no
further profile algebra or localization remains.
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

/-- **R18/R19 closing seam.**  Once the honest integral binary profile Hessian
has zero determinant, the already-proved R19 staircase rigidity gives an
immediate contradiction. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_profileHessianDet
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (hdet : R.profileHessianDet = 0) : False := by
  apply R.impossible_of_coeffwise_hessian
    R.profileHessian00 R.profileHessian01 R.profileHessian11
  · exact R.coeff_profileHessian00
  · exact R.coeff_profileHessian01
  · exact R.coeff_profileHessian11
  · exact hdet

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
