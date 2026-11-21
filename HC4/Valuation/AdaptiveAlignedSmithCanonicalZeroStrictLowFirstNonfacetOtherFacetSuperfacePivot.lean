import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetEulerPivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRaySuperfaceInitial
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import Mathlib.Tactic

/-!
# A19.126: the three cyclic pivots survive on the first strict superface

A19.124 gives the nonzero ordinary Hessian principal minor on the locked ray.
A19.125 says that ray is the exact primary maximal initial form of A19.122's
honest first-superface polynomial.  A19.R10 therefore lifts the pivot to the
whole first superface.

Together with A19.122's zero Hessian determinant, this is the exact
rank-three/singular source polynomial required for a division-free Schur
reduction.
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
variable {R : QsOtherFacetRayReverseReesPackage C}

/-- The first-superface polynomial is bounded by the original primary ray
weight at the original ray level. -/
theorem QsOtherFacetRayFirstSuperfacePackage.primaryWeight_bound
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    HC4.Polynomial.IsWeightLE (qsRayPrimaryIntegerWeight R) (R.level : ℤ)
      S.polynomial := by
  intro d hd
  exact S.ray_exposed_in_polynomial.weight_le (by simpa using hd)

/-- `.pr`: the `(2,3)` ordinary Hessian principal pivot is nonzero on the
honest singular first superface. -/
theorem QsOtherFacetRayFirstSuperfacePackage.pr_hessianPrincipalMinor_ne_zero
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor S.polynomial (2 : Fin 4) 3 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    S.primaryWeight_bound (2 : Fin 4) 3
  rw [S.initialForm_primary_eq_ray]
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (2 : Fin 4) 3
    (C.qs_ray_pr_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.sp`: the `(1,3)` ordinary Hessian principal pivot is nonzero on the
honest singular first superface. -/
theorem QsOtherFacetRayFirstSuperfacePackage.sp_hessianPrincipalMinor_ne_zero
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor S.polynomial (1 : Fin 4) 3 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    S.primaryWeight_bound (1 : Fin 4) 3
  rw [S.initialForm_primary_eq_ray]
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (1 : Fin 4) 3
    (C.qs_ray_sp_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.rq`: the `(1,2)` ordinary Hessian principal pivot is nonzero on the
honest singular first superface. -/
theorem QsOtherFacetRayFirstSuperfacePackage.rq_hessianPrincipalMinor_ne_zero
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor S.polynomial (1 : Fin 4) 2 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    S.primaryWeight_bound (1 : Fin 4) 2
  rw [S.initialForm_primary_eq_ray]
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (1 : Fin 4) 2
    (C.qs_ray_rq_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
