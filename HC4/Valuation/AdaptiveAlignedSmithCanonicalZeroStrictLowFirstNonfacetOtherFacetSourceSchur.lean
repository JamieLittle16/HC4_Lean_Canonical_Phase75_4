import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetEulerPivot
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import Mathlib.Tactic

/-!
# A19.129: cyclic Schur pivots on the represented source

The first-superface route is useful geometrically, but the contact-profile
closure should not identify that auxiliary exposure with a contact-Rees layer.
For the active Schur pivot no such identification is necessary.

The ray-leading reverse Rees already says that the locked degree-one ray is the
exact maximal initial form of the represented source.  The generic weighted
Hessian-principal-minor theorem therefore lifts A19.124's nonzero cyclic ray
pivots directly to the represented source itself.

Importantly, this module makes **no** singularity claim about the full
represented source.  The retained `C.hessian_zero` concerns the first-contact
face `C.face`, whereas the represented special fibre is the determinant-one
source.  Earlier unrooted versions of this file incorrectly fed the former to
a theorem requiring singularity of the latter.  The certified binary
contact/Schur route uses only the valid source-pivot lift here; determinant
closure is supplied by the honest parameter-family clock in A19.128.
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

/-- The ray-leading natural weight is an ordinary integer upper weight bound on
the represented source. -/
theorem QsOtherFacetRayReverseReesPackage.sourceWeight_bound
    (R : QsOtherFacetRayReverseReesPackage C) :
    HC4.Polynomial.IsWeightLE
      (fun i : Fin 4 => (R.weight i : ℤ)) (R.level : ℤ)
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro e he
  have h := R.bound e he
  rw [weight_natCast_eq R.weight e]
  exact_mod_cast h

/-- `.pr`: the `(2,3)` ray pivot lifts directly to the represented source. -/
theorem QsOtherFacetRayReverseReesPackage.pr_source_hessianPrincipalMinor_ne_zero
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (2 : Fin 4) 3 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    R.sourceWeight_bound (2 : Fin 4) 3
  rw [R.initialForm_eq_ray]
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (2 : Fin 4) 3
    (C.qs_ray_pr_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.sp`: the `(1,3)` ray pivot lifts directly to the represented source. -/
theorem QsOtherFacetRayReverseReesPackage.sp_source_hessianPrincipalMinor_ne_zero
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (1 : Fin 4) 3 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    R.sourceWeight_bound (1 : Fin 4) 3
  rw [R.initialForm_eq_ray]
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (1 : Fin 4) 3
    (C.qs_ray_sp_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.rq`: the `(1,2)` ray pivot lifts directly to the represented source. -/
theorem QsOtherFacetRayReverseReesPackage.rq_source_hessianPrincipalMinor_ne_zero
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (1 : Fin 4) 2 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    R.sourceWeight_bound (1 : Fin 4) 2
  rw [R.initialForm_eq_ray]
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (1 : Fin 4) 2
    (C.qs_ray_rq_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
