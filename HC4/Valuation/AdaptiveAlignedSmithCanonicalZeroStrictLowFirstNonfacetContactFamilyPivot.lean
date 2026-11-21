import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactIntegralFace
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactRayPivotLift

/-!
# A19.R18: cyclic active pivots on the honest contact-Rees special fibre

The ray-pivot lift proves the three cyclic active principal minors are already
nonzero on the original first-contact carrier.  The integral-face bridge
identifies that carrier with the special fibre of the honest contact Rees.
This module exposes the resulting family-native pivots for the final Schur
straightening.
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

/-- `.pr`: the `(2,3)` active pivot is nonzero on the honest contact-Rees
special fibre. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contactFamily_specialFiber_hessianPrincipalMinor_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber P.contactFamily) (2 : Fin 4) 3 ≠ 0 := by
  rw [P.contactFamily_specialFiber_eq_face]
  exact C.qs_contactFace_pr_hessianPrincipalMinor_ne_zero hthree houtThree

/-- `.sp`: the `(1,3)` active pivot is nonzero on the contact-Rees special
fibre. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_contactFamily_specialFiber_hessianPrincipalMinor_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber P.contactFamily) (1 : Fin 4) 3 ≠ 0 := by
  rw [P.contactFamily_specialFiber_eq_face]
  exact C.qs_contactFace_sp_hessianPrincipalMinor_ne_zero hthree houtThree

/-- `.rq`: the `(1,2)` active pivot is nonzero on the contact-Rees special
fibre. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_contactFamily_specialFiber_hessianPrincipalMinor_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber P.contactFamily) (1 : Fin 4) 2 ≠ 0 := by
  rw [P.contactFamily_specialFiber_eq_face]
  exact C.qs_contactFace_rq_hessianPrincipalMinor_ne_zero hthree houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
