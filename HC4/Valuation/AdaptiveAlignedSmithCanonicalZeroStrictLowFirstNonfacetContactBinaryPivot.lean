import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySpecialization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSourceSchur
import Mathlib.Tactic

/-!
# A19.134: transport the other-facet source pivot to the binary contact family

A19.129 proves that the represented source has a nonzero cyclic Hessian
principal minor in each surviving other-facet case.  A19.133 proves that the
binary-homogenized contact family specializes at `tau = 1` to that represented
source entrywise at Hessian level.

Because a ring homomorphism sends a zero principal minor to zero, the source
nonvanishing lifts immediately back to the binary family.  This gives the
nonzero active pivot needed to combine the exact A19.128 Schur clock with the
A19.130--A19.132 binary Hessian identities.

No division, balance relation, or new geometric assumption is introduced.
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

/-- Specialization at `tau = 1` commutes with an ordinary Hessian principal
minor of the binary-homogenized family. -/
theorem QsOtherFacetContactQuadraticReesPackage.map_eval_one_hessianPrincipalMinor_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (i j : Fin 4) :
    MvPolynomial.map (Polynomial.evalRingHom 1)
        (HC4.Polynomial.hessianPrincipalMinor
          P.binaryHomogenizedFamily i j) =
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        i j := by
  unfold HC4.Polynomial.hessianPrincipalMinor
  simp only [map_sub, map_mul,
    P.map_eval_one_hessian_binaryHomogenizedFamily]

/-- Hence any nonzero represented-source principal minor is already nonzero on
the honest binary family before specialization. -/
theorem QsOtherFacetContactQuadraticReesPackage.binary_hessianPrincipalMinor_ne_zero_of_source
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (i j : Fin 4)
    (hsource :
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        i j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
      P.binaryHomogenizedFamily i j ≠ 0 := by
  intro hzero
  apply hsource
  rw [← P.map_eval_one_hessianPrincipalMinor_binaryHomogenizedFamily i j,
    hzero]
  simp

/-- `.pr`: the `(2,3)` source pivot of A19.129 survives on the binary family. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_binary_hessianPrincipalMinor_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      P.binaryHomogenizedFamily (2 : Fin 4) 3 ≠ 0 := by
  exact P.binary_hessianPrincipalMinor_ne_zero_of_source (2 : Fin 4) 3
    (R.pr_source_hessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.sp`: the `(1,3)` source pivot of A19.129 survives on the binary family. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_binary_hessianPrincipalMinor_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      P.binaryHomogenizedFamily (1 : Fin 4) 3 ≠ 0 := by
  exact P.binary_hessianPrincipalMinor_ne_zero_of_source (1 : Fin 4) 3
    (R.sp_source_hessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.rq`: the `(1,2)` source pivot of A19.129 survives on the binary family. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_binary_hessianPrincipalMinor_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      P.binaryHomogenizedFamily (1 : Fin 4) 2 ≠ 0 := by
  exact P.binary_hessianPrincipalMinor_ne_zero_of_source (1 : Fin 4) 2
    (R.rq_source_hessianPrincipalMinor_ne_zero hthree houtThree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
