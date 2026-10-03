import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetActivePivot
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# A19.124: the three cyclic pivots on the honest ray Hessian

A19.118 establishes nonzero principal minors on the coefficient-weighted
endpoint pencil.  A19.R9 identifies those minors with specialisations of the
Euler-scaled Hessian principal minors of the actual degree-one ray face.

Thus the three other-facet branches now carry genuine nonzero source-polynomial
pivots:

* `.pr` on `(2,3)`;
* `.sp` on `(1,3)`;
* `.rq` on `(1,2)`.

This remains division-free and does not yet use the strict superface.
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

/-- `.pr`: honest ray Euler-Hessian pivot on `(2,3)`. -/
theorem qs_ray_pr_eulerScaledHessianPrincipalMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.eulerScaledHessianPrincipalMinor
      C.ray.face (2 : Fin 4) 3 ≠ 0 := by
  apply HC4.Polynomial.eulerScaledHessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
    (K := K) (C.qs_ray_degreeOne_supportedLine hthree) (2 : Fin 4) 3
  simpa [qsRayDegreeOneCoefficientPolynomial] using
    C.qs_ray_pr_endpointActiveMinor_ne_zero hthree houtThree

/-- `.sp`: honest ray Euler-Hessian pivot on `(1,3)`. -/
theorem qs_ray_sp_eulerScaledHessianPrincipalMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.eulerScaledHessianPrincipalMinor
      C.ray.face (1 : Fin 4) 3 ≠ 0 := by
  apply HC4.Polynomial.eulerScaledHessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
    (K := K) (C.qs_ray_degreeOne_supportedLine hthree) (1 : Fin 4) 3
  simpa [qsRayDegreeOneCoefficientPolynomial] using
    C.qs_ray_sp_endpointActiveMinor_ne_zero hthree houtThree

/-- `.rq`: honest ray Euler-Hessian pivot on `(1,2)`. -/
theorem qs_ray_rq_eulerScaledHessianPrincipalMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.eulerScaledHessianPrincipalMinor
      C.ray.face (1 : Fin 4) 2 ≠ 0 := by
  apply HC4.Polynomial.eulerScaledHessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
    (K := K) (C.qs_ray_degreeOne_supportedLine hthree) (1 : Fin 4) 2
  simpa [qsRayDegreeOneCoefficientPolynomial] using
    C.qs_ray_rq_endpointActiveMinor_ne_zero hthree houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
