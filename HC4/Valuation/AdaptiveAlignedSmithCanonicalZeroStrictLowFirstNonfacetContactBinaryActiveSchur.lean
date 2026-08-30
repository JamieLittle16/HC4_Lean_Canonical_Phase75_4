import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryPivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurClock
import Mathlib.Tactic

/-!
# A19.135: nonzero active Schur pivot on the binary contact family

A19.134 proves nonvanishing of the relevant ordinary Hessian principal minor
of the binary-homogenized contact family.  A19.128 formulates the exact
closing clock using `permutedFamilyHessianFourBlock`, whose entries live after
the canonical parameter-first ring equivalence.

This file closes that representation seam.  The active determinant of a
permuted family four-block is exactly the parameter-first image of the
corresponding ordinary Hessian principal minor.  Since the parameter-first map
is an equivalence, the three cyclic A19.134 pivots remain nonzero in the exact
Schur block consumed by A19.128.

No localization or division by the pivot is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The active determinant of the state-free permuted family block is the
parameter-first image of the corresponding ordinary Hessian principal minor. -/
theorem permutedFamilyHessianFourBlock_activeDet_eq_parameterFirst_hessianPrincipalMinor
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedFamilyHessianFourBlock rho F).activeDet =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor F (rho 0) (rho 1)) := by
  unfold permutedFamilyHessianFourBlock GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [map_sub, map_mul, map_mul]
  change
    parameterFirstHessian F (rho 0) (rho 0) *
          parameterFirstHessian F (rho 1) (rho 1) -
        parameterFirstHessian F (rho 0) (rho 1) *
          parameterFirstHessian F (rho 0) (rho 1) =
      parameterFirstHessian F (rho 0) (rho 0) *
          parameterFirstHessian F (rho 1) (rho 1) -
        parameterFirstHessian F (rho 0) (rho 1) *
          parameterFirstHessian F (rho 1) (rho 0)
  rw [parameterFirstHessian_symmetric F (rho 1) (rho 0)]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- A nonzero ordinary binary Hessian principal minor gives a nonzero active
determinant in the parameter-first permuted family block. -/
theorem QsOtherFacetContactQuadraticReesPackage.binary_permuted_activeDet_ne_zero_of_minor
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor P.binaryHomogenizedFamily
        (rho 0) (rho 1) ≠ 0) :
    (permutedFamilyHessianFourBlock rho P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_eq_parameterFirst_hessianPrincipalMinor]
  intro hzero
  apply hminor
  apply (parameterFirstEquiv K).injective
  simpa using hzero

/-- `.pr`: the exact binary Schur block has nonzero active determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_binary_activeDet_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  apply P.binary_permuted_activeDet_ne_zero_of_minor
  simpa [qsPrSuperfaceSchurPermutation] using
    P.pr_binary_hessianPrincipalMinor_ne_zero R hthree houtThree

/-- `.sp`: the exact binary Schur block has nonzero active determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_binary_activeDet_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsSpSuperfaceSchurPermutation P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  apply P.binary_permuted_activeDet_ne_zero_of_minor
  simpa [qsSpSuperfaceSchurPermutation] using
    P.sp_binary_hessianPrincipalMinor_ne_zero R hthree houtThree

/-- `.rq`: the exact binary Schur block has nonzero active determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_binary_activeDet_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsRqSuperfaceSchurPermutation P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  apply P.binary_permuted_activeDet_ne_zero_of_minor
  simpa [qsRqSuperfaceSchurPermutation] using
    P.rq_binary_hessianPrincipalMinor_ne_zero R hthree houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
