import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyPivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSuperfaceSchur
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Valuation.PermutedFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# A19.R18: nonzero constant active block on the honest contact Rees

The final Schur straightening must cancel the active transverse block without
introducing a localization into the integral profile calculation.  The exact
certificate needed for that cancellation is stronger than mere nonvanishing
of the family pivot: its *constant parameter coefficient* is nonzero.

The contact-family special fibre has already been identified with the original
first-contact carrier, where the three cyclic Hessian pivots are nonzero.  This
module records the generic parameter-zero Hessian bridge and then exposes the
three corresponding constant active determinants.  No division is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The exact parameter-zero source layer is the usual polynomial-family
special fibre. -/
theorem familyParameterLayer_zero_eq_polynomialFamilySpecialFiber
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterLayer F 0 = polynomialFamilySpecialFiber F := by
  ext d
  rw [familyParameterLayer_coeff]
  simp [polynomialFamilySpecialFiber]

/-- Constant coefficient of the active determinant in a parameter-first
permuted Hessian block is exactly the corresponding Hessian principal minor
of the honest special fibre. -/
theorem permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedFamilyHessianFourBlock rho F).activeDet.coeff 0 =
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber F) (rho 0) (rho 1) := by
  unfold permutedFamilyHessianFourBlock GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix HC4.Polynomial.hessianPrincipalMinor
  simp only [Matrix.submatrix_apply]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.coeff_zero_eq_eval_zero]
  rw [parameterFirstHessian_coeff, parameterFirstHessian_coeff,
    parameterFirstHessian_coeff, parameterFirstHessian_coeff]
  rw [familyParameterLayer_zero_eq_polynomialFamilySpecialFiber]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- `.pr`: the contact-Rees active determinant has nonzero parameter constant
coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contactFamily_activeDet_coeff_zero_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation P.contactFamily).activeDet.coeff 0 ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [qsPrSuperfaceSchurPermutation] using
    P.pr_contactFamily_specialFiber_hessianPrincipalMinor_ne_zero hthree houtThree

/-- `.sp`: the contact-Rees active determinant has nonzero parameter constant
coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_contactFamily_activeDet_coeff_zero_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsSpSuperfaceSchurPermutation P.contactFamily).activeDet.coeff 0 ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [qsSpSuperfaceSchurPermutation] using
    P.sp_contactFamily_specialFiber_hessianPrincipalMinor_ne_zero hthree houtThree

/-- `.rq`: the contact-Rees active determinant has nonzero parameter constant
coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_contactFamily_activeDet_coeff_zero_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsRqSuperfaceSchurPermutation P.contactFamily).activeDet.coeff 0 ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [qsRqSuperfaceSchurPermutation] using
    P.rq_contactFamily_specialFiber_hessianPrincipalMinor_ne_zero hthree houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
