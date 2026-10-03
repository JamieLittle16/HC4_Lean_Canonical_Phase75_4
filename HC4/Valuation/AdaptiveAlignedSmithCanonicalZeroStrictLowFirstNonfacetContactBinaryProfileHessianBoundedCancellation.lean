import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianCancellation
import Mathlib.Tactic

/-!
# A19.R18: bounded cyclic active-pivot cancellation

The binary Hessian clock only supplies product-coefficient vanishing strictly
below its closing order.  The generic R18 cancellation owner already proves
that this is sufficient whenever the right factor has smaller parameter
`natDegree`.  This module attaches that exact bounded interface to each of the
three honest cyclic contact pivots.
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

/-- `.pr`: bounded cancellation by the honest contact-family active pivot. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_cancel_contactFamily_activeDet_of_natDegree_lt
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (N : ℕ)
    (hBdeg : B.natDegree < N)
    (hprod : ∀ n : ℕ, n < N →
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation P.contactFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  apply polynomial_eq_zero_of_constant_pivot_of_natDegree_lt
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation P.contactFamily).activeDet B N
  · exact P.pr_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  · exact hBdeg
  · exact hprod

/-- `.sp`: bounded cancellation by the honest contact-family active pivot. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_cancel_contactFamily_activeDet_of_natDegree_lt
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (N : ℕ)
    (hBdeg : B.natDegree < N)
    (hprod : ∀ n : ℕ, n < N →
      (((permutedFamilyHessianFourBlock
          qsSpSuperfaceSchurPermutation P.contactFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  apply polynomial_eq_zero_of_constant_pivot_of_natDegree_lt
    (permutedFamilyHessianFourBlock
      qsSpSuperfaceSchurPermutation P.contactFamily).activeDet B N
  · exact P.sp_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  · exact hBdeg
  · exact hprod

/-- `.rq`: bounded cancellation by the honest contact-family active pivot. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_cancel_contactFamily_activeDet_of_natDegree_lt
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (N : ℕ)
    (hBdeg : B.natDegree < N)
    (hprod : ∀ n : ℕ, n < N →
      (((permutedFamilyHessianFourBlock
          qsRqSuperfaceSchurPermutation P.contactFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  apply polynomial_eq_zero_of_constant_pivot_of_natDegree_lt
    (permutedFamilyHessianFourBlock
      qsRqSuperfaceSchurPermutation P.contactFamily).activeDet B N
  · exact P.rq_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  · exact hBdeg
  · exact hprod

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
