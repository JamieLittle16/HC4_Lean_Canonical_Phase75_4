import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianBoundedCancellation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDegreeBound
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileTerminalContradiction
import Mathlib.Tactic

/-!
# A19.R18: cyclic active-pivot product clock implies contradiction

The remaining Schur adapter naturally produces coefficientwise vanishing of

    contactActiveDet * parameterFirst(profileHessianDetFamily)

strictly below the binary Hessian closing clock.  The right factor is already
proved to have smaller parameter degree, and each cyclic contact active pivot
has nonzero constant parameter coefficient.  Bounded triangular cancellation
therefore kills the whole binary profile determinant, after which the R18/R19
terminal splice gives `False`.
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

private abbrev binaryProfileClock
    (P : QsOtherFacetContactQuadraticReesPackage C) : ℕ :=
  (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6

/-- `.pr`: the below-clock active-pivot product identity already contradicts
R19. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.pr_impossible_of_profilePivotProductClock
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hprod : ∀ q : ℕ, q < binaryProfileClock P →
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation P.contactFamily).activeDet *
        parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff q) = 0) : False := by
  have hzero :
      parameterFirstEquiv K P.binaryProfileHessianDetFamily = 0 := by
    apply P.pr_cancel_contactFamily_activeDet_of_natDegree_lt
      hthree houtThree
      (parameterFirstEquiv K P.binaryProfileHessianDetFamily)
      (binaryProfileClock P)
    · exact R.parameterFirst_binaryProfileHessianDetFamily_natDegree_lt_hessianClock
    · exact hprod
  apply R.impossible_of_binaryProfileHessianDetFamily_layers
  intro n
  rw [← parameterFirstEquiv_coeff]
  rw [hzero]
  simp

/-- `.sp`: the below-clock active-pivot product identity already contradicts
R19. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.sp_impossible_of_profilePivotProductClock
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent)
    (hprod : ∀ q : ℕ, q < binaryProfileClock P →
      (((permutedFamilyHessianFourBlock
          qsSpSuperfaceSchurPermutation P.contactFamily).activeDet *
        parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff q) = 0) : False := by
  have hzero :
      parameterFirstEquiv K P.binaryProfileHessianDetFamily = 0 := by
    apply P.sp_cancel_contactFamily_activeDet_of_natDegree_lt
      hthree houtThree
      (parameterFirstEquiv K P.binaryProfileHessianDetFamily)
      (binaryProfileClock P)
    · exact R.parameterFirst_binaryProfileHessianDetFamily_natDegree_lt_hessianClock
    · exact hprod
  apply R.impossible_of_binaryProfileHessianDetFamily_layers
  intro n
  rw [← parameterFirstEquiv_coeff]
  rw [hzero]
  simp

/-- `.rq`: the below-clock active-pivot product identity already contradicts
R19. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.rq_impossible_of_profilePivotProductClock
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent)
    (hprod : ∀ q : ℕ, q < binaryProfileClock P →
      (((permutedFamilyHessianFourBlock
          qsRqSuperfaceSchurPermutation P.contactFamily).activeDet *
        parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff q) = 0) : False := by
  have hzero :
      parameterFirstEquiv K P.binaryProfileHessianDetFamily = 0 := by
    apply P.rq_cancel_contactFamily_activeDet_of_natDegree_lt
      hthree houtThree
      (parameterFirstEquiv K P.binaryProfileHessianDetFamily)
      (binaryProfileClock P)
    · exact R.parameterFirst_binaryProfileHessianDetFamily_natDegree_lt_hessianClock
    · exact hprod
  apply R.impossible_of_binaryProfileHessianDetFamily_layers
  intro n
  rw [← parameterFirstEquiv_coeff]
  rw [hzero]
  simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
