import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarSpecialPivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyActiveConstant
import Mathlib.Tactic

/-!
# A19 constant active pivot on the singular planar-contact Rees

The generic R18 cancellation only needs a nonzero constant parameter
coefficient of the active transverse Hessian determinant.  The singular
planar-contact Rees already has exactly the required source-honest special
fibre: its zero layer is the literal locked rank-three pair and the `(2,3)`
principal Hessian minor is nonzero.

This file exports that fact in the parameter-first four-block representation.
No localization, division, determinant implication, or clock identification is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The honest planar-contact family's `(2,3)` active determinant has a
nonzero constant family-parameter coefficient.  This is the division-free
pivot certificate used by the final Schur/profile cancellation. -/
theorem contactFamily_activeDet_coeff_zero_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation D.family).activeDet.coeff 0 ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [qsPrSuperfaceSchurPermutation] using
    D.specialFiber_hessianPrincipalMinor_two_three_ne_zero hthree houtThree

/-- Whole-polynomial cancellation by the planar-contact active pivot.  This is
exactly the generic R18 triangular argument, specialized to the source-honest
planar family. -/
theorem cancel_contactFamily_activeDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (hprod : ∀ n : ℕ,
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation D.family).activeDet * B).coeff n) = 0) :
    B = 0 := by
  let A := (permutedFamilyHessianFourBlock
    qsPrSuperfaceSchurPermutation D.family).activeDet
  have hA0 : A.coeff 0 ≠ 0 := by
    simpa [A] using D.contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  have hAB : A * B = 0 := by
    apply Polynomial.ext
    intro n
    simpa [A] using hprod n
  have hA : A ≠ 0 := by
    intro hzero
    apply hA0
    rw [hzero]
    simp
  exact (mul_eq_zero.mp hAB).resolve_left hA

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
