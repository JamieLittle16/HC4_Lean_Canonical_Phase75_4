import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFirstActualLayer
import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingRelativeFirstLayer
import Mathlib.Tactic

/-!
# A19.108: relative first deformation of the locked-ray reverse Rees

The generic relative-first-layer construction is independent of the old
rank-one closing carrier.  Applied to A19.104b it freezes the complete locked
ray and divides the positive parameter remainder by the least actual order.
Thus the ray-leading family has the honest factorisation

    Q = const(ray) + tau^j * R,

and the special fibre of `R` is exactly the first lower face from A19.105.
This is the recursive polynomial object needed by the staircase argument.
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

/-- Honest relative first-deformation quotient of the ray-leading reverse-Rees
family. -/
noncomputable def QsOtherFacetRayReverseReesPackage.relativeFirstDeformation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  firstActualDeformationFamily
    (reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound)
    R.positiveLayer

/-- Exact decomposition into the frozen locked ray and the first positive
deformation tail. -/
theorem QsOtherFacetRayReverseReesPackage.relativeFirstDeformation_factorisation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C) :
    reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound =
      constantPolynomialFamily C.ray.face +
        MvPolynomial.C
          (Polynomial.X ^ firstPositiveActualParameterOrder
            (reverseWeightedReesFamily R.weight R.level
              (polynomialFamilySpecialFiber
                T.terminal.blocker.presented.family) R.bound)
            R.positiveLayer) *
          R.relativeFirstDeformation := by
  have h := firstActualDeformationFamily_factorisation
    (reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound)
    R.positiveLayer
  rw [R.specialFiber_eq_ray] at h
  simpa [QsOtherFacetRayReverseReesPackage.relativeFirstDeformation] using h

/-- The quotient special fibre is the first lower source face selected in
A19.105. -/
theorem QsOtherFacetRayFirstActualLayerPackage.relativeFirstDeformation_specialFiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {R : QsOtherFacetRayReverseReesPackage C}
    (L : QsOtherFacetRayFirstActualLayerPackage C R) :
    polynomialFamilySpecialFiber R.relativeFirstDeformation = L.layer := by
  have h := firstActualDeformationFamily_specialFiber
    (reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound)
    R.positiveLayer
  rw [← L.order_eq_first, ← L.layer_eq] at h
  simpa [QsOtherFacetRayReverseReesPackage.relativeFirstDeformation] using h

/-- The relative first-deformation quotient is genuinely nonzero. -/
theorem QsOtherFacetRayReverseReesPackage.relativeFirstDeformation_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C) :
    R.relativeFirstDeformation ≠ 0 := by
  simpa [QsOtherFacetRayReverseReesPackage.relativeFirstDeformation] using
    firstActualDeformationFamily_ne_zero
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)
      R.positiveLayer

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
