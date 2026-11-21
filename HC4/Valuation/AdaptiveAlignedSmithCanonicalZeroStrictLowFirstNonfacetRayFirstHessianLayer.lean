import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFirstActualLayer
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Tactic

/-!
# A19.106: first preclosing Hessian layer of the ray-leading Rees family

A19.105 identifies the least positive source layer of the honest ray-leading
reverse-Rees family and, using the dominant determinant clock, proves that this
order is strictly before determinant closure.  Existing generic coefficient
calculus then gives the complete first-variation package without any new
four-by-four determinant calculation:

* spatial Hessians commute with exact parameter-layer extraction;
* every positive Hessian layer below the first actual source order vanishes;
* the full Hessian-determinant layer at the first actual order is zero.

The remaining local task is therefore purely geometric: identify the Schur
linear source of this one honest lower layer against the locked rank-three ray.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Coefficient-level Hessian data at the first genuine deformation of the
locked ray.  The determinant layer is already preclosing and hence zero. -/
structure QsOtherFacetRayFirstHessianLayerPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (R : QsOtherFacetRayReverseReesPackage C)
    (L : QsOtherFacetRayFirstActualLayerPackage C R) where
  hessianLayer_eq :
    familyParameterHessianLayer
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound)
        L.order =
      HC4.Polynomial.hessian L.layer
  lowerHessian_zero :
    ∀ n : ℕ, 0 < n → n < L.order →
      familyParameterHessianLayer
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound)
        n = 0
  determinantLayer_zero :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound))
      L.order = 0

/-- **A19.106 exact first-Hessian frontier.**  The first actual lower source
face is the first positive Hessian layer and its full determinant coefficient
vanishes because A19.105 places it strictly before closure. -/
theorem QsOtherFacetRayFirstActualLayerPackage.firstHessianLayerPackage
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {R : QsOtherFacetRayReverseReesPackage C}
    (L : QsOtherFacetRayFirstActualLayerPackage C R) :
    Nonempty (QsOtherFacetRayFirstHessianLayerPackage C R L) := by
  let Q : MvPolynomial (Fin 4) (Polynomial K) :=
    reverseWeightedReesFamily R.weight R.level
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) R.bound

  have hhessian :
      familyParameterHessianLayer Q L.order = HC4.Polynomial.hessian L.layer := by
    rw [familyParameterHessianLayer_eq_hessian]
    rw [L.layer_eq]

  have hlower :
      ∀ n : ℕ, 0 < n → n < L.order →
        familyParameterHessianLayer Q n = 0 := by
    intro n hnpos hnlt
    apply familyParameterHessianLayer_eq_zero_of_pos_lt_firstPositiveActual
      Q R.positiveLayer hnpos
    rw [← L.order_eq_first]
    exact hnlt

  have hdetzero :
      familyParameterLayer (HC4.Polynomial.hessianDeterminant Q) L.order = 0 :=
    hessianDefect_parameterLayer_eq_zero_of_lt
      Q R.hessianDefect L.order_lt_defect

  exact ⟨{
    hessianLayer_eq := by simpa [Q] using hhessian
    lowerHessian_zero := by simpa [Q] using hlower
    determinantLayer_zero := by simpa [Q] using hdetzero
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
