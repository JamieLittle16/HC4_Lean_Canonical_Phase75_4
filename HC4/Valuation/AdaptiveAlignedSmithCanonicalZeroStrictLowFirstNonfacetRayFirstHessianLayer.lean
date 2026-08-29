import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFirstActualLayer
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Tactic

/-!
# A19.106: first Hessian layer and determinant timing of the ray-leading Rees family

A19.105 identifies the least positive source layer of the honest ray-leading
reverse-Rees family.  Existing generic coefficient calculus already implies
that spatial Hessians commute with exact parameter-layer extraction and that
there are no hidden positive Hessian layers before the least actual source
order.

The pure Hessian determinant clock gives one final two-way split: the first
actual layer is either strictly preclosing, in which case the corresponding
full determinant layer is zero, or it occurs exactly at determinant closure.
This file packages those facts without introducing a Schur chart or expanding
the four-by-four determinant.
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

/-- Coefficient-level Hessian and timing data at the first genuine deformation
of the locked ray. -/
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
  timing :
    L.order < 4 * R.level - 2 * ∑ i : Fin 4, R.weight i ∨
      L.order = 4 * R.level - 2 * ∑ i : Fin 4, R.weight i
  preclosing_determinantLayer_zero :
    L.order < 4 * R.level - 2 * ∑ i : Fin 4, R.weight i →
      familyParameterLayer
        (HC4.Polynomial.hessianDeterminant
          (reverseWeightedReesFamily R.weight R.level
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family) R.bound))
        L.order = 0

/-- **A19.106 exact first-Hessian frontier.**  The first actual lower source
face is also the first positive Hessian layer, and it is either strictly below
the pure determinant-closing order or exactly at it. -/
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
  let Delta : ℕ := 4 * R.level - 2 * ∑ i : Fin 4, R.weight i

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

  have htiming : L.order < Delta ∨ L.order = Delta := by
    exact lt_or_eq_of_le (by simpa [Delta] using L.order_le_defect)

  have hpre :
      L.order < Delta →
        familyParameterLayer (HC4.Polynomial.hessianDeterminant Q) L.order = 0 := by
    intro hlt
    exact hessianDefect_parameterLayer_eq_zero_of_lt
      Q R.hessianDefect (by simpa [Delta] using hlt)

  exact ⟨{
    hessianLayer_eq := by simpa [Q] using hhessian
    lowerHessian_zero := by simpa [Q] using hlower
    timing := by simpa [Delta] using htiming
    preclosing_determinantLayer_zero := by
      intro hlt
      simpa [Q, Delta] using hpre (by simpa [Delta] using hlt)
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
