import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesLowLayerOrderReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualConstructorRefinement
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstDeparture
import Mathlib.Tactic

/-!
# A19.36a: zero strict-low is a blocker first-departure problem

A19.34b/A19.35 moved the positive Rees analysis onto the actual final trace
state, before any pure terminal presentation.  The remaining zero-clock
residual is still naturally stated on the represented terminal special fibre.
Here the old constructor audit can be used without any cross-scale transport.

A canonical surviving terminal has no strict-low Smith exponent.  Therefore a
zero-clock strict-low residual can only come from the canonical blocker
constructor.  Moreover A18.5.88 already retains the blocker's canonical first
positive longitudinal departure on the represented special fibre after the
fixed right recentering.

This file makes that provenance part of the residual interface.  Thus the
zero-clock branch is no longer an arbitrary Smith-pattern contradiction: it is
one concrete blocker together with its actual first longitudinal departure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Source-order residuals after constructor-refining the zero-clock branch.
The positive branches remain on the actual trace family, exactly as in A19.35. -/
structure AdaptiveAlignedSmithCanonicalReesConstructorResidualResolver where
  blockerZeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) state)
      (_geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking D 0)
      (_hzero : state.rawDefect = 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber D.presented.family))
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e)
      (_hdeparture :
        HasFirstExactSmithExponentLongitudinalDeparture
          (longitudinalRightRecenterHom
            (K := K) (polynomialFamilySpecialFiber D.presented.family))
          D.blocker.exponent),
      False

  positiveSpecialFiberLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (_hspecial :
        L.exponent ∈ (polynomialFamilySpecialFiber state.family).support),
      False

  positiveEarlierActualLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (hactual : HasPositiveActualParameterLayer state.family)
      (_hearly :
        firstPositiveActualParameterOrder state.family hactual <
          state.rawDefect),
      False

/-- Constructor reduction of the A19.35 checklist.  The surviving zero branch
is discharged outright; the blocker zero branch is enriched by A18.5.88. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalReesConstructorResidualResolver.toReesLowLayerOrderResidualResolver
    (R : AdaptiveAlignedSmithCanonicalReesConstructorResidualResolver (K := K)) :
    AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver (K := K) where
  zeroStrictLow := by
    intro state hrepair T hzero e he hpattern
    cases T with
    | blocker D geometry =>
        have he' :
            e ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
            using he
        exact R.blockerZeroStrictLow
          hrepair D geometry hzero e he' hpattern
          D.firstLongitudinalDeparture_on_presentedSpecialFiber
    | surviving D geometry =>
        have he' :
            e ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
            using he
        rcases D.noStrictLow_on_specialFiber e he' with
          ⟨hnotPure, hnotFirst, hnotSecond⟩
        rcases hpattern with hpure | hfirst | hsecond
        · exact hnotPure hpure
        · exact hnotFirst hfirst
        · exact hnotSecond hsecond

  positiveSpecialFiberLow := by
    intro state hrepair T hpositive L hspecial
    exact R.positiveSpecialFiberLow hrepair T hpositive L hspecial

  positiveEarlierActualLayer := by
    intro state hrepair T hpositive L hactual hearly
    exact R.positiveEarlierActualLayer
      hrepair T hpositive L hactual hearly

/-- HC4 front door after deleting the surviving zero-clock constructor and
retaining the blocker's honest first-departure certificate. -/
theorem gradient_injective_of_hessianDeterminant_one_of_reesConstructorResidualResolver
    (R : AdaptiveAlignedSmithCanonicalReesConstructorResidualResolver (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_reesLowLayerOrderResidualResolver
      R.toReesLowLayerOrderResidualResolver F hdet

end

end HC4.Valuation
