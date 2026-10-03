import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesLowLayerOrder
import HC4.PlanarJC2HessianEmbedding
import Mathlib.Tactic

/-!
# A19.35: split the surviving Rees low layer on the actual trace family

A19.34b removes every successful positive Rees coefficient bound by inserting
A19.33 as an ordinary raw-defect restart edge.  The only positive terminal
residue is therefore a concrete `CanonicalPositiveTransverseReesLowLayer` on
the genuine final trace state.

A19.27 already gives the exact source-facing dichotomy for such a layer.  It is
either literally present on the actual special fibre, or the actual family has
a positive parameter layer whose globally first positive order is strictly
below the determinant clock.

This file records that dichotomy before any terminal presentation is used.
In particular it does not transport parameter orders through ramification.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Presentation-free refinement of the two A19.34b residual themes.

The two positive fields are deliberately stated on `state.family`, not on the
possibly ramified family stored by the normalized presented terminal. -/
structure AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver where
  zeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hzero : state.rawDefect = 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e),
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

/-- A19.27 discharges the old positive-low-layer field by the exact actual
source-order split. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver.toReesReducedResidualResolver
    (R : AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver
      (K := K)) :
    AdaptiveAlignedSmithCanonicalReesReducedResidualResolver (K := K) where
  zeroStrictLow := by
    intro state hrepair T hzero e he hpattern
    exact R.zeroStrictLow hrepair T hzero e he hpattern

  positiveLowLayer := by
    intro state hrepair T hpositive L
    rcases L.specialFiber_or_earlierActualLayer with hspecial | hearlier
    · exact R.positiveSpecialFiberLow hrepair T hpositive L hspecial
    · rcases hearlier with ⟨hactual, hfirst⟩
      exact R.positiveEarlierActualLayer
        hrepair T hpositive L hactual hfirst

/-- HC4 front door after the presentation-free A19.27 split. -/
theorem gradient_injective_of_hessianDeterminant_one_of_reesLowLayerOrderResidualResolver
    (R : AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_reesReducedResidualResolver
      R.toReesReducedResidualResolver F hdet

/-- Soundness guard for the strengthened source-facing checklist: completing
these three fields is already enough to prove planar JC2. -/
theorem planarJC2_of_reesLowLayerOrderResidualResolver
    (R : AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver
      (K := K)) :
    HC4.PlanarJC2Injectivity K := by
  apply HC4.planarJC2_of_hessianFour_gradient_injective
  intro F hdet
  exact
    gradient_injective_of_hessianDeterminant_one_of_reesLowLayerOrderResidualResolver
      R F hdet

end

end HC4.Valuation
