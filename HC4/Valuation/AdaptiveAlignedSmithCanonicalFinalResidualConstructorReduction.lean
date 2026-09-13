import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualConstructorRefinement
import Mathlib.Tactic

/-!
# A19.26: exact constructor-level residuals for unrestricted HC4

A19.25 proves the two crossed constructor cases are empty:

* a represented surviving terminal has no strict-low special-fibre exponent;
* a positive represented blocker cannot satisfy the determinant-closing
  transverse Rees coefficient bound.

Consequently the A19.24 three-field resolver has only four genuinely live
constructor-specific obligations.  This file records that exact reduction and
nothing more.  In particular it introduces no new termination relation and no
cross-scale recursion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The exact constructor-specific residue after A19.25. -/
structure AdaptiveAlignedSmithCanonicalFinalConstructorResidualResolver where
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
        IsLowNegativeSecondSmithPattern e),
      False

  blockerPositiveLowLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) state)
      (_geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking D 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        D.presented.rawDefect D.presented.family),
      False

  survivingPositiveLowLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) state)
      (_geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking D 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        D.presented.rawDefect D.presented.family),
      False

  survivingPositiveReesReentry :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) state)
      (_geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking D 0)
      (_hpositive : 0 < state.rawDefect)
      (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
        D.presented.rawDefect D.presented.family)
      (_hspend :
        AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
          (D.presented.canonicalPositiveTransverseSectionFrontierState hbound)
          state),
      False

/-- A constructor-specific resolver fills the exact A19.24 resolver.  The two
missing crossed cases are discharged by A19.25. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalFinalConstructorResidualResolver.toFinalResidualResolver
    (R : AdaptiveAlignedSmithCanonicalFinalConstructorResidualResolver (K := K)) :
    AdaptiveAlignedSmithCanonicalFinalResidualResolver (K := K) where
  zeroStrictLow := by
    intro state hrepair T hzero e he hpattern
    cases T with
    | blocker D geometry =>
        have he' : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
            AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using he
        exact R.blockerZeroStrictLow hrepair D geometry hzero e he' hpattern
    | surviving D geometry =>
        have he' : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
            AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using he
        rcases D.noStrictLow_on_specialFiber e he' with
          ⟨hnotPure, hnotFirst, hnotSecond⟩
        rcases hpattern with hpure | hfirst | hsecond
        · exact hnotPure hpure
        · exact hnotFirst hfirst
        · exact hnotSecond hsecond

  positiveLowLayer := by
    intro state hrepair T hpositive L
    cases T with
    | blocker D geometry =>
        have L' : CanonicalPositiveTransverseReesLowLayer
            D.presented.rawDefect D.presented.family := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using L
        exact R.blockerPositiveLowLayer hrepair D geometry hpositive L'
    | surviving D geometry =>
        have L' : CanonicalPositiveTransverseReesLowLayer
            D.presented.rawDefect D.presented.family := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using L
        exact R.survivingPositiveLowLayer hrepair D geometry hpositive L'

  positiveReesReentry := by
    intro state hrepair T hpositive hbound hspend
    cases T with
    | blocker D geometry =>
        have hbound' : HasCanonicalPositiveTransverseReesCoefficientBound
            D.presented.rawDefect D.presented.family := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using hbound
        have hmove := D.sourcePresentation
        change Nonempty
          (CertifiedRamifiedEpisodeInternalMove D.presented state) at hmove
        rcases hmove with ⟨hmove⟩
        have hpositivePresented : 0 < D.presented.rawDefect := by
          rw [CertifiedRamifiedEpisodeInternalMove.raw_eq hmove]
          exact Nat.mul_pos
            (CertifiedRamifiedEpisodeInternalMove.ramification_pos hmove)
            hpositive
        exact D.not_positiveTransverseReesCoefficientBound hpositivePresented hbound'
    | surviving D geometry =>
        have hbound' : HasCanonicalPositiveTransverseReesCoefficientBound
            D.presented.rawDefect D.presented.family := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using hbound
        have hspend' :
            AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
              (D.presented.canonicalPositiveTransverseSectionFrontierState hbound') state := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState] using hspend
        exact R.survivingPositiveReesReentry
          hrepair D geometry hpositive hbound' hspend'

/-- **Constructor-level exact reduction to unrestricted HC4.** -/
theorem gradient_injective_of_hessianDeterminant_one_of_finalConstructorResidualResolver
    (R : AdaptiveAlignedSmithCanonicalFinalConstructorResidualResolver (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact gradient_injective_of_hessianDeterminant_one_of_finalResidualResolver
    R.toFinalResidualResolver F hdet

end

end HC4.Valuation
