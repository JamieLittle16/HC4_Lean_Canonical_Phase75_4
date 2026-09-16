import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceAdapter
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalConformalZeroClockImpossible
import Mathlib.Tactic

/-!
# A19.24: exact residual obligations for unrestricted HC4

The final terminal proof has now split completely by determinant clock.

At source raw defect zero, A19.23 closes the terminal outright whenever the
three genuinely strict-low Smith patterns are absent.  Thus only an actual
strict-low exponent of the represented special fibre remains.

At positive source raw defect, the represented terminal also has positive raw
defect because its presentation is a positive pure ramification.  A19.22 then
has only two outcomes: a concrete low layer in the represented polynomial
family, or the canonical maximal transverse Rees frontier together with its
source-facing certified spend.

This file records exactly those residual branches.  It is intentionally a
reduction theorem: no new geometric hypothesis is hidden and every branch
which is already closed is discharged internally.  Consequently the three
fields below are the exact Lean-level checklist still separating the current
branch from unrestricted HC4.  Mathematically they comprise only two local
themes: consume low layers, and consume the successful positive Rees re-entry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The exact residual local obligations after A19.22 and the unconditional
zero-clock conformal closure. -/
structure AdaptiveAlignedSmithCanonicalFinalResidualResolver where
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

  positiveLowLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        T.presentedState.rawDefect T.presentedState.family),
      False

  positiveReesReentry :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
        T.presentedState.rawDefect T.presentedState.family)
      (_hspend :
        AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
          (T.presentedState.canonicalPositiveTransverseSectionFrontierState hbound)
          state),
      False

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- Every actually reachable terminal is impossible once the exact three
residual branches above are consumed.  The zero-clock no-low case is closed
internally by the affine one-zero recovery theorem; the positive case is
exactly A19.22. -/
theorem impossible_of_finalResidualResolver
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0)
    (hrepair : state.repair = rankOneRepairState 0)
    (R : AdaptiveAlignedSmithCanonicalFinalResidualResolver (K := K)) :
    False := by
  by_cases hzero : state.rawDefect = 0
  · by_cases hlow :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e
    · rcases hlow with ⟨e, he, hpattern⟩
      exact R.zeroStrictLow hrepair T hzero e he hpattern
    · have hno : T.HasNoStrictLowSmithPatterns := by
        intro e he
        constructor
        · intro hpure
          exact hlow ⟨e, he, Or.inl hpure⟩
        constructor
        · intro hfirst
          exact hlow ⟨e, he, Or.inr (Or.inl hfirst)⟩
        · intro hsecond
          exact hlow ⟨e, he, Or.inr (Or.inr hsecond)⟩
      exact T.conformalDegreeTwoFace_impossible_of_source_rawDefect_eq_zero
        hzero hno
  · have hpositive : 0 < state.rawDefect := Nat.pos_of_ne_zero hzero
    have hmove := T.sourcePresentation
    change Nonempty
      (CertifiedRamifiedEpisodeInternalMove T.presentedState state) at hmove
    rcases hmove with ⟨hmove⟩
    have hpositivePresented : 0 < T.presentedState.rawDefect := by
      rw [CertifiedRamifiedEpisodeInternalMove.raw_eq hmove]
      exact Nat.mul_pos
        (CertifiedRamifiedEpisodeInternalMove.ramification_pos hmove)
        hpositive
    have hfront :=
      T.positiveTransverseRees_lowLayer_or_sourceRamifiedSpend hpositivePresented
    rcases hfront with hlow | hspend
    · rcases hlow with ⟨L⟩
      exact R.positiveLowLayer hrepair T hpositive L
    · rcases hspend with ⟨hbound, hspend⟩
      exact R.positiveReesReentry hrepair T hpositive hbound hspend

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- **Exact final reduction to unrestricted HC4.**

No JC2 hypothesis, homogeneous-family hypothesis, external degree cap, or new
termination relation remains.  Filling the residual resolver is enough for
the unrestricted determinant-one gradient injectivity theorem. -/
theorem gradient_injective_of_hessianDeterminant_one_of_finalResidualResolver
    (R : AdaptiveAlignedSmithCanonicalFinalResidualResolver (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
      F hdet (fun hrepair T => T.impossible_of_finalResidualResolver hrepair R)

end

end HC4.Valuation
