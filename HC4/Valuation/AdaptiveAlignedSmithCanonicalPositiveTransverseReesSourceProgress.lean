import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSpecialFiberSplit
import Mathlib.Tactic

/-!
# A19.34: source-honest positive transverse Rees frontier

A19.33 completely resolves a successful positive transverse Rees transform on
the state on which it is run.  At a normalized terminal that state is the
represented endpoint, which may itself be a pure ramified presentation of the
actual A18 trace state.  A strict raw drop on the represented clock must not be
silently compared with the smaller unramified source clock.

This file records the exact source-facing statement.

* if coefficient clearing fails, retain the concrete A19 low layer;
* if the section frontier is strict, A19.31 gives genuine same-scale progress
  on the represented endpoint and the original pure presentation is retained
  explicitly beside it;
* if the section frontier reaches the full determinant-closing weight, the
  A19.21 target has literal raw defect zero.  Zero is strictly below the
  positive *actual trace source* regardless of presentation scale, so this one
  branch is an honest A18 raw-defect restart from that source.

No cross-scale raw comparison is used in the strict-frontier branch and no new
termination measure is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact source-facing outcomes of the positive A19 Rees frontier at a
presented rank-three terminal. -/
inductive AdaptiveAlignedSmithCanonicalTerminalPositiveReesSourceOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | lowLayer
      (L : Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          source.rawDefect source.family))
  | presentedLowLayer
      (presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (sourcePresentation :
        HasCertifiedRamifiedEpisodeInternalMove presented source)
      (L : Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          presented.rawDefect presented.family))
  | presentedSameScale
      (P : AdaptiveAlignedSmithCanonicalPresentedSameScaleProgress RR source)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
      (rawDefect_lt : target.rawDefect < source.rawDefect)
      (repair_eq : target.repair = source.repair)

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- A successful coefficient bound on a positive represented terminal is
source-honestly either a strict same-scale exit *after the retained pure
presentation*, or a literal zero-clock target which is directly below the
actual positive source. -/
theorem positiveReesBound_presentedSameScale_or_sourceProgress
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hsourcePos : 0 < source.rawDefect)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
      T.presentedState.rawDefect T.presentedState.family) :
    AdaptiveAlignedSmithCanonicalTerminalPositiveReesSourceOutcome RR source := by
  let presented := T.presentedState
  let r := canonicalPositiveTransverseSectionFrontierWeight
    presented.rawDefect presented.movingSection
  have hpresentedPos : 0 < presented.rawDefect := by
    simpa [presented] using T.presentedState_rawDefect_pos_of_source_pos hsourcePos
  have hrle : r ≤ presented.rawDefect := by
    exact canonicalPositiveTransverseSectionFrontierWeight_le
      presented.rawDefect presented.movingSection
  rcases lt_or_eq_of_le hrle with hrlt | hreq
  · rcases presented.exists_canonicalPositiveTransverseRees_unramifiedReentry
        hpresentedPos hbound (by simpa [r] using hrlt) with
      ⟨target, hrawEq, hscale, hdegree, hcomplexity, hrepairLocal, hrawLt⟩
    have hsame : SameEpisodeScale target presented := by
      exact hscale
    have hprogress : CertifiedSameScaleEpisodeProgress RR target presented :=
      certifiedSameScaleEpisodeProgress_of_rawDefect_lt RR hsame hrawLt
    exact .presentedSameScale {
      presented := presented
      sourcePresentation := T.sourcePresentation
      target := target
      progress := hprogress
    }
  · let target := presented.canonicalPositiveTransverseSectionFrontierState hbound
    have hzero : target.rawDefect = 0 := by
      apply (presented.canonicalPositiveTransverseSectionFrontierState_rawDefect_zero_iff
        hbound).2
      simpa [r] using hreq
    have hpresentedRepair : presented.repair = source.repair := by
      rcases T.sourcePresentation with ⟨hmove⟩
      simpa [presented] using hmove.repair_eq
    have hrepair : target.repair = source.repair := by
      calc
        target.repair = presented.repair := by rfl
        _ = source.repair := hpresentedRepair
    have hraw : target.rawDefect < source.rawDefect := by
      rw [hzero]
      exact hsourcePos
    have hprogress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
      unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
      rw [hrepair]
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact hraw
    exact .globalProgress target hprogress hraw hrepair

/-- **Source-honest positive A19 frontier.**

At a positive reachable terminal, running the Rees test on the represented
endpoint has exactly three meaningful outcomes: a concrete low layer on that
presentation, a retained presentation followed by same-scale raw descent, or
an honest raw-defect restart from the actual trace source. -/
theorem positiveRees_sourceFrontier
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hsourcePos : 0 < source.rawDefect) :
    AdaptiveAlignedSmithCanonicalTerminalPositiveReesSourceOutcome RR source := by
  let presented := T.presentedState
  by_cases hbound : HasCanonicalPositiveTransverseReesCoefficientBound
      presented.rawDefect presented.family
  · exact T.positiveReesBound_presentedSameScale_or_sourceProgress
      hsourcePos hbound
  · have hpresentedPos : 0 < presented.rawDefect := by
      simpa [presented] using T.presentedState_rawDefect_pos_of_source_pos hsourcePos
    have hlow : Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          presented.rawDefect presented.family) :=
      canonicalPositiveTransverseReesLowLayer_of_not_bound
        hpresentedPos hbound
    exact .presentedLowLayer presented T.sourcePresentation hlow

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation