import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionReentry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeSpecialFiber
import Mathlib.Tactic

/-!
# A19.22: source-facing positive transverse Rees adapter

A19.21 closes the moving-section issue on the represented positive-clock
state.  Coefficient clearing either fails at one of the four concrete low
Smith patterns, or the canonical frontier state is an honest factor-two
ramified raw-defect spend from that represented state.

A presented rank-three terminal is itself connected to the actual trace state
by a certified pure ramified presentation.  The existing cross-scale
composition theorem `HasCertifiedRamifiedEpisodeInternalMove.then_spend`
therefore transports the A19.21 spend all the way back to the trace source.

This file contains only that assembly.  It introduces no new geometry and no
new termination relation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- For a positive-clock adaptive state, the full A19.21 trichotomy can be
compressed to the two outcomes needed by final assembly: a concrete low Smith
layer, or an honest ramified spend.  The full-weight zero-defect landing is
included in the spend branch because the positive section-frontier weight
already makes its raw clock strictly smaller after the fixed ramification by
two. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseRees_lowLayer_or_ramifiedSpend
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect) :
    Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          s.rawDefect s.family) ∨
      ∃ hbound :
          HasCanonicalPositiveTransverseReesCoefficientBound
            s.rawDefect s.family,
        AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
          (s.canonicalPositiveTransverseSectionFrontierState hbound) s := by
  classical
  by_cases hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family
  · right
    refine ⟨hbound, ?_⟩
    change Nonempty
      (CertifiedRamifiedRawDefectSpend
        (s.canonicalPositiveTransverseSectionFrontierState hbound) s)
    exact ⟨s.canonicalPositiveTransverseSectionFrontierState_ramifiedSpend
      hpositive hbound⟩
  · left
    exact canonicalPositiveTransverseReesLowLayer_of_not_bound
      hpositive hbound

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- **A19.22 source-facing positive-clock adapter.**

Run the positive transverse Rees frontier on the actual represented terminal
state.  If a low layer appears, retain its concrete family-level witness.  If
coefficient clearing succeeds, compose the resulting factor-two spend with
`sourcePresentation`; the output is then a certified ramified raw-defect spend
from the genuine trace state `source`, not merely from its represented
presentation.
-/
theorem positiveTransverseRees_lowLayer_or_sourceRamifiedSpend
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hpositive : 0 < T.presentedState.rawDefect) :
    Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          T.presentedState.rawDefect T.presentedState.family) ∨
      ∃ hbound :
          HasCanonicalPositiveTransverseReesCoefficientBound
            T.presentedState.rawDefect T.presentedState.family,
        AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
          (T.presentedState.canonicalPositiveTransverseSectionFrontierState hbound)
          source := by
  rcases T.presentedState.canonicalPositiveTransverseRees_lowLayer_or_ramifiedSpend
      hpositive with hlow | hspend
  · exact Or.inl hlow
  · right
    rcases hspend with ⟨hbound, hspend⟩
    exact ⟨hbound, T.sourcePresentation.then_spend hspend⟩

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation
