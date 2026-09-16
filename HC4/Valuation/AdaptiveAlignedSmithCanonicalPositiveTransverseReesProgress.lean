import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesUnramifiedProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionReentry
import Mathlib.Tactic

/-!
# A19.33: every successful positive Rees frontier is an A18 trace edge

A19.32 handles the strict-early moving-section frontier by removing the
artificial factor-two cover and producing an honest same-scale raw-defect
restart.  One endpoint remains: the moving section may survive all the way to
the determinant-closing weight.  In that case A19.21 already constructs a
factor-two presentation whose literal raw Hessian defect is zero.

Although that endpoint changes presentation scale, its raw clock is `0`, so
for a positive incoming clock it is unconditionally smaller as a natural
number.  The A18.4.109 trace constructor requires exactly global macro
progress, strict raw-defect decrease, and unchanged repair metadata; it does
not require scale equality separately.

Thus coefficient clearing success is completely consumed by the existing
A18 raw-defect termination mechanism.  No new recursion or scaled-defect
order is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Every successful positive transverse Rees frontier is a genuine A18
restart edge.**

If the section frontier is strict, use the unramified A19.32 state.  If it
reaches full weight, use the literal zero-raw-defect A19.21 state. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.exists_canonicalPositiveTransverseRees_progress
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < source.rawDefect)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
      source.rawDefect source.family) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source ∧
      target.rawDefect < source.rawDefect ∧
      target.repair = source.repair := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    source.rawDefect source.movingSection
  have hrle : r ≤ source.rawDefect :=
    canonicalPositiveTransverseSectionFrontierWeight_le
      source.rawDefect source.movingSection
  rcases lt_or_eq_of_le hrle with hrlt | hreq
  · exact source.exists_canonicalPositiveTransverseRees_unramifiedProgress
      hpositive hbound (by simpa [r] using hrlt)
  · let target := source.canonicalPositiveTransverseSectionFrontierState hbound
    have hzero : target.rawDefect = 0 := by
      apply (source.canonicalPositiveTransverseSectionFrontierState_rawDefect_zero_iff
        hbound).2
      simpa [r] using hreq
    have hraw : target.rawDefect < source.rawDefect := by
      rw [hzero]
      exact hpositive
    have hrepair : target.repair = source.repair := by
      rfl
    have hprogress :
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
      unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
      rw [hrepair]
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact hraw
    exact ⟨target, hprogress, hraw, hrepair⟩

end

end HC4.Valuation
