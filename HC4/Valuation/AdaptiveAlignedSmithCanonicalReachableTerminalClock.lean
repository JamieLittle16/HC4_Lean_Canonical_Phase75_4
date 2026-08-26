import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
import Mathlib.Tactic

/-!
# A19.5: the HC4 front door reaches only clocks at most six

The unrestricted determinant-one entry does not start the mature A18 recursion
at an arbitrary determinant clock.  A17.8 performs one explicit transverse
Rees re-entry from raw defect zero to raw defect six, and A18.4.109 then uses
only strict natural-valued raw-defect descents.

This file retains that quantitative information through the complete finite
termination trace.  It is deliberately trace-facing: no terminal geometry is
reinterpreted and no new endpoint assumption is introduced.

Consequently every presented terminal actually reachable from an unrestricted
HC4 collision has raw defect at most six.  Later JC2-facing assembly may thus
work on this reachable seven-clock frontier rather than the much stronger
class of all abstract presented terminals.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The terminal state of a finite rank-one trace never has larger raw defect
than its source.  Every recursive edge stored by A18.4.109 is a strict raw
natural-number descent. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree_rawDefect_le_source
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    T.reachedRankThree.state.rawDefect ≤ source.rawDefect := by
  induction T with
  | terminal geometry =>
      exact Nat.le_refl _
  | restart progress rawDefect_lt repair_eq tail ih =>
      exact le_trans ih (Nat.le_of_lt rawDefect_lt)

/-- Presented-terminal normalization does not change the reached trace state,
so the same monotonicity bound is available at the final polynomial-facing
interface. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedPresentedRankThree_rawDefect_le_source
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    T.reachedPresentedRankThree.state.rawDefect ≤ source.rawDefect := by
  simpa [AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedPresentedRankThree,
    AdaptiveAlignedSmithCanonicalReachedRankThree.toPresentedTerminal] using
    T.reachedRankThree_rawDefect_le_source

namespace AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

/-- **HC4-reachable terminal clock bound.**

The one-time A17.8 re-entry has raw defect exactly six.  Every subsequent edge
of the only recursive A18.4.109 trace strictly lowers raw defect.  Hence the
actual presented terminal reached from any normalized determinant-one
collision has raw defect at most six. -/
theorem positiveRankOneTerminationTrace_reachedPresented_rawDefect_le_six
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (E.positiveRankOneTerminationTrace RR complexity).reachedPresentedRankThree.state.rawDefect ≤ 6 := by
  have h :=
    (E.positiveRankOneTerminationTrace RR complexity).reachedPresentedRankThree_rawDefect_le_source
  simpa using h

end AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

end

end HC4.Valuation
