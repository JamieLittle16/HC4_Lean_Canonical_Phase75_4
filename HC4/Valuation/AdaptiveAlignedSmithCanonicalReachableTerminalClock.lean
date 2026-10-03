import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
import Mathlib.Tactic

/-!
# A19.5: the HC4 front door reaches only clocks at most six

The unrestricted determinant-one entry does not start the mature A18 recursion
at an arbitrary determinant clock.  A17.8 performs one explicit transverse
Rees re-entry from raw defect zero to raw defect six, and A18.4.109 thereafter
uses only strict natural-valued raw-defect descents.

For final assembly we do not need to name the terminal state obtained by
forgetting the intermediate trace.  It is enough to consume the trace itself:
if its source clock lies below a bound, then every recursive tail does too, and
the terminal node may be discharged by a contradiction supplied only on that
bounded frontier.

This avoids strengthening the final HC4 obligation to arbitrary presented
terminals and retains the actual A18.4.109 trace as the sole termination
mechanism.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A terminal contradiction need only be supplied on a raw-defect interval
containing the trace source.  Strict A18 restart descent propagates that bound
to every tail automatically. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.impossible_of_bounded_presentedTerminal_impossible
    {RR : RepairRanking}
    {complexity bound : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    (hsource : source.rawDefect ≤ bound)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        state.rawDefect ≤ bound →
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity → False) :
    False := by
  induction T with
  | terminal geometry =>
      exact hterminal hsource geometry.toPresentedTerminal
  | restart progress rawDefect_lt repair_eq tail ih =>
      have htarget : _ := le_trans (Nat.le_of_lt rawDefect_lt) hsource
      exact ih htarget

namespace AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

/-- **HC4-reachable trace closure.**

The one-time A17.8 transverse Rees re-entry has raw defect exactly six.  Every
subsequent recursive edge of A18.4.109 strictly lowers raw defect.  Therefore
to contradict the trace issued from a normalized determinant-one collision it
is enough to contradict presented terminals whose source raw defect is at most
six. -/
theorem positiveRankOneTerminationTrace_impossible_of_bounded_terminal
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        state.rawDefect ≤ 6 →
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity → False) :
    False := by
  let T := E.positiveRankOneTerminationTrace RR complexity
  apply T.impossible_of_bounded_presentedTerminal_impossible
  · change (E.positiveReentry complexity).state.rawDefect ≤ 6
    rw [E.positiveReentry_rawDefect]
  · exact hterminal

end AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

end

end HC4.Valuation
