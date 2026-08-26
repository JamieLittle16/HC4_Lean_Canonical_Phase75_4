import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalImpossible
import Mathlib.Tactic

/-!
# A18.5.75: consume the well-founded rank-one termination trace

A18.4.109 already performed the only recursion needed in the canonical
rank-one endgame.  Its trace has exactly two constructors:

* `terminal`, carrying complete rank-three geometry; and
* `restart`, carrying a strict raw-defect successor and a tail trace.

Consequently, once complete terminal geometry has been shown impossible,
there is no second termination argument to prove.  The trace is consumed by
ordinary structural elimination: a restart is impossible precisely because
its stored tail is impossible, while a terminal is discharged by the supplied
terminal contradiction.

This file deliberately introduces no measure, no clock and no recursive
definition.  It isolates the final logical splice so that the remaining
mathematics is exactly the hypothesis-free impossibility of the normalized
presented terminal.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **A18.5.75 — structural collapse of the finite rank-one trace.**

If every normalized presented terminal carrying the complete rank-three
geometry is contradictory, then every A18.4.109 termination trace is
contradictory.  The strict raw-defect certificates stored on restart edges are
not used again here: they were already used to construct the finite trace. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.impossible_of_presentedTerminal_impossible
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity → False) :
    False := by
  induction trace with
  | terminal geometry =>
      exact hterminal geometry.toPresentedTerminal
  | restart progress rawDefect_lt repair_eq tail ih =>
      exact ih

/-- Equivalent carrier-facing form.  This is often the thinnest consumer for
A18.5.74, since every presented terminal already has its canonical singular
carrier and all determinant-clock bookkeeping has been hidden there. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.impossible_of_singularCarrier_impossible
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    (hcarrier :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
        {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity},
        AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T → False) :
    False := by
  induction trace with
  | terminal geometry =>
      let T := geometry.toPresentedTerminal
      exact hcarrier T.singularCarrier
  | restart progress rawDefect_lt repair_eq tail ih =>
      exact ih

/-- State-facing final splice.  Once terminal geometry is impossible, the
canonical rank-one state itself is impossible.  The only well-founded
recursion is the already-constructed `rankOneTerminationTrace`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.rankOne_impossible_of_presentedTerminal_impossible
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity → False) :
    False := by
  exact
    (source.rankOneTerminationTrace RR complexity hsrepair)
      .impossible_of_presentedTerminal_impossible hterminal

/-- Carrier-facing state form, ready for the A18.5.74 terminal rigidity
constructor. -/
theorem ScaleAwareAdaptiveGeometricRestartState.rankOne_impossible_of_singularCarrier_impossible
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hcarrier :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
        {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity},
        AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T → False) :
    False := by
  exact
    (source.rankOneTerminationTrace RR complexity hsrepair)
      .impossible_of_singularCarrier_impossible hcarrier

end

end HC4.Valuation
