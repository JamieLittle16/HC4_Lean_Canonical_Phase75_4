import HC4.Valuation.AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingCompleteClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentationFreeExactClock
import Mathlib.Tactic

/-!
# A19.44: retained rank-three geometry is zero defect or honest global progress

The A18.4.107/108 rank-one termination trace deliberately stops when one
complete aligned episode retains rank-three geometry.  By that point the
presented blocker and surviving closures are substantially stronger than the
older A19 residual interfaces:

* a presented blocker is already either literal zero raw defect on the honest
  source or geometry-backed global macro progress;
* a presented surviving endpoint has the same two outcomes, except for the
  canonical Smith-exposure boundary presentation;
* A18.4.38 proves that canonical exposure boundary impossible.

The boundary-origin rank-three packet is itself canonically either blocker or
surviving, so the same finite closure applies there as well.  Consequently a
retained rank-three node with positive raw defect is never terminal: it has an
actual strict global-macro successor.

No presentation is declared progress and no repair-only transition is
invented here.  The theorem only composes already-certified closures.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete source-honest outcome of a retained aligned rank-three packet. -/
inductive AdaptiveAlignedSmithCanonicalRankThreeCompleteOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)

private theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.completeRankThreeOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRankThreeCompleteOutcome RR source := by
  cases D.completeSoundReduction RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | globalProgress target h =>
      exact .globalProgress target h
  | exposureBoundaryPresentation presented E target target_eq hmove =>
      exact E.impossible.elim

/-- **A19.44 complete retained-rank-three closure.**

Every exact blocker, exact surviving wall, or boundary-origin rank-three packet
closes either at literal source raw defect zero or by a certified global macro
successor. -/
theorem AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry.completeClosure
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
      RR source complexity)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRankThreeCompleteOutcome RR source := by
  cases G with
  | exactBlocker D geometry =>
      cases D.completeSoundClosure RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | globalProgress target h =>
          exact .globalProgress target h

  | exactSurviving D geometry =>
      exact D.completeRankThreeOutcome RR complexity hsrepair

  | boundary geometry =>
      cases geometry with
      | blocker D rankThree =>
          cases D.completeSoundClosure RR complexity hsrepair with
          | zeroDefect hzero =>
              exact .zeroDefect hzero
          | globalProgress target h =>
              exact .globalProgress target h
      | surviving D rankThree =>
          exact D.completeRankThreeOutcome RR complexity hsrepair

/-- In particular a positive-defect retained rank-three node has a genuine
strict global-macro successor. -/
theorem AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry.exists_globalProgress_of_pos
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
      RR source complexity)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hpos : 0 < source.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
  cases G.completeClosure hsrepair with
  | zeroDefect hzero =>
      omega
  | globalProgress target h =>
      exact ⟨target, h⟩

end

end HC4.Valuation
