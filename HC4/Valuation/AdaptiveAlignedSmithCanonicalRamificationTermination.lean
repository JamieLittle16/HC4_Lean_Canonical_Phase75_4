import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRamifiedSpendClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockStationaryEndgame
import Mathlib.Tactic

/-!
# A17.7: scale-sound ramification termination at the pre-final frontier

A17.6 removes every remaining local stationary-planar-core constructor and
packages each strict exit as

    source --(ramified presentation)--> outer --(same-scale strict)--> target.

The presentation edge must not itself be followed recursively: its scale may
change.  At this point the incoming state is still in the canonical rank-one
repair stage, however, and the finite repair engine already supplies the
intrinsic rank-one-to-rank-two transition at fixed complexity.

This file records that transition directly on the incoming scale-aware state.
`withRepairOnly` changes no geometric datum, no scale, and no raw defect, so
the resulting certificate is a genuine `CertifiedSameScaleEpisodeProgress`.
Consequently every nonterminal constructor of the A17.6 macro frontier can be
closed before its ramified presentation is made recursive.

The exported frontier contains only

* literal zero raw defect; or
* certified same-scale well-founded progress from the actual incoming state.

Thus no fresh ramification factor survives in the recursive interface handed
to the global assembly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The canonical finite-repair escalation can be performed directly on a
rank-one scale-aware state without changing any geometric component.

This is the scale-sound form needed by global recursion: both the parameter
scale and raw defect are literally unchanged, while the finite repair measure
strictly decreases by `rankOne_to_rankTwo_repairProgress`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_sameScaleRankTwoRepairProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedSameScaleEpisodeProgress RR target s := by
  let target := s.withRepairOnly (rankTwoRepairState complexity)
  refine ⟨target, ?_⟩
  apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
  · rfl
  · rfl
  · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
      hsrepair] using rankOne_to_rankTwo_repairProgress complexity

/-- Final ramification-free recursive interface for the stationary planar
core.  There is deliberately no ramified-presentation constructor here. -/
inductive AdaptiveAlignedSmithCanonicalRamificationTerminatedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : s.rawDefect = 0)
  | strictProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hprogress : CertifiedSameScaleEpisodeProgress RR target s)

/-- **A17.7 ramification-termination frontier.**

Consume the completely local-free A17.6 frontier.  A literal zero defect stays
terminal.  Every other constructor is closed on the original incoming state
by the already-certified finite rank-one-to-rank-two repair transition.

In particular, neither a bare ramified spend nor a zero-cost ramified
presentation survives this theorem.  Recursive use of the result therefore
stays at one literal scale and is governed by the existing well-founded
fixed-scale episode order. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalRamificationTerminatedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRamificationTerminatedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreMacroClosedFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | strictMacro outer target hmove hprogress =>
      rcases s.exists_sameScaleRankTwoRepairProgress RR complexity hsrepair with
        ⟨target', hprogress'⟩
      exact .strictProgress target' hprogress'
  | internalPresentation target hmove trace =>
      rcases s.exists_sameScaleRankTwoRepairProgress RR complexity hsrepair with
        ⟨target', hprogress'⟩
      exact .strictProgress target' hprogress'

end

end HC4.Valuation
