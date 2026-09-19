import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalGeometryFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesGlobalDescent
import Mathlib.Tactic

/-!
# Final global/local assembly for the zero strict-low frontier

A19.53 already reduces one canonical Rees-reduced rank-one episode to either
honest global macro progress or an actual zero-clock strict-low blocker.
A19.54--A19.71 and the subsequent codimension-two/top-kernel closure now turn
that local terminal into the complete source-honest `FinalGeometryFrontier`.

This file is the missing assembly splice between those two green chains.

No new local algebra is introduced here.  In particular:

* the global-progress constructor is kept as genuine well-founded progress;
* the local constructor retains the actual reached state and singular terminal;
* no auxiliary Rees order is identified with the zero blocker clock;
* no repair-only transition is promoted to a contradiction;
* no generic JC2 fallback is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Complete local payload remaining when one Rees-reduced rank-one episode
cannot leave by honest global macro progress. -/
structure AdaptiveAlignedSmithCanonicalReachableFinalGeometryData
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  terminal :
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state
  frontier : terminal.FinalGeometryFrontier

/-- Package the now-complete local geometry of one actual zero strict-low
terminal without changing the reached state. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.toReachableFinalGeometryData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    AdaptiveAlignedSmithCanonicalReachableFinalGeometryData
      (K := K) state where
  terminal := T
  frontier := T.finalGeometryFrontier

/-- **Final reached-state assembly.**

The actual endpoint of a canonical Rees-reduced rank-one episode either has a
genuine successor in the already well-founded global macro order, or carries
the complete final source-honest zero-strict-low geometry frontier.

This is the lossless bridge from the global A19.45/A19.53 reduction into the
newly completed A19.55--A19.71 local geometry. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_finalGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalReachableFinalGeometryData
          (K := K) T.trace.reachedRankThree.state) := by
  rcases T.globalProgress_or_zeroStrictLowSingularTerminal hsrepair with
    hprogress | hterminal
  · exact Or.inl hprogress
  · rcases hterminal with ⟨Z⟩
    exact Or.inr ⟨Z.toReachableFinalGeometryData⟩

/-- Source-facing form of the same splice.  If the reached state exits
globally, compose that exit with the finite raw-defect trace so the recursive
successor is strictly below the incoming source.  Otherwise retain the final
local geometry at the honest reached state. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_from_source_or_finalGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalReachableFinalGeometryData
          (K := K) T.trace.reachedRankThree.state) := by
  rcases T.globalProgress_or_finalGeometry hsrepair with
    hprogress | hgeometry
  · rcases hprogress with ⟨target, htarget⟩
    rcases T.trace.reachedRankThree_eq_or_globalProgress with hEq | htrace
    · exact Or.inl ⟨target, by simpa [hEq] using htarget⟩
    · exact Or.inl
        ⟨target,
          adaptiveAlignedSmithCanonicalGlobalMacroProgress_trans
            htarget htrace⟩
  · exact Or.inr hgeometry

/-- At a genuinely globally terminal incoming rank-one state, the complete
final local geometry is therefore unavoidable.  This is the exact terminal
consumer interface for the final HC4 contradiction theorem. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.finalGeometry_of_no_globalProgress_from_source
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalReachableFinalGeometryData
        (K := K) T.trace.reachedRankThree.state) := by
  rcases T.globalProgress_from_source_or_finalGeometry hsrepair with
    ⟨target, hprogress⟩ | hgeometry
  · exact (hterminal target hprogress).elim
  · exact hgeometry

end

end HC4.Valuation
