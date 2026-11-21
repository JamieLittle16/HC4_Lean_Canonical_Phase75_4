import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankThreeCompleteClosure
import Mathlib.Tactic

/-!
# A19.45: Rees-reduced rank-three closure is zero defect or global progress

A19.34b retains an actual rank-three state after exhausting every successful
positive transverse Rees coefficient bound.  A19.44 subsequently strengthened
the retained rank-three geometry itself: at canonical rank one it is already
either literal source raw defect zero or an honest strict global-macro
successor.

This file composes those facts at the exact reached state of the Rees-reduced
trace.  In particular the two positive low-layer residuals are not terminal
first-contact obligations: positive retained rank-three geometry is global
progress and belongs to the outer well-founded macro recursion.

No global progress edge is inserted into the raw-defect-only rank-one trace.
The theorem merely exposes the correct outer outcome.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The reached state of a Rees-reduced rank-one trace is either at literal
raw defect zero or admits a certified strict successor in the existing global
macro order. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.reachedRankThree_zero_or_globalProgress
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity source)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    T.trace.reachedRankThree.state.rawDefect = 0 ∨
      ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state := by
  have hrepair :
      T.trace.reachedRankThree.state.repair =
        rankOneRepairState complexity :=
    T.reachedRankThree_repair_eq hsrepair
  cases T.trace.reachedRankThree.geometry.completeClosure hrepair with
  | zeroDefect hzero =>
      exact Or.inl hzero
  | globalProgress target h =>
      exact Or.inr ⟨target, h⟩

/-- Positive reached raw defect is therefore never a terminal A19 residual. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress_of_reachedRankThree_pos
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity source)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hpos : 0 < T.trace.reachedRankThree.state.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress
        target T.trace.reachedRankThree.state := by
  rcases T.reachedRankThree_zero_or_globalProgress hsrepair with
    hzero | hprogress
  · omega
  · exact hprogress

/-- Equivalently, any reached state which is terminal for the global macro
order must have literal raw defect zero. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.reachedRankThree_rawDefect_eq_zero_of_no_globalProgress
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity source)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) :
    T.trace.reachedRankThree.state.rawDefect = 0 := by
  rcases T.reachedRankThree_zero_or_globalProgress hsrepair with
    hzero | ⟨target, hprogress⟩
  · exact hzero
  · exact (hterminal target hprogress).elim

end

end HC4.Valuation
