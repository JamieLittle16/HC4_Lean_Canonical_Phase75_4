import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowGlobalProgress
import Mathlib.Tactic

/-!
# Compose rank-one Rees terminal progress back to the incoming source

The zero-strict-low closure now gives a genuine global macro successor from the
actual reached rank-three state of every producer-free rank-one Rees reduced
trace.  Final global recursion needs that strict decrease at the incoming
source, not merely at the trace endpoint.

This module exports the two elementary transport facts needed for that splice:

* transitivity of the already-defined global macro relation; and
* the endpoint of a finite rank-one termination trace is either literally its
  source or is itself globally below that source.

No new progress relation, terminal notion, repair transition, or mathematical
hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The global macro relation is transitive because it is the pullback of the
strict lexicographic order on the canonical global key. -/
theorem adaptiveAlignedSmithCanonicalGlobalMacroProgress_trans
    {a b c : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hab : AdaptiveAlignedSmithCanonicalGlobalMacroProgress a b)
    (hbc : AdaptiveAlignedSmithCanonicalGlobalMacroProgress b c) :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress a c := by
  unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress at hab hbc ⊢
  letI : IsTrans ℕ Nat.lt :=\n    ⟨fun _ _ _ hab hbc => Nat.lt_trans hab hbc⟩
  letI : IsTrans (ℕ × ℕ) (Prod.Lex Nat.lt Nat.lt) :=
    ⟨fun _ _ _ hxy hyz => Prod.Lex.trans hxy hyz⟩
  exact Prod.Lex.trans hab hbc

/-- Forget the intermediate nodes of a finite rank-one termination trace while
retaining the global comparison with its incoming source.  A terminal trace is
literally stationary; otherwise the stored restart edge, composed with the
induction hypothesis, makes the reached state globally smaller. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree_eq_or_globalProgress
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    T.reachedRankThree.state = source ∨
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress
        T.reachedRankThree.state source := by
  induction T with
  | terminal geometry =>
      exact Or.inl rfl
  | @restart source target progress rawDefect_lt repair_eq tail ih =>
      change
        tail.reachedRankThree.state = source ∨
          AdaptiveAlignedSmithCanonicalGlobalMacroProgress
            tail.reachedRankThree.state source
      rcases ih with hEq | hTail
      · right
        rw [hEq]
        exact progress
      · right
        exact adaptiveAlignedSmithCanonicalGlobalMacroProgress_trans hTail progress

/-- **Source-facing producer-free Rees descent.**

The reached rank-three state of every canonical complexity-zero Rees-reduced
trace already has a strict global successor by the zero-strict-low closure.
Composing with the finite raw-defect trace gives a strict global successor of
the original source itself. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress_from_source
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
  obtain ⟨target, hprogress⟩ := T.exists_globalProgress hsrepair
  rcases T.trace.reachedRankThree_eq_or_globalProgress with hEq | htrace
  · refine ⟨target, ?_⟩
    simpa [hEq] using hprogress
  · exact ⟨target,
      adaptiveAlignedSmithCanonicalGlobalMacroProgress_trans hprogress htrace⟩

end

end HC4.Valuation
