import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
import Mathlib.Tactic

/-!
# Zero-clock strict-low terminals are already global progress

The A19 strict-low terminal retains two facts on the reached scale-aware state
itself:

* the finite repair label is exactly `rankOneRepairState 0`; and
* the raw Hessian defect is exactly zero.

A18.4.40 already proves that every raw-defect-zero state has concrete
transverse rank-two Hessian geometry: if the four relevant transverse minors
all vanished, the full Hessian determinant would vanish, contradicting the
unit determinant forced by raw defect zero.  Once that literal minor is
retained, the existing geometry-carrying rank-one-to-rank-two theorem gives a
certified same-scale global macro successor.

Therefore the strict-low terminal alternative is not terminal at all.  This
module closes it directly at the reached state.  It does not identify any
auxiliary Rees clock with the blocker clock, does not use naked repair-only
progress, and does not invoke generic JC2 or any of the later `qs` local
frontier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- **Zero-clock strict-low terminal closure.**  The retained reached state
already has concrete transverse rank-two Hessian geometry and hence a certified
global macro successor. -/
theorem exists_globalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state := by
  let P :=
    ScaleAwareAdaptiveGeometricRestartState.zeroDefect_globalRankTwoProgress
      canonicalAdaptiveAlignedSmithRepairRanking state 0 T.repair_eq T.source_zero
  exact ⟨P.target, P.globalProgress⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- **Producer-free rank-one Rees trace always exits by honest global
progress.**  A19.53's only residual terminal alternative is consumed by the
zero-defect rank-two geometry already present on the same reached state. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress
        target T.trace.reachedRankThree.state := by
  rcases T.globalProgress_or_zeroStrictLowTerminal hsrepair with
    hprogress | hterminal
  · exact hprogress
  · rcases hterminal with ⟨Z⟩
    exact Z.exists_globalProgress

end

end HC4.Valuation
