import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
import Mathlib.Tactic

/-!
# A19 direct closure of the zero strict-low terminal

The A19.53 terminal record already stores, on the *same actual reached state*,

* `state.rawDefect = 0`; and
* `state.repair = rankOneRepairState 0`.

A18.4.40 proves that every raw-defect-zero scale-aware family contains literal
nonzero transverse `2 x 2` Hessian geometry, and only after storing that
geometry attaches the canonical rank-one to rank-two same-scale/global macro
transition.

Therefore the A19.53 zero strict-low terminal is not a genuine local terminal:
it has an immediate geometry-backed global successor.  This argument uses the
actual family Hessian.  It does not identify any auxiliary Rees clock with the
zero blocker, does not use `withRepairOnly` without geometry, and does not
project the strict-low carrier to JC2.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- **A19 zero strict-low direct exit.**  The terminal's stored raw-zero and
rank-one hypotheses feed directly into A18.4.40's geometry-bearing rank-two
progress packet. -/
noncomputable def directZeroDefectRankTwoProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankTwoProgress
      canonicalAdaptiveAlignedSmithRepairRanking state 0 :=
  ScaleAwareAdaptiveGeometricRestartState.zeroDefect_globalRankTwoProgress
    canonicalAdaptiveAlignedSmithRepairRanking state 0 T.repair_eq T.source_zero

/-- Proposition-valued global successor form used by the rank-one trace
assembly. -/
theorem exists_globalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state := by
  let P := T.directZeroDefectRankTwoProgress
  exact ⟨P.target, P.globalProgress⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- **A19 rank-one Rees-reduced trace has no local zero terminal.**
Every endpoint of the A19.53 global/local split already has a genuine global
macro successor. -/
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
