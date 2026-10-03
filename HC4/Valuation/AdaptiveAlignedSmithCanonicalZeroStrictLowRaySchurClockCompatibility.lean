import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import HC4.Valuation.AdaptiveAlignedSmithClosingChartProvenance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockDispatcher

/-!
# Ray clock compatibility at the reached zero-clock terminal

The auxiliary ray reverse Rees has positive determinant defect. The retained
terminal blocker has defect zero. Consequently the ray clock cannot be reused
as a clock on the original blocker: in fact no exact rank-one Schur clock on
that blocker exists. A ray departure therefore needs a new certified source
transition and a terminal-exclusion consumer; the stationary `ofGeometry`
adapter is not such a transition.
-/
namespace HC4.Valuation
noncomputable section
open HC4.Newton
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- An exact positive-transverse clock cannot belong to the retained zero
clock blocker, regardless of which Hessian chart is proposed. -/
theorem no_exactRankOneSchurClock
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData (K := K) state)
    (S : AdaptiveAlignedExactRankOneSchurClock T.blocker.blocker.aligned.endpoint) :
    False := by
  have hz := T.zeroClockFirstContactPacket.2.1
  have hp := S.firstOrder_pos
  have hl := S.firstOrder_le_defect
  omega

/-- In particular the honest-chart input of `schurPreterminal` cannot be
constructed on this original blocker. This does not exclude an auxiliary ray
clock, which has a different, positive defect. -/
theorem no_recenteredRankOneSchurChart
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData (K := K) state)
    (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData T.blocker.blocker) :
    False :=
  T.no_exactRankOneSchurClock D.clock

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}

/-- The positive ray defect is not the retained blocker's defect. -/
theorem QsOtherFacetRayReverseReesPackage.defect_ne_terminalBlocker_defect
    (R : QsOtherFacetRayReverseReesPackage C) :
    4 * R.level - 2 * ∑ i : Fin 4, R.weight i ≠
      T.terminal.blocker.blocker.aligned.endpoint.defect := by
  have hz := T.terminal.zeroClockFirstContactPacket.2.1
  have hp := R.defect_pos
  omega

/-- Ramifying the zero-clock source cannot supply the positive ray clock
needed by a stationary exact-clock presentation. -/
theorem QsOtherFacetRayReverseReesPackage.defect_ne_ramified_source_defect
    (R : QsOtherFacetRayReverseReesPackage C) (ramification : ℕ) :
    4 * R.level - 2 * ∑ i : Fin 4, R.weight i ≠
      ramification * state.rawDefect := by
  rw [T.terminal.source_zero, mul_zero]
  exact Nat.ne_of_gt R.defect_pos

/-- No target carrying the positive ray clock is a certified ramified internal
presentation of the original zero-clock state. Thus the existing source
presentation certificate cannot be obtained just by changing the target family. -/
theorem QsOtherFacetRayReverseReesPackage.no_ramifiedInternalMove_to_ray_defect
    (R : QsOtherFacetRayReverseReesPackage C)
    (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hraw : target.rawDefect = 4 * R.level - 2 * ∑ i : Fin 4, R.weight i) :
    ¬ HasCertifiedRamifiedEpisodeInternalMove target state := by
  rintro ⟨h⟩
  exact R.defect_ne_ramified_source_defect h.ramification (hraw.symm.trans h.raw_eq)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
