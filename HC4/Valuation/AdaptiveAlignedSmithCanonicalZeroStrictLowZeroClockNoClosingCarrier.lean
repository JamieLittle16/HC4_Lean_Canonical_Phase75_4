import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBlocker
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerCausality
import Mathlib.Tactic

/-!
# Zero-clock strict-low blockers cannot enter the direct-closing carrier

The mature direct-closing Schur machinery is a positive-clock construction.
For any genuine `AdaptiveAlignedSmithRankOneClosingSourceCarrier`, the least
positive actual source layer is positive and causality proves that it occurs
no later than the determinant-closing order.

At the A19 zero-strict-low endpoint that determinant clock is literally zero.
Consequently no direct-closing carrier can exist there.  This is a soundness
guard for the final HC4 seam: the zero-clock endpoint cannot be discharged by
silently reusing the positive-clock direct-closing pipeline.

No JC2 input, repair promotion, or terminal cocharacter is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithBlockerEndpoint

/-- A rank-one direct-closing source carrier is impossible when its honest
aligned determinant clock is zero. -/
theorem noClosingSourceCarrier_of_defect_eq_zero
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hzero : B.aligned.endpoint.defect = 0) :
    ¬ Nonempty (AdaptiveAlignedSmithRankOneClosingSourceCarrier B) := by
  intro hC
  rcases hC with ⟨C⟩
  have hpos : 0 < C.firstActualLayerOrder :=
    C.firstActualLayerOrder_pos
  have hle : C.firstActualLayerOrder ≤ B.aligned.endpoint.defect :=
    C.firstActualLayerOrder_le_defect
  rw [hzero] at hle
  omega

end AdaptiveAlignedSmithBlockerEndpoint

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- The actual strict-low blocker reconstructed from the retained support
exponent cannot be fed into the positive-clock direct-closing carrier.

The reconstructed blocker has the same aligned endpoint as the represented
blocker, while `zeroClockFirstContactPacket` proves that endpoint clock is
zero. -/
theorem strictLowBlocker_noClosingSourceCarrier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    ¬ Nonempty
      (AdaptiveAlignedSmithRankOneClosingSourceCarrier
        (T.blocker.strictLowBlocker T.exponent T.mem T.pattern)) := by
  let B := T.blocker.strictLowBlocker T.exponent T.mem T.pattern
  have hzero : B.aligned.endpoint.defect = 0 := by
    dsimp [B]
    rw [T.blocker.strictLowBlocker_aligned]
    exact T.zeroClockFirstContactPacket.2.1
  exact B.noClosingSourceCarrier_of_defect_eq_zero hzero

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

end

end HC4.Valuation
