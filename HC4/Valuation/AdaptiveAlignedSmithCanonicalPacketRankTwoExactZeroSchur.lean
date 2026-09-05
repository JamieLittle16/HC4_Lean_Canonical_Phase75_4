import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingLosslessRankTwo
import HC4.Valuation.AdaptiveAlignedSmithRankTwoZeroSchurComplete
import Mathlib.Tactic

/-!
# A18.4.78: actual packet-family rank two reaches exact zero-Schur data

The nonrigid `D >= 3` surviving packet retained by A18.4.77 is already an
`AdaptiveRankTwoFamilyContinuation`.  The older matrix-exposure stack was
built for exactly this object:

1. expose the retained integral Smith wall on an honest polynomial family;
2. use packet isolation on that same family; and
3. reindex the packet Hessian to obtain an exact zero-Schur four-block.

This file makes that handoff explicit.  The only alternate branch is literal
zero determinant clock on the retained aligned family.  No repair-only target
is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Lossless result of consuming one geometry-bearing packet continuation. -/
inductive AdaptiveAlignedSmithCanonicalPacketRankTwoExactZeroSchurOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity) : Type (u + 1)
  | zeroDefect
      (hzero : (P.rankOneAnalysisState s W complexity).defect = 0)
  | exactZeroSchur
      (hD : 3 ≤ P.degree)
      (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
        (K := K) s W P complexity R2)
      (Z : ExactZeroSchurFourBlockData K)
      (Z_eq : Z = M.toExactZeroSchurAutomatic s W P complexity R2 hD)

/-- **Packet-family rank two -> zero defect or exact zero-Schur geometry.** -/
noncomputable def
    AdaptiveAlignedSmithRankTwoPacketEndpoint.toExactZeroSchurOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hD : 3 ≤ P.degree) :
    AdaptiveAlignedSmithCanonicalPacketRankTwoExactZeroSchurOutcome
      s W P complexity R2 := by
  refine Classical.choice ?_
  rcases R2.zeroDefect_or_matrixExposure s W P complexity with
    hzero | hM
  · exact ⟨.zeroDefect hzero⟩
  · rcases hM with ⟨M⟩
    let Z := M.toExactZeroSchurAutomatic s W P complexity R2 hD
    exact ⟨.exactZeroSchur hD M Z (by rfl)⟩

end

end HC4.Valuation
