import HC4.Valuation.AdaptiveAlignedSmithRankTwoZeroSchur
import HC4.Valuation.AdaptiveRigidMatrixExposure
import Mathlib.Tactic

/-!
# Automatic exact zero-Schur closure of the aligned rank-two branch

The previous adapter reached `ExactZeroSchurFourBlockData` from an actual
rank-two matrix exposure under one explicit hypothesis:

    0 < M.exposure.defect.

That positivity is not an additional assumption.  The current repository
already proves `quadraticSmithSpecialFiber_hessianDefect_pos`: whenever a
determinant-clock family has special fibre exactly equal to a quadratic
Smith subface, its defect is positive.

An `AdaptiveRankTwoMatrixExposure` carries exactly those hypotheses:

* its exact determinant clock;
* exact equality of its special fibre with the retained Smith subface;
* the quadratic shape of that subface.

Hence the aligned `D >= 3` rank-two branch now reaches the exact zero-Schur
clock with no extra hypothesis.

This file deliberately stops at the exact zero-Schur interface.  Its clock
already contains a strictly positive first Schur order, which is the input
used by the existing kernel/restart machinery.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The actual aligned rank-two matrix exposure necessarily has positive
Hessian defect, because its special fibre is exactly the quadratic Smith
subface retained by the same continuation. -/
theorem
    AdaptiveAlignedSmithRankTwoMatrixEndpoint.exposure_defect_pos
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2) :
    0 < M.exposure.defect := by
  exact
    quadraticSmithSpecialFiber_hessianDefect_pos
      M.exposure.hessianDefect
      M.exposure.specialFiber_eq
      R2.continuation.quadratic

/-- **Automatic `D >= 3` aligned rank-two zero-Schur endpoint.**

There is no remaining positivity assumption: it is forced by the exact
quadratic special fibre of the matrix exposure. -/
noncomputable def
    AdaptiveAlignedSmithRankTwoMatrixEndpoint.toExactZeroSchurAutomatic
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2)
    (hD : 3 ≤ P.degree) :
    ExactZeroSchurFourBlockData K :=
  M.toExactZeroSchur
    s W P complexity R2 hD
    (M.exposure_defect_pos s W P complexity R2)

/-- The resulting exact zero-Schur clock has a genuinely positive first
Schur order.  This is the strict local quantity consumed by the existing
kernel blow-up/restart stack. -/
theorem
    AdaptiveAlignedSmithRankTwoMatrixEndpoint.zeroSchur_firstOrder_pos
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2)
    (hD : 3 ≤ P.degree) :
    0 <
      (M.toExactZeroSchurAutomatic
        s W P complexity R2 hD).toClock.firstOrder := by
  exact
    (M.toExactZeroSchurAutomatic
      s W P complexity R2 hD).toClock.firstOrder_pos

end

end HC4.Valuation
