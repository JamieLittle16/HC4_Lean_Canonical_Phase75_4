import HC4.Valuation.AdaptiveAlignedSmithCanonicalPacketRankTwoExactZeroSchur
import Mathlib.Tactic

/-!
# A18.4.79: scalar exact zero-Schur clock exposes rank-three geometry

The packet matrix exposure of A18.4.78 produces `ExactZeroSchurFourBlockData K`
on the coefficient field itself.  Its two-stage clock is therefore simpler
than the older A17 source-polynomial version: no source evaluation is needed.

If the residual determinant clock is zero, the constant first Schur tail is
already a nondegenerate binary block.  If residual clock remains and its first
transverse order is preterminal, the kernel coefficient vanishes while the
off-diagonal coefficient is nonzero, giving a block of the form

    [ a  b ]
    [ b  0 ]

with determinant `-b^2 != 0`.

Both alternatives therefore carry actual nondegenerate geometry before the
canonical rank-two -> rank-three repair promotion is attached.  The only
unresolved scalar-clock alternative is the exact positive-residual closing
clock, retained losslessly for the projective closing machinery.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Constant block of the normalised first zero-Schur tail. -/
noncomputable def scalarZeroSchurTailBlock
    (Z : ExactZeroSchurFourBlockData K) : BinarySchurBlock K where
  a := Z.toClock.tailSeries.active.coeff 0
  b := Z.toClock.tailSeries.offDiag.coeff 0
  c := Z.toClock.tailSeries.kernel.coeff 0

/-- First transverse binary block of a residual rank-one Schur clock. -/
noncomputable def scalarRankOneFirstTransverseBlock
    (S : ExactRankOneSchurClockAt K) : BinarySchurBlock K where
  a := S.series.leading
  b := S.series.offDiag.coeff S.firstOrder
  c := S.series.kernel.coeff S.firstOrder

/-- A concrete nondegenerate binary event which licenses the finite
rank-two -> rank-three promotion. -/
structure AdaptiveAlignedSmithCanonicalScalarNondegenerateRankThreeExit
    (complexity : ℕ) : Type (u + 1) where
  block : BinarySchurBlock K
  detCore_ne_zero : block.detCore ≠ 0
  trivialKernel : block.HasTrivialKernel
  rankTwoToRankThree :
    RepairProgress
      (rankTwoRepairState complexity)
      (rankThreeRepairState complexity)
  measure_lt :
    (rankThreeRepairState complexity).measure <
      (rankTwoRepairState complexity).measure

/-- The only scalar exact-zero-Schur alternative not immediately
nondegenerate is an exact positive-residual rank-one closing clock. -/
structure AdaptiveAlignedSmithCanonicalScalarResidualRankOneClosing
    (Z : ExactZeroSchurFourBlockData K) where
  residualClock : ExactRankOneSchurClockAt K
  residualDefect_pos : 0 < Z.toClock.residualDefect
  residualClock_defect_eq : residualClock.defect = Z.toClock.residualDefect
  firstOrder_eq_defect : residualClock.firstOrder = residualClock.defect
  closingCoefficient_ne :
    residualClock.series.offDiag.coeff residualClock.defect ≠ 0 ∨
      residualClock.series.kernel.coeff residualClock.defect ≠ 0

/-- Lossless scalar zero-Schur rank-three frontier. -/
inductive AdaptiveAlignedSmithCanonicalScalarZeroSchurRankThreeOutcome
    (Z : ExactZeroSchurFourBlockData K)
    (complexity : ℕ) : Type (u + 1)
  | rankThree
      (E : AdaptiveAlignedSmithCanonicalScalarNondegenerateRankThreeExit
        (K := K) complexity)
  | residualRankOneClosing
      (C : AdaptiveAlignedSmithCanonicalScalarResidualRankOneClosing Z)

/-- Residual-zero zero-Schur geometry is already a nondegenerate rank-three
entry. -/
noncomputable def scalarRankThreeExit_of_residualZero
    (Z : ExactZeroSchurFourBlockData K)
    (complexity : ℕ)
    (hzero : Z.toClock.residualDefect = 0) :
    AdaptiveAlignedSmithCanonicalScalarNondegenerateRankThreeExit
      (K := K) complexity := by
  let q := scalarZeroSchurTailBlock Z
  have hdet : q.detCore ≠ 0 := by
    simpa [q, scalarZeroSchurTailBlock, BinarySchurBlock.detCore] using
      Z.toClock.tail_constant_det_ne_zero_of_residual_zero hzero
  have htrivial : q.HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero q hdet
  have hrepair :
      RepairProgress
        (rankTwoRepairState complexity)
        (rankThreeRepairState complexity) :=
    rankTwo_to_rankThree_repairProgress complexity
  exact {
    block := q
    detCore_ne_zero := hdet
    trivialKernel := htrivial
    rankTwoToRankThree := hrepair
    measure_lt := repairState_measure_lt_of_progress hrepair
  }

/-- A preterminal residual rank-one clock likewise produces an actual
nondegenerate binary block. -/
noncomputable def scalarRankThreeExit_of_preterminal
    (S : ExactRankOneSchurClockAt K)
    (complexity : ℕ)
    (hpre : S.firstOrder < S.defect) :
    AdaptiveAlignedSmithCanonicalScalarNondegenerateRankThreeExit
      (K := K) complexity := by
  let q := scalarRankOneFirstTransverseBlock S
  have hkernelPoly :
      S.series.kernel.coeff S.firstOrder = 0 :=
    S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre
  have hoff : q.b ≠ 0 := by
    simpa [q, scalarRankOneFirstTransverseBlock] using
      S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
  have hkernel : q.c = 0 := by
    simp [q, scalarRankOneFirstTransverseBlock, hkernelPoly]
  have hdetEq : q.detCore = -(q.b * q.b) := by
    simp [BinarySchurBlock.detCore, hkernel]
  have hdet : q.detCore ≠ 0 := by
    rw [hdetEq]
    exact neg_ne_zero.mpr (mul_ne_zero hoff hoff)
  have htrivial : q.HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero q hdet
  have hrepair :
      RepairProgress
        (rankTwoRepairState complexity)
        (rankThreeRepairState complexity) :=
    rankTwo_to_rankThree_repairProgress complexity
  exact {
    block := q
    detCore_ne_zero := hdet
    trivialKernel := htrivial
    rankTwoToRankThree := hrepair
    measure_lt := repairState_measure_lt_of_progress hrepair
  }

/-- **Exact scalar zero-Schur clock -> nondegenerate rank three or exact
residual closing.** -/
noncomputable def exactScalarZeroSchur_rankThree_or_closing
    (Z : ExactZeroSchurFourBlockData K)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalScalarZeroSchurRankThreeOutcome
      Z complexity := by
  refine Classical.choice ?_
  let E := Z.toClock
  by_cases hres0 : E.residualDefect = 0
  · exact ⟨.rankThree
      (scalarRankThreeExit_of_residualZero Z complexity hres0)⟩
  · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
    rcases E.tail_pivot_of_residual_pos hres with hleft | hright
    · let S := E.toRankOneClockLeft hres hleft
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · exact ⟨.rankThree
          (scalarRankThreeExit_of_preterminal S complexity hpre)⟩
      · have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
        have hfirst :
            S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
          simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
        rw [hfirst] at htrans
        exact ⟨.residualRankOneClosing {
          residualClock := S
          residualDefect_pos := by simpa [E] using hres
          residualClock_defect_eq := rfl
          firstOrder_eq_defect := hclose
          closingCoefficient_ne := htrans
        }⟩
    · let S := E.toRankOneClockRight hres hright
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · exact ⟨.rankThree
          (scalarRankThreeExit_of_preterminal S complexity hpre)⟩
      · have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
        have hfirst :
            S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
          simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
        rw [hfirst] at htrans
        exact ⟨.residualRankOneClosing {
          residualClock := S
          residualDefect_pos := by simpa [E] using hres
          residualClock_defect_eq := rfl
          firstOrder_eq_defect := hclose
          closingCoefficient_ne := htrans
        }⟩

end

end HC4.Valuation
