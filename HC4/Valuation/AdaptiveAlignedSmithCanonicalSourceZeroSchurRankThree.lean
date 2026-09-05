import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianChart
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurSourceIntegratedDeparture
import Mathlib.Tactic

/-!
# A18.4.83: source-valued exact zero-Schur blocks are completely rank three

A17.12--A17.17 already contain all algebra needed to analyse an exact
zero-Schur block over the source polynomial ring.  Their historical exported
frontiers are tied to one stationary blocker, but the decisive internal data
are generic in

    Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K).

This file exposes that generic content directly.

* residual defect zero: evaluate the nonzero determinant of the normalised
  tail at a source point, obtaining a concrete nondegenerate binary block;
* positive residual, preterminal: evaluate the nonzero mixed first coefficient;
  the kernel coefficient vanishes there, so the block has determinant `-b^2`;
* positive residual, exact closing: retain A17.16/A17.17's denominator-free
  projective coefficient on the original Schur series.  It is a later
  nonzero direction on the kernel line of the first rank-one Schur block.

Only after one of these actual geometric events is present do we attach the
canonical rank-two -> rank-three repair decrease.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- First residual rank-one transverse block evaluated at a source point. -/
noncomputable def sourceZeroSchurFirstTransverseBlock
    {Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
      Z complexity)
    (point : Fin 4 → K) : BinarySchurBlock K where
  a := MvPolynomial.eval point T.residualClock.series.leading
  b := MvPolynomial.eval point
    (T.residualClock.series.offDiag.coeff T.residualClock.firstOrder)
  c := MvPolynomial.eval point
    (T.residualClock.series.kernel.coeff T.residualClock.firstOrder)

/-- Generic nondegenerate rank-three event extracted from a source-valued
zero-Schur block. -/
structure AdaptiveAlignedSmithCanonicalSourceNondegenerateRankThreeExit
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) : Type (u + 1) where
  block : BinarySchurBlock K
  detCore_ne_zero : block.detCore ≠ 0
  trivialKernel : block.HasTrivialKernel
  provenance :
    (∃ hzero : Z.toClock.residualDefect = 0,
      ∃ point : Fin 4 → K,
        block = zeroSchurClosingTailBlockAt Z point) ∨
    (∃ T : AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
        Z complexity,
      ∃ point : Fin 4 → K,
        block = sourceZeroSchurFirstTransverseBlock T point)
  rankTwoToRankThree :
    RepairProgress
      (rankTwoRepairState complexity)
      (rankThreeRepairState complexity)
  measure_lt :
    (rankThreeRepairState complexity).measure <
      (rankTwoRepairState complexity).measure

/-- Projective rank-three event: a later raw Schur coefficient is nonzero in
exactly the kernel direction selected by the first determinant-zero Schur
block. -/
structure AdaptiveAlignedSmithCanonicalSourceProjectiveRankThreeExit
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) : Type (u + 1) where
  departure :
    AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
      Z complexity
  rankTwoToRankThree :
    RepairProgress
      (rankTwoRepairState complexity)
      (rankThreeRepairState complexity)
  measure_lt :
    (rankThreeRepairState complexity).measure <
      (rankTwoRepairState complexity).measure

/-- Complete source-valued zero-Schur rank-three geometry. -/
inductive AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) : Type (u + 1)
  | nondegenerate
      (E : AdaptiveAlignedSmithCanonicalSourceNondegenerateRankThreeExit
        Z complexity)
  | projective
      (E : AdaptiveAlignedSmithCanonicalSourceProjectiveRankThreeExit
        Z complexity)

/-- Residual-zero branch: the normalised tail has a nonzero determinant
polynomial and therefore a nondegenerate scalar evaluation. -/
noncomputable def sourceRankThreeExit_of_residualZero
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ)
    (hzero : Z.toClock.residualDefect = 0) :
    AdaptiveAlignedSmithCanonicalSourceNondegenerateRankThreeExit
      Z complexity := by
  let detPoly : MvPolynomial (Fin 4) K :=
    Z.toClock.tailSeries.active.coeff 0 *
        Z.toClock.tailSeries.kernel.coeff 0 -
      Z.toClock.tailSeries.offDiag.coeff 0 *
        Z.toClock.tailSeries.offDiag.coeff 0
  have hdetPoly : detPoly ≠ 0 := by
    simpa [detPoly] using
      Z.toClock.tail_constant_det_ne_zero_of_residual_zero hzero
  have hex : ∃ point, MvPolynomial.eval point detPoly ≠ 0 :=
    exists_source_eval_ne_zero_of_ne_zero detPoly hdetPoly
  let point : Fin 4 → K := Classical.choose hex
  have hpoint : MvPolynomial.eval point detPoly ≠ 0 :=
    Classical.choose_spec hex
  let q : BinarySchurBlock K := zeroSchurClosingTailBlockAt Z point
  have hdet : q.detCore ≠ 0 := by
    simpa [q, zeroSchurClosingTailBlockAt, BinarySchurBlock.detCore,
      detPoly] using hpoint
  have htrivial : q.HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero q hdet
  have hrepair := rankTwo_to_rankThree_repairProgress complexity
  exact {
    block := q
    detCore_ne_zero := hdet
    trivialKernel := htrivial
    provenance := Or.inl ⟨hzero, point, rfl⟩
    rankTwoToRankThree := hrepair
    measure_lt := repairState_measure_lt_of_progress hrepair
  }

/-- Preterminal positive-residual branch: the first mixed coefficient survives
at some source point and the kernel coefficient is zero. -/
noncomputable def sourceRankThreeExit_of_preterminal
    {Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)}
    (complexity : ℕ)
    (T : AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
      Z complexity) :
    AdaptiveAlignedSmithCanonicalSourceNondegenerateRankThreeExit
      Z complexity := by
  let B : MvPolynomial (Fin 4) K :=
    T.residualClock.series.offDiag.coeff T.residualClock.firstOrder
  have hB : B ≠ 0 := by simpa [B] using T.offDiag_ne
  have hex : ∃ point, MvPolynomial.eval point B ≠ 0 :=
    exists_source_eval_ne_zero_of_ne_zero B hB
  let point : Fin 4 → K := Classical.choose hex
  have hpoint : MvPolynomial.eval point B ≠ 0 :=
    Classical.choose_spec hex
  have hkernelPoly :
      T.residualClock.series.kernel.coeff T.residualClock.firstOrder = 0 :=
    T.residualClock.kernel_coeff_firstOrder_eq_zero_of_preterminal
      T.firstOrder_lt
  let q := sourceZeroSchurFirstTransverseBlock T point
  have hoff : q.b ≠ 0 := by
    simpa [q, sourceZeroSchurFirstTransverseBlock, B] using hpoint
  have hkernel : q.c = 0 := by
    simp [q, sourceZeroSchurFirstTransverseBlock, hkernelPoly]
  have hdetEq : q.detCore = -(q.b * q.b) := by
    simp [BinarySchurBlock.detCore, hkernel]
  have hdet : q.detCore ≠ 0 := by
    rw [hdetEq]
    exact neg_ne_zero.mpr (mul_ne_zero hoff hoff)
  have htrivial : q.HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero q hdet
  have hrepair := rankTwo_to_rankThree_repairProgress complexity
  exact {
    block := q
    detCore_ne_zero := hdet
    trivialKernel := htrivial
    provenance := Or.inr ⟨T, point, rfl⟩
    rankTwoToRankThree := hrepair
    measure_lt := repairState_measure_lt_of_progress hrepair
  }

/-- **Every source-valued exact zero-Schur block carries complete rank-three
geometry.** -/
noncomputable def exactSourceZeroSchur_completeRankThreeGeometry
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
      Z complexity := by
  let E := Z.toClock
  by_cases hres0 : E.residualDefect = 0
  · exact .nondegenerate
      (sourceRankThreeExit_of_residualZero Z complexity hres0)
  · refine Classical.choice ?_
    have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
    cases exactZeroSchurFourBlock_canonicalPositiveResidual_rankTwo_or_projectiveClosing
        Z complexity hres with
    | preterminalRankTwo T =>
        exact ⟨.nondegenerate
          (sourceRankThreeExit_of_preterminal complexity T)⟩
    | projectiveClosing D =>
        have hrepair := rankTwo_to_rankThree_repairProgress complexity
        exact ⟨.projective {
          departure := D.toSourceIntegrated complexity
          rankTwoToRankThree := hrepair
          measure_lt := repairState_measure_lt_of_progress hrepair
        }⟩

end

end HC4.Valuation
