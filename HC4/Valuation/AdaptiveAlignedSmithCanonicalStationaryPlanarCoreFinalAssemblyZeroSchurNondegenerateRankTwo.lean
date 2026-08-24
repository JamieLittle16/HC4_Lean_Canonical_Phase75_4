import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurTwoStageRankTwo
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurProjectiveWedgeConstancy
import HC4.Newton.RankOnePacketReentry
import Mathlib.Tactic

/-!
# Final assembly A17.13: nondegenerate first transverse rank-two exit

A17.12 retains the exact residual rank-one Schur clock in the preterminal
zero-Schur branch.  At its first transverse order `e < defect`, the existing
clock algebra says that the kernel coefficient vanishes, whereas the
mixed/off-diagonal coefficient is nonzero.

Over the characteristic-zero source field we may evaluate that nonzero
four-variable coefficient at a source point where it remains nonzero.  The
resulting concrete symmetric binary block therefore has the form

    [ a  b ]
    [ b  0 ]

with `b != 0`, hence determinant core `-b^2 != 0`.  This file records that
actual nondegenerate block, its trivial-kernel consequence, and the associated
finite rank-two-to-rank-three repair bookkeeping in one certificate.

The important point is soundness: the repair promotion is no longer exported
without the algebraic event which justifies it.  No `withRepairOnly` target is
manufactured here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Evaluate the first preterminal transverse Schur coefficient at a source
point.  A17.12 proves that its off-diagonal polynomial is nonzero and its
kernel polynomial is zero. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation.firstTransverseBlock
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
      RR P complexity)
    (point : Fin 4 → K) : BinarySchurBlock K where
  a := MvPolynomial.eval point
    (D.twoStage.residualClock.series.active.coeff
      D.twoStage.residualClock.firstOrder)
  b := MvPolynomial.eval point
    (D.twoStage.residualClock.series.offDiag.coeff
      D.twoStage.residualClock.firstOrder)
  c := MvPolynomial.eval point
    (D.twoStage.residualClock.series.kernel.coeff
      D.twoStage.residualClock.firstOrder)

/-- Genuine nondegenerate geometry at the first transverse coefficient of the
A17.12 preterminal rank-two branch.  This is data-valued because it stores the
source evaluation point. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ)
    (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
      RR P complexity) where
  point : Fin 4 → K
  offDiag_ne : (D.firstTransverseBlock point).b ≠ 0
  kernel_eq_zero : (D.firstTransverseBlock point).c = 0
  detCore_ne_zero : (D.firstTransverseBlock point).detCore ≠ 0
  trivialKernel : (D.firstTransverseBlock point).HasTrivialKernel
  rankTwoToRankThree :
    RepairProgress
      (rankTwoRepairState complexity)
      (rankThreeRepairState complexity)
  measure_lt :
    (rankThreeRepairState complexity).measure <
      (rankTwoRepairState complexity).measure

/-- The preterminal residual Schur clock contains an actual nondegenerate
binary first-transverse block.

This is the geometry which was missing from the old naked `2 -> 3` repair
step: the off-diagonal first coefficient survives at some source point, the
kernel coefficient is identically zero, and the evaluated determinant is
therefore `-b^2`. -/
theorem AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation.exists_nondegenerateRankTwoExit
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
      RR P complexity) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
        RR P complexity D) := by
  let B : MvPolynomial (Fin 4) K :=
    D.twoStage.residualClock.series.offDiag.coeff
      D.twoStage.residualClock.firstOrder
  have hB : B ≠ 0 := by
    simpa [B] using D.twoStage.offDiag_ne
  rcases exists_source_eval_ne_zero_of_ne_zero B hB with ⟨point, hpoint⟩

  have hkernelPoly :
      D.twoStage.residualClock.series.kernel.coeff
          D.twoStage.residualClock.firstOrder = 0 :=
    HC4.Newton.ExactRankOneSchurClockAt.kernel_coeff_firstOrder_eq_zero_of_preterminal
      D.twoStage.residualClock D.twoStage.firstOrder_lt

  let q : BinarySchurBlock K := D.firstTransverseBlock point
  have hoff : q.b ≠ 0 := by
    simpa [q,
      AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation.firstTransverseBlock,
      B] using hpoint
  have hkernel : q.c = 0 := by
    simp [q,
      AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation.firstTransverseBlock,
      hkernelPoly]
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

  exact ⟨{
    point := point
    offDiag_ne := by simpa [q] using hoff
    kernel_eq_zero := by simpa [q] using hkernel
    detCore_ne_zero := by simpa [q] using hdet
    trivialKernel := by simpa [q] using htrivial
    rankTwoToRankThree := hrepair
    measure_lt := repairState_measure_lt_of_progress hrepair
  }⟩

/-- A17.13 frontier: the A17.12 preterminal constructor is replaced by an
explicit nondegenerate first-transverse rank-two exit.  The exact closing
branch is left untouched for the next closing pass. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreNondegenerateRankTwoOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | zeroSchurNondegenerateRankTwo
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
        RR P complexity)
      (hexit : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
          RR P complexity D))
  | zeroSchurClosing
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (h : HasAdaptiveAlignedZeroSchurClosing P.carrier.chartData.zeroData)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.13 nondegenerate-rank-two frontier.**

No bare preterminal rank-two repair survives this theorem.  Whenever the
A17.12 two-stage clock takes that branch, the frontier exports a concrete
source evaluation at which the first transverse binary Schur block has
nonzero determinant and trivial kernel. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreNondegenerateRankTwoFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreNondegenerateRankTwoOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreSoundTwoStageFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | zeroSchurPreterminalRankTwo P D =>
      exact .zeroSchurNondegenerateRankTwo P D D.exists_nondegenerateRankTwoExit
  | zeroSchurClosing P h =>
      exact .zeroSchurClosing P h
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
