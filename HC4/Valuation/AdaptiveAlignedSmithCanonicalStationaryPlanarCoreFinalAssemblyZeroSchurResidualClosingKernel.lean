import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurClosingSplit
import Mathlib.Tactic

/-!
# Final assembly A17.15: residual zero-Schur closing is a genuine kernel crossing

A17.14 leaves one positive-residual closing object: an exact residual
rank-one Schur clock whose first transverse order is exactly its remaining
determinant defect.  The old closing interface only retained the weak
alternative

    offDiag(defect) != 0 or kernel(defect) != 0.

At exact determinant closure the second alternative is in fact forced.  The
coefficient of the determinant at the closing order is nonzero, while the
first-departure linearisation identifies that coefficient with

    leading * kernel(defect).

Since the rank-one leading coefficient is nonzero, the kernel coefficient
cannot vanish.

This file records the resulting source-valued kernel crossing and evaluates
it at a source point where it remains nonzero.  Thus the final positive
zero-Schur closing branch no longer carries an ambiguous transverse
coefficient: it carries an honest nonzero kernel-direction curvature event.
No repair state is changed in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- At the exact determinant defect the residual rank-one determinant has a
nonzero coefficient. -/
theorem exactRankOneSchurClockAt_determinant_coeff_defect_ne_zero
    (S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K)) :
    S.series.determinant.coeff S.defect ≠ 0 := by
  rw [S.determinantFactor]
  rw [Polynomial.coeff_mul_X_pow']
  simpa using S.clearingFactor_coeff_zero_ne_zero

/-- **Residual closing is necessarily a kernel crossing.**

The mixed coefficient may also survive at closure, but it cannot be the sole
cause of determinant closure. -/
theorem exactRankOneSchurClockAt_kernel_coeff_firstOrder_ne_zero_of_closing
    (S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
    (hclose : S.firstOrder = S.defect) :
    S.series.kernel.coeff S.firstOrder ≠ 0 := by
  have hdet : S.series.determinant.coeff S.firstOrder ≠ 0 := by
    simpa [hclose] using exactRankOneSchurClockAt_determinant_coeff_defect_ne_zero S
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        S.series.leading * S.series.kernel.coeff S.firstOrder := by
    simpa [FirstRankOneSchurDeparture.determinant,
      RankOneSchurSeries.determinant, ExactRankOneSchurClockAt.firstOrder] using
      (S.series.firstDeparture S.hasTransverse).coeff_order_determinant
  intro hkernel
  apply hdet
  rw [hlin, hkernel]
  simp

/-- Defect-indexed form of the residual closing-kernel statement. -/
theorem exactRankOneSchurClockAt_kernel_coeff_defect_ne_zero_of_closing
    (S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
    (hclose : S.firstOrder = S.defect) :
    S.series.kernel.coeff S.defect ≠ 0 := by
  have h := exactRankOneSchurClockAt_kernel_coeff_firstOrder_ne_zero_of_closing S hclose
  rw [hclose] at h
  exact h

/-- Evaluated kernel-direction coefficient at the exact residual closing
order. -/
noncomputable def zeroSchurResidualClosingKernelValue
    {Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)}
    (D : AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData Z)
    (point : Fin 4 → K) : K :=
  MvPolynomial.eval point
    (D.residualClock.series.kernel.coeff D.residualClock.defect)

/-- Genuine geometric event carried by the positive-residual zero-Schur
closing branch.  The residual Schur kernel coefficient is a nonzero source
polynomial and remains nonzero at the stored source point. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurResidualClosingKernelCrossing
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (D : AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData Z) where
  kernelPolynomial_ne :
    D.residualClock.series.kernel.coeff D.residualClock.defect ≠ 0
  point : Fin 4 → K
  kernelValue_ne : zeroSchurResidualClosingKernelValue D point ≠ 0

/-- Every A17.14 positive-residual closing datum yields an honest nonzero
kernel-direction source event. -/
theorem AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData.exists_kernelCrossing
    {Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)}
    (D : AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData Z) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroSchurResidualClosingKernelCrossing Z D) := by
  have hkernel :
      D.residualClock.series.kernel.coeff D.residualClock.defect ≠ 0 :=
    exactRankOneSchurClockAt_kernel_coeff_defect_ne_zero_of_closing
      D.residualClock D.firstOrder_eq_defect
  rcases exists_source_eval_ne_zero_of_ne_zero
      (D.residualClock.series.kernel.coeff D.residualClock.defect)
      hkernel with ⟨point, hpoint⟩
  exact ⟨{
    kernelPolynomial_ne := hkernel
    point := point
    kernelValue_ne := by
      simpa [zeroSchurResidualClosingKernelValue] using hpoint
  }⟩

/-- A17.15 frontier.  The positive-residual closing constructor now retains a
literal nonzero kernel crossing. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroSchurKernelClosingOutcome
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
  | zeroSchurResidualZeroNondegenerate
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit
          P.carrier.chartData.zeroData))
  | zeroSchurResidualKernelClosing
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData
        P.carrier.chartData.zeroData)
      (hcross : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualClosingKernelCrossing
          P.carrier.chartData.zeroData D))
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.15 residual-closing kernel frontier.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreZeroSchurKernelClosingFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroSchurKernelClosingOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreZeroSchurClosingSplitFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | zeroSchurNondegenerateRankTwo P D hexit =>
      exact .zeroSchurNondegenerateRankTwo P D hexit
  | zeroSchurResidualZeroNondegenerate P D =>
      exact .zeroSchurResidualZeroNondegenerate P D
  | zeroSchurResidualRankOneClosing P hD =>
      rcases hD with ⟨D⟩
      exact .zeroSchurResidualKernelClosing P D D.exists_kernelCrossing
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
