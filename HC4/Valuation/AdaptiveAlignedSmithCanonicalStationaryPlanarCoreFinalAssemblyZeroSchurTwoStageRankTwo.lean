import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurGeometricRankTwo
import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgame
import Mathlib.Tactic

/-!
# Final assembly A17.12: geometry-carrying two-stage zero-Schur rank-two bridge

A17.11 repaired the first abstraction leak in the final stationary zero-Schur
branch: the finite rank-one-to-rank-two promotion now travels together with
an honest nonzero active `2 x 2` Hessian minor on the retained source chart.

There is a second, older interface which used to forget the *dynamic* reason
for the same promotion.  `ExactZeroSchurFourBlockData.rankTwoProgress_or_closing`
returns either a bare `RepairProgress` or an exact closing alternative.  Its
proof, however, already constructs much more geometry in the progress branch:

* a positive residual determinant clock;
* a canonical residual rank-one Schur clock;
* strict preterminal first transverse order; and
* a nonzero off-diagonal first transverse coefficient.

This file keeps that information.  Thus the zero-Schur branch now has a fully
geometry-carrying two-stage split:

* exact zero-Schur closing; or
* rank-two finite-repair progress accompanied simultaneously by the original
  nonzero active Hessian minor and the residual nonzero mixed Schur layer.

No new Hessian calculation is introduced; this is a lossless repackaging of
the already-green two-stage clock proof.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The geometric content hidden by the old bare zero-Schur rank-two repair
output.  The residual rank-one clock is an actual algebraic clock produced by
the exact zero-Schur block; `firstOrder_lt` and `offDiag_ne` are precisely the
preterminal mixed-layer witness which forces the rank promotion. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) where
  residualClock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K)
  residualDefect_pos : 0 < Z.toClock.residualDefect
  residualClock_defect_eq : residualClock.defect = Z.toClock.residualDefect
  firstOrder_lt : residualClock.firstOrder < residualClock.defect
  offDiag_ne :
    residualClock.series.offDiag.coeff residualClock.firstOrder ≠ 0
  repairProgress :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity)
  measure_lt :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure

/-- Lossless two-stage outcome of an exact zero-Schur block. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurTwoStageOutcome
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) : Prop where
  | preterminalRankTwo
      (D : AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
        Z complexity)
  | closing
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

/-- **Lossless two-stage zero-Schur dichotomy.**

This is the proof of `ExactZeroSchurFourBlockData.rankTwoProgress_or_closing`
with the preterminal clock data retained instead of discarded. -/
theorem exactZeroSchurFourBlock_geometryRankTwo_or_closing
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalZeroSchurTwoStageOutcome Z complexity := by
  let E := Z.toClock
  by_cases hres0 : E.residualDefect = 0
  · exact .closing <| Or.inl
      ⟨hres0, E.tail_constant_det_ne_zero_of_residual_zero hres0⟩
  · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
    rcases E.tail_pivot_of_residual_pos hres with hleft | hright
    · let S := E.toRankOneClockLeft hres hleft
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · have hrepair :
          RepairProgress
            (rankOneRepairState complexity)
            (rankTwoRepairState complexity) :=
          rankOne_to_rankTwo_repairProgress complexity
        exact .preterminalRankTwo {
          residualClock := S
          residualDefect_pos := by simpa [E] using hres
          residualClock_defect_eq := rfl
          firstOrder_lt := hpre
          offDiag_ne := S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
          repairProgress := hrepair
          measure_lt := repairState_measure_lt_of_progress hrepair
        }
      · have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
        have hfirst :
            S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
          simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
        rw [hfirst] at htrans
        exact .closing <| Or.inr
          ⟨S, by simpa [E] using hres, rfl, hclose, htrans⟩
    · let S := E.toRankOneClockRight hres hright
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · have hrepair :
          RepairProgress
            (rankOneRepairState complexity)
            (rankTwoRepairState complexity) :=
          rankOne_to_rankTwo_repairProgress complexity
        exact .preterminalRankTwo {
          residualClock := S
          residualDefect_pos := by simpa [E] using hres
          residualClock_defect_eq := rfl
          firstOrder_lt := hpre
          offDiag_ne := S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
          repairProgress := hrepair
          measure_lt := repairState_measure_lt_of_progress hrepair
        }
      · have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
        have hfirst :
            S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
          simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
        rw [hfirst] at htrans
        exact .closing <| Or.inr
          ⟨S, by simpa [E] using hres, rfl, hclose, htrans⟩

/-- Complete geometry retained in the preterminal rank-two branch of the
stationary zero-Schur packet.  `chartContinuation` carries the honest nonzero
active Hessian minor from A17.11, while `twoStage` carries the later mixed
Schur coefficient which actually witnesses the preterminal rank jump. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ) where
  chartContinuation :
    AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
      RR P complexity
  twoStage :
    AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
      P.carrier.chartData.zeroData complexity

/-- The exact zero-Schur local packet is now either genuinely closing, or its
rank-two continuation carries both independent geometric witnesses. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurSoundContinuationOutcome
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ) : Prop where
  | preterminalRankTwo
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
        RR P complexity)
  | closing
      (h : HasAdaptiveAlignedZeroSchurClosing P.carrier.chartData.zeroData)

/-- Refine the A17.11 continuation through the full two-stage zero-Schur
clock without losing either source-chart or residual-clock geometry. -/
theorem AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem.soundRankTwo_or_closing
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ)
    (D : AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
      RR P complexity) :
    AdaptiveAlignedSmithCanonicalZeroSchurSoundContinuationOutcome
      RR P complexity := by
  cases exactZeroSchurFourBlock_geometryRankTwo_or_closing
      P.carrier.chartData.zeroData complexity with
  | preterminalRankTwo T =>
      exact .preterminalRankTwo {
        chartContinuation := D
        twoStage := T
      }
  | closing h =>
      exact .closing h

/-- Sound A17.12 post-rigid frontier.  The zero-Schur constructor is no longer
just `rank-two geometry + bookkeeping progress`: it is split through the full
exact two-stage clock, retaining the mixed first-layer witness whenever the
rank-two branch is taken. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreSoundTwoStageOutcome
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
  | zeroSchurPreterminalRankTwo
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
        RR P complexity)
  | zeroSchurClosing
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (h : HasAdaptiveAlignedZeroSchurClosing P.carrier.chartData.zeroData)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.12 geometry-complete zero-Schur frontier.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreSoundTwoStageFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreSoundTwoStageOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreSoundPostRigidFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | zeroSchurRankTwo P D =>
      cases P.soundRankTwo_or_closing RR complexity D with
      | preterminalRankTwo T =>
          exact .zeroSchurPreterminalRankTwo P T
      | closing h =>
          exact .zeroSchurClosing P h

end

end HC4.Valuation
