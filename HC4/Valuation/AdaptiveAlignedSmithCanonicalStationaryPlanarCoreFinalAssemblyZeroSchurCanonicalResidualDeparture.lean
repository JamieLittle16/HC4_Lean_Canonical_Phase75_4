import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurResidualClosingKernel
import HC4.Newton.SchurTangentialRawRay
import Mathlib.Tactic

/-!
# Final assembly A17.16: canonical residual zero-Schur projective departure

A17.14/A17.15 exposed the positive-residual zero-Schur closing coefficient,
but the old proposition `HasAdaptiveAlignedZeroSchurClosing` had already
forgotten which of the two canonical tail pivots produced the residual
rank-one clock.  Consequently the residual clock exported by A17.15 is only
an existential clock with the correct defect; it is not definitionally tied
to the honest zero-Schur tail.

That loss of provenance is too weak for the final source-level adapter.  This
file reruns the two-stage clock directly on the retained exact zero-Schur
four-block and keeps the canonical left/right alignment.

For positive residual defect there are now only two possibilities:

* the canonical residual clock is preterminal, in which case the already-green
  A17.12/A17.13 nondegenerate rank-two exit is reconstructed; or
* the canonical residual clock closes.  A17.15 forces its aligned kernel
  coefficient to be nonzero.  Pulling that coefficient back through the
  explicit left/right alignment gives a denominator-free nonzero polynomial
  on the *raw normalised zero-Schur tail*.  Its physical order

      firstZeroSchurOrder + residualDefect

  is strictly below the outer determinant defect.

Thus the exported closing branch is no longer an arbitrary residual clock: it
is a canonical raw-Schur projective departure attached to the exact honest
Hessian chart, with its pivot and preclosing physical order retained.

No repair state is relabelled in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The residual closing layer occurs at a physical raw-Schur order strictly
below the outer determinant-closing order. -/
theorem exactZeroSchurClock_firstOrder_add_residualDefect_lt_defect
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K)) :
    E.firstOrder + E.residualDefect < E.defect := by
  have hle := E.twice_firstOrder_le_defect
  have hpos := E.firstOrder_pos
  unfold ExactZeroSchurClock.residualDefect
  omega

/-- Canonical source-safe projective departure of the positive residual
zero-Schur tail.  The constructors retain the actual pivot used by the
canonical two-stage clock.

In the left-pivot case `rawDeparture_ne` is exactly the raw coefficient whose
value becomes the aligned kernel coefficient after the constant congruence.
In the right-axis case the aligned kernel is literally the raw active entry. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurCanonicalResidualProjectiveDeparture
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) : Prop
  | left
      (hres : 0 < Z.toClock.residualDefect)
      (hleft : Z.toClock.tailSeries.LeftPivot)
      (hclose :
        (Z.toClock.toRankOneClockLeft hres hleft).firstOrder =
          (Z.toClock.toRankOneClockLeft hres hleft).defect)
      (kernel_ne :
        (Z.toClock.toRankOneClockLeft hres hleft).series.kernel.coeff
          Z.toClock.residualDefect ≠ 0)
      (rawDeparture_ne :
        (Z.toClock.tailSeries.offDiag.coeff 0)^2 *
              Z.toClock.tailSeries.active.coeff Z.toClock.residualDefect -
            2 * Z.toClock.tailSeries.active.coeff 0 *
              Z.toClock.tailSeries.offDiag.coeff 0 *
              Z.toClock.tailSeries.offDiag.coeff Z.toClock.residualDefect +
            (Z.toClock.tailSeries.active.coeff 0)^2 *
              Z.toClock.tailSeries.kernel.coeff Z.toClock.residualDefect ≠ 0)
      (physicalOrder_lt :
        Z.toClock.firstOrder + Z.toClock.residualDefect < Z.toClock.defect)
  | right
      (hres : 0 < Z.toClock.residualDefect)
      (hright : Z.toClock.tailSeries.RightAxisPivot)
      (hclose :
        (Z.toClock.toRankOneClockRight hres hright).firstOrder =
          (Z.toClock.toRankOneClockRight hres hright).defect)
      (kernel_ne :
        (Z.toClock.toRankOneClockRight hres hright).series.kernel.coeff
          Z.toClock.residualDefect ≠ 0)
      (rawDeparture_ne :
        Z.toClock.tailSeries.active.coeff Z.toClock.residualDefect ≠ 0)
      (physicalOrder_lt :
        Z.toClock.firstOrder + Z.toClock.residualDefect < Z.toClock.defect)

/-- Lossless canonical positive-residual classification.  Unlike the old
`HasAdaptiveAlignedZeroSchurClosing`, the closing constructor retains the
actual tail pivot and therefore remains attached to the raw zero-Schur
series. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurCanonicalPositiveResidualOutcome
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) : Prop
  | preterminalRankTwo
      (D : AdaptiveAlignedSmithCanonicalZeroSchurPreterminalRankTwoClockData
        Z complexity)
  | projectiveClosing
      (D : AdaptiveAlignedSmithCanonicalZeroSchurCanonicalResidualProjectiveDeparture Z)

/-- Rerun the positive-residual two-stage clock without forgetting the
left/right pivot. -/
theorem exactZeroSchurFourBlock_canonicalPositiveResidual_rankTwo_or_projectiveClosing
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ)
    (hres : 0 < Z.toClock.residualDefect) :
    AdaptiveAlignedSmithCanonicalZeroSchurCanonicalPositiveResidualOutcome
      Z complexity := by
  let E := Z.toClock
  have hresE : 0 < E.residualDefect := by
    simpa [E] using hres
  have hphysical : E.firstOrder + E.residualDefect < E.defect :=
    exactZeroSchurClock_firstOrder_add_residualDefect_lt_defect E
  rcases E.tail_pivot_of_residual_pos hresE with hleft | hright
  · let S := E.toRankOneClockLeft hresE hleft
    rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
    · have hrepair :
          RepairProgress
            (rankOneRepairState complexity)
            (rankTwoRepairState complexity) :=
        rankOne_to_rankTwo_repairProgress complexity
      exact .preterminalRankTwo {
        residualClock := S
        residualDefect_pos := by simpa [E] using hresE
        residualClock_defect_eq := rfl
        firstOrder_lt := hpre
        offDiag_ne := S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
        repairProgress := hrepair
        measure_lt := repairState_measure_lt_of_progress hrepair
      }
    · have hkernelS : S.series.kernel.coeff S.defect ≠ 0 :=
        exactRankOneSchurClockAt_kernel_coeff_defect_ne_zero_of_closing S hclose
      have hkernel :
          (E.toRankOneClockLeft hresE hleft).series.kernel.coeff
            E.residualDefect ≠ 0 := by
        simpa [S, ExactZeroSchurClock.toRankOneClockLeft] using hkernelS
      have haligned :
          (E.tailSeries.alignLeft hleft).kernel.coeff E.residualDefect ≠ 0 := by
        simpa [ExactZeroSchurClock.toRankOneClockLeft] using hkernel
      have hraw :
          (E.tailSeries.offDiag.coeff 0)^2 *
                E.tailSeries.active.coeff E.residualDefect -
              2 * E.tailSeries.active.coeff 0 *
                E.tailSeries.offDiag.coeff 0 *
                E.tailSeries.offDiag.coeff E.residualDefect +
              (E.tailSeries.active.coeff 0)^2 *
                E.tailSeries.kernel.coeff E.residualDefect ≠ 0 := by
        rw [E.tailSeries.alignLeft_kernel_coeff hleft E.residualDefect] at haligned
        exact haligned
      exact .projectiveClosing <| .left
        (by simpa [E] using hresE)
        (by simpa [E] using hleft)
        (by simpa [E, S] using hclose)
        (by simpa [E] using hkernel)
        (by simpa [E] using hraw)
        (by simpa [E] using hphysical)
  · let S := E.toRankOneClockRight hresE hright
    rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
    · have hrepair :
          RepairProgress
            (rankOneRepairState complexity)
            (rankTwoRepairState complexity) :=
        rankOne_to_rankTwo_repairProgress complexity
      exact .preterminalRankTwo {
        residualClock := S
        residualDefect_pos := by simpa [E] using hresE
        residualClock_defect_eq := rfl
        firstOrder_lt := hpre
        offDiag_ne := S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
        repairProgress := hrepair
        measure_lt := repairState_measure_lt_of_progress hrepair
      }
    · have hkernelS : S.series.kernel.coeff S.defect ≠ 0 :=
        exactRankOneSchurClockAt_kernel_coeff_defect_ne_zero_of_closing S hclose
      have hkernel :
          (E.toRankOneClockRight hresE hright).series.kernel.coeff
            E.residualDefect ≠ 0 := by
        simpa [S, ExactZeroSchurClock.toRankOneClockRight] using hkernelS
      have haligned :
          (E.tailSeries.alignRight hright).kernel.coeff E.residualDefect ≠ 0 := by
        simpa [ExactZeroSchurClock.toRankOneClockRight] using hkernel
      have hraw : E.tailSeries.active.coeff E.residualDefect ≠ 0 := by
        simpa [BinarySchurPolynomialSeries.alignRight] using haligned
      exact .projectiveClosing <| .right
        (by simpa [E] using hresE)
        (by simpa [E] using hright)
        (by simpa [E, S] using hclose)
        (by simpa [E] using hkernel)
        (by simpa [E] using hraw)
        (by simpa [E] using hphysical)

/-- A17.16 frontier.  The arbitrary existential residual clock from A17.15 is
not exported.  We rerun the canonical tail classification.  If that canonical
clock is preterminal we reconstruct the already-green geometry-backed
nondegenerate rank-two exit; otherwise we retain an exact raw-tail projective
departure with its physical preclosing order. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCanonicalResidualDepartureOutcome
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
  | zeroSchurCanonicalResidualProjectiveDeparture
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurCanonicalResidualProjectiveDeparture
        P.carrier.chartData.zeroData)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.16 canonical residual-departure frontier.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreCanonicalResidualDepartureFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCanonicalResidualDepartureOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreZeroSchurKernelClosingFrontier
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
  | zeroSchurResidualKernelClosing P D hcross =>
      cases exactZeroSchurFourBlock_canonicalPositiveResidual_rankTwo_or_projectiveClosing
          P.carrier.chartData.zeroData complexity D.residualDefect_pos with
      | preterminalRankTwo T =>
          rcases P.exists_geometryCarryingRankTwoContinuation
              RR complexity hsrepair with ⟨C⟩
          let sound : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
              RR P complexity := {
            chartContinuation := C
            twoStage := T
          }
          exact .zeroSchurNondegenerateRankTwo P sound
            sound.exists_nondegenerateRankTwoExit
      | projectiveClosing hdeparture =>
          exact .zeroSchurCanonicalResidualProjectiveDeparture P hdeparture
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
