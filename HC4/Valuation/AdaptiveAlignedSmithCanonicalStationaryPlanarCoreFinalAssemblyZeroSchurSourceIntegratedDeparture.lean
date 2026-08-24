import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurCanonicalResidualDeparture
import Mathlib.Tactic

/-!
# Final assembly A17.17: source-integrated canonical zero-Schur departure

A17.16 is the first lossless residual interface: in the positive-residual
closing branch it retains the canonical left/right tail pivot and a nonzero
denominator-free projective coefficient at a physical order strictly below
the outer determinant defect.

The remaining issue is purely one of provenance.  The coefficient in A17.16
is written on the normalised tail obtained after removing the first common
zero-Schur parameter factor.  For the global assembly we must put that event
back on the original honest Hessian chart, rather than recurse on an auxiliary
tail clock.

This file performs exactly that pullback.  Coefficient extraction from

    S = X^e * tail(S)

shows that the `r`th tail coefficient is literally the `(e+r)`th coefficient
of the original raw Schur series.  Hence the canonical A17.16 departure is an
actual nonzero projective departure of the denominator-cleared Schur block of
the retained right-recentered Hessian chart, at the retained physical order

    e + residualDefect < defect.

The resulting certificate also carries the finite rank-one-to-rank-two repair
step, but never by itself: the progress proof is exported only together with
this exact source-chart projective event.  No `withRepairOnly` state is
constructed here and no auxiliary residual clock survives the exported
frontier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Exact tail-to-raw coefficient transport -/

/-- The `r`th active coefficient of the normalised zero-Schur tail is exactly
the `(firstOrder + r)`th coefficient of the original raw Schur series. -/
theorem ExactZeroSchurClock.active_coeff_firstOrder_add_eq_tail
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
    (r : ℕ) :
    E.zeroSeries.series.active.coeff (E.firstOrder + r) =
      E.tailSeries.active.coeff r := by
  change
    E.zeroSeries.series.active.coeff
        (E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer + r) =
      (E.zeroSeries.tailSeries E.hasPositiveEntryLayer).active.coeff r
  rw [E.zeroSeries.active_eq_firstFactor_mul_tail E.hasPositiveEntryLayer]
  rw [Polynomial.coeff_X_pow_mul']
  simp [ZeroSchurSeries.tailSeries]

/-- Off-diagonal analogue of `active_coeff_firstOrder_add_eq_tail`. -/
theorem ExactZeroSchurClock.offDiag_coeff_firstOrder_add_eq_tail
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
    (r : ℕ) :
    E.zeroSeries.series.offDiag.coeff (E.firstOrder + r) =
      E.tailSeries.offDiag.coeff r := by
  change
    E.zeroSeries.series.offDiag.coeff
        (E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer + r) =
      (E.zeroSeries.tailSeries E.hasPositiveEntryLayer).offDiag.coeff r
  rw [E.zeroSeries.offDiag_eq_firstFactor_mul_tail E.hasPositiveEntryLayer]
  rw [Polynomial.coeff_X_pow_mul']
  simp [ZeroSchurSeries.tailSeries]

/-- Kernel analogue of `active_coeff_firstOrder_add_eq_tail`. -/
theorem ExactZeroSchurClock.kernel_coeff_firstOrder_add_eq_tail
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
    (r : ℕ) :
    E.zeroSeries.series.kernel.coeff (E.firstOrder + r) =
      E.tailSeries.kernel.coeff r := by
  change
    E.zeroSeries.series.kernel.coeff
        (E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer + r) =
      (E.zeroSeries.tailSeries E.hasPositiveEntryLayer).kernel.coeff r
  rw [E.zeroSeries.kernel_eq_firstFactor_mul_tail E.hasPositiveEntryLayer]
  rw [Polynomial.coeff_X_pow_mul']
  simp [ZeroSchurSeries.tailSeries]

/-- The raw series of the zero-Schur clock is definitionally the polynomial
Schur series of the exact four-block which generated it. -/
@[simp] theorem ExactZeroSchurFourBlockData.toClock_zeroSeries_series
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) :
    Z.toClock.zeroSeries.series = Z.block.polynomialSchurSeries := by
  rfl

/-- On the retained A17.3F local packet, that raw Schur series is therefore
literally the one belonging to the honest right-recentered Hessian chart. -/
theorem AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem.zeroSchurRawSeries_eq_honestChart
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s) :
    P.carrier.chartData.zeroData.toClock.zeroSeries.series =
      P.carrier.chartData.chart.block.polynomialSchurSeries := by
  rw [ExactZeroSchurFourBlockData.toClock_zeroSeries_series]
  rw [P.carrier.zeroSchurBlock_eq_chartBlock]

/-! ## Original-chart projective departure -/

/-- Physical order, on the unnormalised zero-Schur series, of the canonical
residual closing departure. -/
def zeroSchurCanonicalResidualPhysicalOrder
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) : ℕ :=
  Z.toClock.firstOrder + Z.toClock.residualDefect

/-- Denominator-free left-pivot projective departure polynomial written on the
*original* zero-Schur series rather than on its normalised tail. -/
noncomputable def zeroSchurCanonicalLeftRawDeparturePolynomial
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) :
    MvPolynomial (Fin 4) K :=
  let E := Z.toClock
  let S := E.zeroSeries.series
  let e := E.firstOrder
  let n := zeroSchurCanonicalResidualPhysicalOrder Z
  (S.offDiag.coeff e)^2 * S.active.coeff n -
    2 * S.active.coeff e * S.offDiag.coeff e * S.offDiag.coeff n +
    (S.active.coeff e)^2 * S.kernel.coeff n

/-- Right-axis projective departure polynomial on the original zero-Schur
series. -/
noncomputable def zeroSchurCanonicalRightRawDeparturePolynomial
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) :
    MvPolynomial (Fin 4) K :=
  let E := Z.toClock
  E.zeroSeries.series.active.coeff
    (zeroSchurCanonicalResidualPhysicalOrder Z)

/-- Final source-integrated form of the canonical residual projective event.

Every constructor is attached to the original exact zero-Schur four-block,
retains the canonical pivot, occurs strictly before determinant closure, and
carries the geometry-backed rank-one-to-rank-two repair decrease. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (complexity : ℕ) : Prop
  | left
      (hres : 0 < Z.toClock.residualDefect)
      (hleft : Z.toClock.tailSeries.LeftPivot)
      (rawDeparture_ne : zeroSchurCanonicalLeftRawDeparturePolynomial Z ≠ 0)
      (physicalOrder_lt :
        zeroSchurCanonicalResidualPhysicalOrder Z < Z.toClock.defect)
      (repairProgress :
        RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity))
      (measure_lt :
        (rankTwoRepairState complexity).measure <
          (rankOneRepairState complexity).measure)
  | right
      (hres : 0 < Z.toClock.residualDefect)
      (hright : Z.toClock.tailSeries.RightAxisPivot)
      (rawDeparture_ne : zeroSchurCanonicalRightRawDeparturePolynomial Z ≠ 0)
      (physicalOrder_lt :
        zeroSchurCanonicalResidualPhysicalOrder Z < Z.toClock.defect)
      (repairProgress :
        RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity))
      (measure_lt :
        (rankTwoRepairState complexity).measure <
          (rankOneRepairState complexity).measure)

/-- Pull the A17.16 canonical tail departure back to the original raw Schur
series coefficient-by-coefficient. -/
theorem AdaptiveAlignedSmithCanonicalZeroSchurCanonicalResidualProjectiveDeparture.toSourceIntegrated
    {Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)}
    (D : AdaptiveAlignedSmithCanonicalZeroSchurCanonicalResidualProjectiveDeparture Z)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
      Z complexity := by
  let E := Z.toClock
  have hrepair :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) :=
    rankOne_to_rankTwo_repairProgress complexity
  have hmeasure :
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure :=
    repairState_measure_lt_of_progress hrepair
  cases D with
  | left hres hleft hclose hkernel hraw hphysical =>
      have hA0 :
          E.tailSeries.active.coeff 0 =
            E.zeroSeries.series.active.coeff E.firstOrder := by
        symm
        simpa [E] using HC4.Valuation.ExactZeroSchurClock.active_coeff_firstOrder_add_eq_tail E 0
      have hB0 :
          E.tailSeries.offDiag.coeff 0 =
            E.zeroSeries.series.offDiag.coeff E.firstOrder := by
        symm
        simpa [E] using HC4.Valuation.ExactZeroSchurClock.offDiag_coeff_firstOrder_add_eq_tail E 0
      have hAr :
          E.tailSeries.active.coeff E.residualDefect =
            E.zeroSeries.series.active.coeff
              (E.firstOrder + E.residualDefect) := by
        symm
        exact HC4.Valuation.ExactZeroSchurClock.active_coeff_firstOrder_add_eq_tail E E.residualDefect
      have hBr :
          E.tailSeries.offDiag.coeff E.residualDefect =
            E.zeroSeries.series.offDiag.coeff
              (E.firstOrder + E.residualDefect) := by
        symm
        exact HC4.Valuation.ExactZeroSchurClock.offDiag_coeff_firstOrder_add_eq_tail E E.residualDefect
      have hCr :
          E.tailSeries.kernel.coeff E.residualDefect =
            E.zeroSeries.series.kernel.coeff
              (E.firstOrder + E.residualDefect) := by
        symm
        exact HC4.Valuation.ExactZeroSchurClock.kernel_coeff_firstOrder_add_eq_tail E E.residualDefect
      have hraw' := hraw
      rw [hA0, hB0, hAr, hBr, hCr] at hraw'
      exact .left
        (by simpa [E] using hres)
        (by simpa [E] using hleft)
        (by
          simpa [zeroSchurCanonicalLeftRawDeparturePolynomial,
            zeroSchurCanonicalResidualPhysicalOrder, E] using hraw')
        (by
          simpa [zeroSchurCanonicalResidualPhysicalOrder, E] using hphysical)
        hrepair hmeasure
  | right hres hright hclose hkernel hraw hphysical =>
      have hAr :
          E.tailSeries.active.coeff E.residualDefect =
            E.zeroSeries.series.active.coeff
              (E.firstOrder + E.residualDefect) := by
        symm
        exact HC4.Valuation.ExactZeroSchurClock.active_coeff_firstOrder_add_eq_tail E E.residualDefect
      have hraw' := hraw
      rw [hAr] at hraw'
      exact .right
        (by simpa [E] using hres)
        (by simpa [E] using hright)
        (by
          simpa [zeroSchurCanonicalRightRawDeparturePolynomial,
            zeroSchurCanonicalResidualPhysicalOrder, E] using hraw')
        (by
          simpa [zeroSchurCanonicalResidualPhysicalOrder, E] using hphysical)
        hrepair hmeasure

/-! ## A17.17 final local/source frontier -/

/-- After A17.17 no auxiliary residual clock or unintegrated projective tail
survives.  Every zero-Schur nonterminal output is now an explicit
geometry-backed rank-two event on the retained honest chart. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreSourceIntegratedOutcome
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
  | zeroSchurSourceIntegratedProjectiveDeparture
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
        P.carrier.chartData.zeroData complexity)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.17 source-integrability frontier.**  This is the intended last
local/source adapter before global HC4 assembly: the canonical residual
projective branch is transported back to the original honest Schur chart and
is exported only together with genuine finite repair descent. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreSourceIntegratedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreSourceIntegratedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreCanonicalResidualDepartureFrontier
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
  | zeroSchurCanonicalResidualProjectiveDeparture P D =>
      exact .zeroSchurSourceIntegratedProjectiveDeparture P
        (D.toSourceIntegrated complexity)
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
