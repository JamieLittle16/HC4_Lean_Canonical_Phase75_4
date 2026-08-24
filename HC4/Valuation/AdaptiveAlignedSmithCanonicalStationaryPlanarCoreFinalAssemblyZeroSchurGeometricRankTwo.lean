import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostRigidElimination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockStationaryEndgame

/-!
# Final assembly A17.11: geometry-carrying zero-Schur rank-two bridge

The A17.10 soundness audit identified one abstraction leak in the provisional
pre-final frontier: the surviving zero-Schur packet was converted to a
rank-two repair tag by `withRepairOnly`, while the geometric reason for that
promotion was discarded.

The retained zero-Schur source packet already contains the missing geometric
certificate.  Its exact honest Hessian chart has

* a nonzero active `2 x 2` special-fibre minor;
* vanishing special Schur block; and
* the exact pure determinant clock of the incoming aligned endpoint.

Thus the chart itself is a genuine rank-at-least-two Hessian witness.  This
module packages that witness together with the finite repair transition.  The
state-level repair target is still the same-family `withRepairOnly` target,
but it can only leave this module accompanied by the exact chart geometry
which justifies the promotion.

No new local classification, kernel argument, or JC2 input is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Genuine rank-two geometry already present in a surviving zero-Schur
packet.  Everything is stated on the exact honest right-recentered Hessian
chart retained by the packet; in particular `activeDet_coeff_zero_ne_zero`
is a literal nonzero `2 x 2` minor of the special-fibre Hessian in an
invertible source chart, not a repair-metadata assertion. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurChartRankTwoWitness
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s) : Prop where
  determinantCore :
    P.carrier.chartData.chart.block.determinantCore =
      Polynomial.X ^ P.stationary.blocker.aligned.endpoint.defect
  activeDet_coeff_zero_ne_zero :
    P.carrier.chartData.chart.block.activeDet.coeff 0 ≠ 0
  schurA_coeff_zero :
    P.carrier.chartData.chart.block.schurA.coeff 0 = 0
  schurB_coeff_zero :
    P.carrier.chartData.chart.block.schurB.coeff 0 = 0
  schurC_coeff_zero :
    P.carrier.chartData.chart.block.schurC.coeff 0 = 0

/-- Extract the honest chart-level rank-two witness from the exact zero-Schur
carrier. -/
theorem AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem.chartRankTwoWitness
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s) :
    Nonempty (AdaptiveAlignedSmithCanonicalZeroSchurChartRankTwoWitness P) := by
  have hactive :=
    P.carrier.chartData.zeroData.activeDet_coeff_zero_ne_zero
  have hA := P.carrier.chartData.zeroData.schurA_coeff_zero
  have hB := P.carrier.chartData.zeroData.schurB_coeff_zero
  have hC := P.carrier.chartData.zeroData.schurC_coeff_zero
  rw [P.carrier.zeroSchurBlock_eq_chartBlock] at hactive hA hB hC
  exact ⟨{
    determinantCore := P.carrier.chartData.chart.determinantCore
    activeDet_coeff_zero_ne_zero := hactive
    schurA_coeff_zero := hA
    schurB_coeff_zero := hB
    schurC_coeff_zero := hC
  }⟩

/-- Geometry-carrying rank-two continuation for the zero-Schur branch.

The target differs from the incoming state only in the finite repair tag, but
unlike the provisional A17.4 transition the rank-two chart witness is retained
as part of the continuation object. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ) where
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq : target = s.withRepairOnly (rankTwoRepairState complexity)
  geometry : AdaptiveAlignedSmithCanonicalZeroSchurChartRankTwoWitness P
  repairProgress :
    RepairProgress (rankOneRepairState complexity) (rankTwoRepairState complexity)
  progress : CertifiedSameScaleEpisodeProgress RR target s

/-- Build the sound same-family rank-two continuation.  The numerical repair
step is exactly the existing finite repair transition, but it is now exported
only together with the honest nonzero active Hessian minor which witnesses the
rank-two geometry. -/
theorem AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem.exists_geometryCarryingRankTwoContinuation
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
        RR P complexity) := by
  rcases P.chartRankTwoWitness with ⟨geometry⟩
  let target := s.withRepairOnly (rankTwoRepairState complexity)
  have hrepair :
      RepairProgress (rankOneRepairState complexity) (rankTwoRepairState complexity) :=
    rankOne_to_rankTwo_repairProgress complexity
  have hprogress : CertifiedSameScaleEpisodeProgress RR target s := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
        hsrepair] using hrepair
  exact ⟨{
    target := target
    target_eq := rfl
    geometry := geometry
    repairProgress := hrepair
    progress := hprogress
  }⟩

/-- Sound post-rigid frontier.  Relative to A17.3F the only change is that the
zero-Schur local packet is converted to a *geometry-carrying* rank-two
continuation rather than to a naked repair macro. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreSoundPostRigidOutcome
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
  | zeroSchurRankTwo
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
        RR P complexity)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.11 sound zero-Schur bridge.**

This is the replacement for the provisional A17.4 zero-Schur promotion.  No
surviving zero-Schur packet is converted to a rank-two repair state without
also carrying the exact honest Hessian-chart witness that proves rank at least
two. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreSoundPostRigidFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreSoundPostRigidOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePostRigidEliminationFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      rcases P.exists_geometryCarryingRankTwoContinuation RR complexity hsrepair with ⟨D⟩
      exact .zeroSchurRankTwo P D

end

end HC4.Valuation
