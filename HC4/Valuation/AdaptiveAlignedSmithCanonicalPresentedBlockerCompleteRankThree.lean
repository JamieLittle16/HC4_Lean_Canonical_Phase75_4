import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerRigidPacketGeometry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedKernelRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalResidualChartRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalClosingCarrierCompleteRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThree
import Mathlib.Tactic

/-!
# A18.4.103: complete presented blocker closure at rank three

The blocker side is now completely geometric.

* positive rational slope: retained saturated opening -> A18.4.99 rank three;
* preterminal rank-one Schur clock: A18.4.86 rank three;
* zero-Schur chart: A18.4.83 rank three;
* closing carrier: A18.4.72 returns kernel or residual geometry, consumed by
  A18.4.99/A18.4.100;
* all-minors branch: A18.4.101 leaves only transverse freeness or rigid
  axis-square packets; freeness is contradictory and the rigid obstruction
  again ends in the complete kernel opening;
* every one of the five stationary residual packets is rank three by the
  retained exact chart of A18.4.100.

Thus the historical packet-rank-two remainder has disappeared.  This file
introduces no new local mathematics and no repair-only rank promotion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete rank-three geometry reachable from one presented blocker. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | kernel
      (G : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity)
  | schurPreterminal
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (hpre : chart.clock.firstOrder < D.blocker.aligned.endpoint.defect)
      (geometry : AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThreeExit
        chart.clock hpre complexity)
  | zeroSchur
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        chart.zeroData complexity)
  | residual
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (geometry : AdaptiveAlignedSmithCanonicalResidualRankThreeGeometry
        S complexity)

/-- Final local blocker frontier. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteRankThreeOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | rankThree
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteRankThreeGeometry
          RR D complexity))

/-- Lift a presented-kernel rank-three packet across the older pure
presentation of `D`. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry.liftAcrossBlocker
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
      D.presented complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
      source complexity where
  presented := G.presented
  sourcePresentation := D.sourcePresentation.trans G.sourcePresentation
  geometry := G.geometry

/-- **Every presented blocker is zero or completely rank three.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.completeRankThreeOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteRankThreeOutcome
      RR D complexity := by
  cases D.completeRationalNormalizationOutcome RR complexity hsrepair with
  | rankTwo hP =>
      rcases hP with ⟨P⟩
      exact .rankThree ⟨.kernel P.completeRankThreeGeometry⟩

  | stationary Z S hblock =>
      have hclock : S.blocker.aligned.endpoint.defect = D.presented.rawDefect := by
        rw [hblock]
        exact D.defect_eq
      have hpresentedRepair : D.presented.repair = rankOneRepairState complexity := by
        rcases D.sourcePresentation with ⟨hmove⟩
        rw [hmove.repair_eq]
        exact hsrepair

      cases D.rigidPacketGeometricOutcome with
      | zeroDefect hzero =>
          have hpzero : D.presented.rawDefect = 0 := by
            rw [← D.defect_eq]
            exact hzero
          exact .zeroDefect
            (D.sourcePresentation.source_rawDefect_eq_zero_of_target hpzero)

      | schurRankTwo hG =>
          rcases hG with ⟨G⟩
          cases G with
          | schurPreterminal chart hpre =>
              rcases chart.clock.exists_preterminalRankThreeExit
                  hpre complexity with ⟨E⟩
              exact .rankThree ⟨.schurPreterminal chart hpre E⟩
          | zeroSchurPreterminal chart residual residual_pos residual_clock hpre =>
              exact .rankThree ⟨.zeroSchur chart
                (exactSourceZeroSchur_completeRankThreeGeometry
                  chart.zeroData complexity)⟩

      | schurClosing chart closing transverse =>
          let C0 : AdaptiveAlignedSmithRankOneClosingSourceCarrier D.blocker := {
            source := D.blocker.recenteredSourceData
            chartData := chart
            closing := ⟨closing, transverse⟩
          }
          let C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker := by
            rw [hblock]
            exact C0
          cases S.toTerminalSourcePacket.closingCarrier_completeRankTwoOutcome_currentScale
              RR hclock complexity hpresentedRepair C with
          | kernelRankTwo hP =>
              rcases hP with ⟨P⟩
              exact .rankThree ⟨.kernel
                P.completeRankThreeGeometry.liftAcrossBlocker⟩
          | residualRankTwo hG =>
              rcases hG with ⟨G⟩
              exact .rankThree ⟨.residual S G.toRankThree⟩

      | zeroSchurClosing chart closing =>
          exact .rankThree ⟨.zeroSchur chart
            (exactSourceZeroSchur_completeRankThreeGeometry
              chart.zeroData complexity)⟩

      | transverseFree hall hfree =>
          have hfreeS :
              ∀ d ∈ S.blocker.aligned.endpoint.rawSpecialFiber.support,
                d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0 := by
            simpa [hblock] using hfree
          exact (S.not_rawSpecialFiber_transverseFree hfreeS).elim

      | planarRigid hall P hrigid =>
          let P' : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
              (K := K) S.blocker := by
            rw [hblock]
            exact P
          have hall' :
              ∀ rho : Equiv.Perm (Fin 4),
                (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
                  rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
            simpa [hblock] using hall
          have hrigid' : HasRigidRankOnePacket
              (0 : Fin 4) 1 2 P'.degree P'.packet := by
            simpa [P'] using hrigid
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
            source := S.toTerminalSourcePacket
            hall := hall'
            packet := .planar P' hrigid'
          }
          rcases R.completeRankTwoOutcome_currentScale
              RR hclock complexity hpresentedRepair with ⟨P0⟩
          exact .rankThree ⟨.kernel
            P0.completeRankThreeGeometry.liftAcrossBlocker⟩

      | wSquareRigid hall P hrigid =>
          let P' : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker := by
            rw [hblock]
            exact P
          have hall' :
              ∀ rho : Equiv.Perm (Fin 4),
                (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
                  rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
            simpa [hblock] using hall
          have hrigid' : HasRigidRankOnePacket
              (0 : Fin 4) 3 2 P'.degree P'.packet := by
            simpa [P'] using hrigid
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
            source := S.toTerminalSourcePacket
            hall := hall'
            packet := .wSquare P' hrigid'
          }
          rcases R.completeRankTwoOutcome_currentScale
              RR hclock complexity hpresentedRepair with ⟨P0⟩
          exact .rankThree ⟨.kernel
            P0.completeRankThreeGeometry.liftAcrossBlocker⟩

end

end HC4.Valuation
