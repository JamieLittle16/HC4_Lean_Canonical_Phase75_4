import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedPositiveSlopeRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalClosingCarrierCompleteRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import Mathlib.Tactic

/-!
# A18.4.73: presented blocker closes by zero or geometric global progress

A18.4.67 removes the positive-slope same-scale branch from rational
normalisation.  A18.4.72 removes the last same-scale branch from the deep
closing-carrier and rigid obstruction endpoints.  Every other constructor of
the A18.4.51 blocker closure already carried explicit rank-two geometry.

Rerunning the blocker splice therefore leaves only two outputs:

* literal zero raw defect on the original source; or
* strict progress in the well-founded global macro key, backed by an actual
  rank-two geometric witness on the target family.

There is no presentation-only, same-scale, or rational recursive constructor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

inductive AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)

/-- **A18.4.73 complete presented-blocker closure.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.completeSoundClosure
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteOutcome RR source := by
  cases D.completeRationalNormalizationOutcome RR complexity hsrepair with
  | rankTwo hP =>
      rcases hP with ⟨P⟩
      exact .globalProgress P.local.target P.globalProgress

  | stationary Z S hblock =>
      have hclock : S.blocker.aligned.endpoint.defect = D.presented.rawDefect := by
        rw [hblock]
        exact D.defect_eq
      have hpresentedRepair : D.presented.repair = rankOneRepairState complexity := by
        rcases D.sourcePresentation with ⟨hmove⟩
        rw [hmove.repair_eq]
        exact hsrepair

      cases D.geometricOutcome with
      | zeroDefect hzero =>
          have hpzero : D.presented.rawDefect = 0 := by
            rw [← D.defect_eq]
            exact hzero
          exact .zeroDefect
            (D.sourcePresentation.source_rawDefect_eq_zero_of_target hpzero)

      | rankTwoGeometry hG =>
          rcases hG with ⟨G⟩
          let P := AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.ofGeometry
            RR D complexity hsrepair G
          exact .globalProgress P.target P.globalProgress

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
              let Q :=
                AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
                  RR complexity hsrepair D.sourcePresentation P
              exact .globalProgress Q.local.target Q.globalProgress
          | residualRankTwo hgeometry =>
              rcases hgeometry with ⟨G⟩
              let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
                  D S complexity := {
                blocker_eq := hblock
                witness := Sum.inl G
              }
              let P := AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
                RR D S complexity hsrepair GG
              exact .globalProgress P.target P.globalProgress

      | zeroSchurClosing chart closing =>
          let G0 : AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry D := {
            chart := chart
            activeDet_coeff_zero_ne_zero := chart.zeroData.activeDet_coeff_zero_ne_zero
            schurA_coeff_zero := chart.zeroData.schurA_coeff_zero
            schurB_coeff_zero := chart.zeroData.schurB_coeff_zero
            schurC_coeff_zero := chart.zeroData.schurC_coeff_zero
          }
          let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
              D S complexity := {
            blocker_eq := hblock
            witness := Sum.inr G0
          }
          let P := AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
            RR D S complexity hsrepair GG
          exact .globalProgress P.target P.globalProgress

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
          let Q :=
            AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
              RR complexity hsrepair D.sourcePresentation P0
          exact .globalProgress Q.local.target Q.globalProgress

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
          let Q :=
            AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
              RR complexity hsrepair D.sourcePresentation P0
          exact .globalProgress Q.local.target Q.globalProgress

end

end HC4.Valuation
