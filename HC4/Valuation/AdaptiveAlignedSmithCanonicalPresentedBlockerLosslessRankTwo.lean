import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteClosure
import Mathlib.Tactic

/-!
# A18.4.76: lossless presented-blocker rank-two frontier

A18.4.73 proves that a presented blocker has only zero defect or global
progress.  For global termination that compact statement is ideal, but it
forgets which concrete rank-two geometry justified the progress.

This file reruns the same finite blocker split without that final erasure.
Every nonzero branch now exports one of the existing geometry-bearing objects:

* a complete saturated-kernel opening with diagonal/mixed Hessian activity;
* a direct blocker Schur/packet rank-two witness; or
* the final stationary residual/zero-Schur rank-two witness.

No new local mathematics and no new successor construction is introduced.
The purpose is to give the rank-two endgame a single lossless entry point.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete geometry-bearing outcome of one presented blocker. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerLosslessRankTwoOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | completeKernel
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR source complexity))
  | blocker
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
          RR D complexity))
  | stationary
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
          RR D S complexity))

/-- **Lossless A18.4.73.**  This is the same complete blocker closure, but every
rank-two exit retains the exact family geometry which licensed the promotion. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.losslessRankTwoClosure
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerLosslessRankTwoOutcome
      RR D complexity := by
  cases D.completeRationalNormalizationOutcome RR complexity hsrepair with
  | rankTwo hP =>
      exact .completeKernel hP

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
          exact .blocker ⟨
            AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.ofGeometry
              RR D complexity hsrepair G
          ⟩

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
                  RR complexity hsrepair
                  (D.sourcePresentation.trans P.sourcePresentation)
                  P.localProgress
              exact .completeKernel ⟨Q⟩
          | residualRankTwo hgeometry =>
              rcases hgeometry with ⟨G⟩
              let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
                  D S complexity := {
                blocker_eq := hblock
                witness := Sum.inl G
              }
              exact .stationary S ⟨
                AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
                  RR D S complexity hsrepair GG
              ⟩

      | zeroSchurClosing chart closing =>
          let G0 : AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry D := {
            chart := chart
          }
          let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
              D S complexity := {
            blocker_eq := hblock
            witness := Sum.inr G0
          }
          exact .stationary S ⟨
            AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
              RR D S complexity hsrepair GG
          ⟩

      | transverseFree hall hfree =>
          have hfreeS :
              ∀ d ∈ S.blocker.aligned.endpoint.rawSpecialFiber.support,
                d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0 := by
            simpa [hblock] using hfree
          exact (S.not_rawSpecialFiber_transverseFree hfreeS).elim

      | planarRigid hall P hrigid =>
          rcases transportPlanarRigidPacket (K := K) hblock P hrigid with
            ⟨P', hrigid'⟩
          have hall' :
              ∀ rho : Equiv.Perm (Fin 4),
                (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
                  rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
            simpa [hblock] using hall
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
            source := S.toTerminalSourcePacket
            hall := hall'
            packet := .planar P' hrigid'
          }
          rcases R.completeRankTwoOutcome_currentScale
              RR hclock complexity hpresentedRepair with ⟨P0⟩
          let Q :=
            AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
              RR complexity hsrepair
              (D.sourcePresentation.trans P0.sourcePresentation)
              P0.localProgress
          exact .completeKernel ⟨Q⟩

      | wSquareRigid hall P hrigid =>
          rcases transportWSquareRigidPacket (K := K) hblock P hrigid with
            ⟨P', hrigid'⟩
          have hall' :
              ∀ rho : Equiv.Perm (Fin 4),
                (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
                  rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
            simpa [hblock] using hall
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
            source := S.toTerminalSourcePacket
            hall := hall'
            packet := .wSquare P' hrigid'
          }
          rcases R.completeRankTwoOutcome_currentScale
              RR hclock complexity hpresentedRepair with ⟨P0⟩
          let Q :=
            AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
              RR complexity hsrepair
              (D.sourcePresentation.trans P0.sourcePresentation)
              P0.localProgress
          exact .completeKernel ⟨Q⟩

end

end HC4.Valuation
