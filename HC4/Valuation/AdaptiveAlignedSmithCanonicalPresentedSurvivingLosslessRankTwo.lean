import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingCompleteClosure
import Mathlib.Tactic

/-!
# A18.4.77: lossless presented-surviving rank-two frontier

A18.4.70 closes every surviving endpoint for termination, but its compact
`globalProgress` constructor hides the object needed by the finite-rank
endgame.  This file repeats the same finite degree/packet split and retains the
actual geometry.

In particular the nonrigid `D >= 3` packet branch exports the existing
`AdaptiveAlignedSmithRankTwoPacketEndpoint`, whose continuation contains the
integral Smith wall, quadratic subface and persistent packet provenance needed
by the already-green matrix-exposure/zero-Schur pipeline.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Geometry-bearing result of one presented surviving wall. -/
inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingLosslessRankTwoOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | completeKernel
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR source complexity))
  | rigidExposure
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) D.presented W P)
      (hD : 3 ≤ P.degree)
      (Q : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
          RR D.presented W P R hD complexity))
  | packetFamily
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (hD : 3 ≤ P.degree)
      (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
        (K := K) D.presented W P complexity)
  | exposureBoundaryPresentation
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) D.presented)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toPresentedBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target source)

/-- **Lossless A18.4.70.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.losslessRankTwoReduction
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedSurvivingLosslessRankTwoOutcome
      RR D complexity := by
  let s := D.presented
  let W := D.toStateEndpoint

  have hsrepairPresented : s.repair = rankOneRepairState complexity := by
    rcases D.sourcePresentation with ⟨hmove⟩
    dsimp [s]
    rw [hmove.repair_eq]
    exact hsrepair

  rcases W.persistentPacket s with ⟨P⟩
  rcases P.degree_eq_two_or_three_le s W with hD2 | hD3

  · rcases P.degreeTwo_zeroDefect_or_boundary_or_saturated
        s W hD2 with hzero | hboundary | hsaturated

    · have hsZero : s.rawDefect = 0 := by
        change W.original.aligned.endpoint.defect = 0 at hzero
        have hclock : W.original.aligned.endpoint.defect = s.rawDefect := by
          simpa [s, W,
            AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
            using D.defect_eq
        rw [hclock] at hzero
        exact hzero
      exact .zeroDefect
        (D.sourcePresentation.source_rawDefect_eq_zero_of_target hsZero)

    · rcases hboundary with ⟨B⟩
      let E := B.toGlobalExposureBoundary
      have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
        simpa [E, s, W,
          AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
          using D.defect_eq
      let target := E.toPresentedBoundaryState
      have hpresented : HasCertifiedRamifiedEpisodeInternalMove target s := by
        dsimp [target]
        exact E.certifiedInternalMove_from_presented hclock
      exact .exposureBoundaryPresentation E target rfl
        (D.sourcePresentation.trans hpresented)

    · rcases hsaturated with ⟨S⟩
      let E := S.toGlobalKernelFreeExposure P
      have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
        simpa [E, s, W,
          AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
          using D.defect_eq
      exact .completeKernel
        (E.completeRankTwoProgress_from_presented
          RR D hclock complexity hsrepair)

  · rcases P.rigid_or_rankTwoFamilyContinuation s W complexity with
      hrigid | hrankTwo

    · rcases hrigid with ⟨R⟩
      cases R.geometricExposureOutcome s W P hD3 complexity with
      | zeroDefect hzero =>
          have hsZero : s.rawDefect = 0 := by
            change W.original.aligned.endpoint.defect = 0 at hzero
            have hclock : W.original.aligned.endpoint.defect = s.rawDefect := by
              simpa [s, W,
                AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
                using D.defect_eq
            rw [hclock] at hzero
            exact hzero
          exact .zeroDefect
            (D.sourcePresentation.source_rawDefect_eq_zero_of_target hsZero)

      | boundary exposure hboundary =>
          let E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
              (K := K) s := {
            W := W
            exposure := exposure
            boundary := hboundary
          }
          have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
            simpa [E, s, W,
              AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
              using D.defect_eq
          let target := E.toPresentedBoundaryState
          have hpresented : HasCertifiedRamifiedEpisodeInternalMove target s := by
            dsimp [target]
            exact E.certifiedInternalMove_from_presented hclock
          exact .exposureBoundaryPresentation E target rfl
            (D.sourcePresentation.trans hpresented)

      | rankTwoGeometry hgeometry =>
          rcases hgeometry with ⟨G⟩
          exact .rigidExposure W P R hD3 ⟨
            AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofGeometry
              RR W P R hD3 complexity hsrepairPresented G
          ⟩

      | canonicalClosing C hspecial =>
          let E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
              (K := K) s := {
            W := W
            exposure := C.exposure
            canonicalSpecial := hspecial
            specialFiber_free_three := C.specialFiber_free_three hspecial
          }
          have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
            simpa [E, s, W,
              AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
              using D.defect_eq
          exact .completeKernel
            (E.completeRankTwoProgress_from_presented
              RR D hclock complexity hsrepair)

    · rcases hrankTwo with ⟨R2⟩
      exact .packetFamily W P hD3 R2

end

end HC4.Valuation
