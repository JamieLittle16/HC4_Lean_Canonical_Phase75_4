import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingZeroLinearJetRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingFirstContactClosure
import Mathlib.Tactic

/-!
# A18.4.70: presented surviving endpoint closes without same-scale recursion

A18.4.53 removed rational-spend recursion from surviving endpoints but still
retained a `presentedSameScale` constructor at the two kernel-free exposure
leaves.  A18.4.68 proves that those exact exposure families have zero source
jet and therefore go directly to geometry-backed rank-two progress.

Rerunning the short surviving packet split now leaves only:

* literal zero defect on the original source;
* strict global-key progress backed by actual rank-two geometry; or
* the canonical exposure section-boundary presentation, already known to be
  contradictory at the next splice.

There is no same-scale recursive constructor in this interface.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingCompleteOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
  | exposureBoundaryPresentation
      (presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) presented)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toPresentedBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target source)

/-- **A18.4.70 complete presented surviving closure.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.completeSoundReduction
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedSurvivingCompleteOutcome
      RR source complexity := by
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
      exact .exposureBoundaryPresentation s E target rfl
        (D.sourcePresentation.trans hpresented)

    · rcases hsaturated with ⟨S⟩
      let E := S.toGlobalKernelFreeExposure P
      have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
        simpa [E, s, W,
          AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
          using D.defect_eq
      rcases E.completeRankTwoProgress_from_presented
          RR D hclock complexity hsrepair with ⟨Q⟩
      exact .globalProgress Q.localProgress.target Q.globalProgress

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
          exact .exposureBoundaryPresentation s E target rfl
            (D.sourcePresentation.trans hpresented)

      | rankTwoGeometry hgeometry =>
          rcases hgeometry with ⟨G⟩
          have hclock : W.original.aligned.endpoint.defect = s.rawDefect := by
            simpa [s, W,
              AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
              using D.defect_eq
          let Q :=
            AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofPresentedGeometry
              RR W P R hD3 complexity hsrepairPresented hclock G
          have htarget : Q.target.repair = rankTwoRepairState complexity := by
            rw [Q.target_eq]
            rfl
          exact .globalProgress Q.target
            (globalMacroProgress_of_rankTwoTarget
              complexity hsrepair htarget)

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
          rcases E.completeRankTwoProgress_from_presented
              RR D hclock complexity hsrepair with ⟨Q⟩
          exact .globalProgress Q.localProgress.target Q.globalProgress

    · rcases hrankTwo with ⟨R2⟩
      let target :=
        R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAwareAt
          s.scale s.scale_pos
      have htarget : target.repair = rankTwoRepairState complexity := by
        rfl
      exact .globalProgress target
        (globalMacroProgress_of_rankTwoTarget
          complexity hsrepair htarget)

end

end HC4.Valuation