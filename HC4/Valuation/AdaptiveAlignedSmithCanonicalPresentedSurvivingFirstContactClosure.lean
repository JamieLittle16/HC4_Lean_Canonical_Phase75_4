import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingKernelFirstContact
import Mathlib.Tactic

/-!
# A18.4.53: presented surviving endpoint closes without a rational recursive edge

A18.4.52 removes the only unsafe leaf of A18.4.31: a canonical kernel-free
Smith exposure is no longer converted directly into a ramified raw-defect
spend.  Instead it terminates by saturated first contact, yielding either a
strict same-scale exit of the actual exposed state or a geometry-backed
rank-one -> rank-two promotion on the saturated-opening family.

This file reruns the short A18.4.31 splice with that stronger endpoint.  Every
surviving-wall output is now one of:

* zero determinant defect on the original source;
* a strict fixed-scale exit after an explicitly retained pure presentation;
* strict progress in the well-founded global macro key, always coming from a
  geometry-backed rank-two promotion; or
* the canonical exposure-boundary presentation, which A18.4.37 proves
  impossible.

There is no ramified raw-defect spend and no anonymous ramified strict macro.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A rank-two target is globally below an original rank-one source regardless
of intervening pure ramified presentations.  This helper is intentionally
about the finite repair coordinate only. -/
theorem globalMacroProgress_of_rankTwoTarget
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (htarget : target.repair = rankTwoRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
  unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
  unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
  apply Prod.Lex.left
  rw [htarget, hsrepair]
  exact repairState_measure_lt_of_progress
    (rankOne_to_rankTwo_repairProgress complexity)

/-- First-contact-safe closure of one already-presented surviving endpoint. -/
inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingFirstContactClosedOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | presentedSameScale
      (P : AdaptiveAlignedSmithCanonicalPresentedSameScaleProgress RR source)
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

/-- **A18.4.53 presented surviving first-contact closure.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.firstContactSoundReduction
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedSurvivingFirstContactClosedOutcome
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
      cases E.firstContactOutcome_from_presented
          RR D hclock complexity hsrepair with
      | presentedSameScale P0 =>
          exact .presentedSameScale P0
      | rankTwo hP =>
          rcases hP with ⟨Q⟩
          exact .globalProgress Q.local.target Q.globalProgress

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
          cases E.firstContactOutcome_from_presented
              RR D hclock complexity hsrepair with
          | presentedSameScale P0 =>
              exact .presentedSameScale P0
          | rankTwo hP =>
              rcases hP with ⟨Q⟩
              exact .globalProgress Q.local.target Q.globalProgress

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
