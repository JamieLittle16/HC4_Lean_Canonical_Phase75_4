import HC4.Valuation.AdaptiveAlignedSmithCanonicalFirstContactBoundaryAbsorber
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExposureNoBoundary
import Mathlib.Tactic

/-!
# A18.4.55: direct first-contact dispatcher

The historical exact-clock pipeline first packaged a blocker/surviving
endpoint, sent it through a long stationary residual stack, and only much later
recovered the actual represented family.  A18.4.51 and A18.4.53 now make that
round trip unnecessary.

Starting directly from the provenance-preserving one-shot aligned-Smith
classifier, split the universal clock bound

    endpoint.defect ≤ 20 * source.rawDefect

before doing any local geometry.

* If equality holds, the aligned endpoint is an honest pure presentation of
  the source at the literal outer scale.  We package it immediately as a
  current-scale presented blocker/surviving endpoint and invoke the new
  first-contact closures.
* If strict inequality holds, we retain that event explicitly as the sole
  initial aligned-clock loss.  It is not called recursive progress here.
* A genuine section boundary is consumed by A18.4.54.  The only exposure
  boundary which could survive that absorber is impossible by A18.4.37.

Thus none of the old exact-clock closing-carrier, rigid-packet, or
kernel-exposure ramified spends survive this frontier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The final local classification before the initial aligned-clock loss is
itself discharged. -/
inductive AdaptiveAlignedSmithCanonicalDirectFirstContactOutcome
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
  | outerProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalOuterKey.Lt
        (target.canonicalOuterKey RR) (source.canonicalOuterKey RR))
  | alignedClockLoss
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target source)

/-- **A18.4.55 direct first-contact classifier.**

Exact aligned endpoints are consumed at their actual current scale.  No
historical exact-clock residual object is formed. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalDirectFirstContactFrontier
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalDirectFirstContactOutcome
      RR source complexity := by
  rcases source.alignedSmithClassifierDispatcher_withClockBound with
    ⟨B, hclock⟩ | ⟨W, hclock⟩ | hboundary

  · by_cases hlt :
        B.aligned.endpoint.defect <
          alignedSmithRamificationIndex * source.rawDefect
    · let target := B.aligned.toOuterScaleAwareState source
      exact .alignedClockLoss target
        ⟨B.aligned.certifiedOuterSpend_of_defect_lt source hlt⟩
    · have heq :
          B.aligned.endpoint.defect =
            alignedSmithRamificationIndex * source.rawDefect := by
        exact Nat.le_antisymm hclock (Nat.le_of_not_gt hlt)
      let presented := B.aligned.toOuterScaleAwareState source
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        exact ⟨B.aligned.certifiedOuterInternal_of_defect_eq source heq⟩
      let D : AdaptiveAlignedSmithCanonicalPresentedBlocker
          (K := K) source := {
        presented := presented
        sourcePresentation := hmove
        blocker := B
        defect_eq := by rfl
        family_eq := by rfl
        movingSection_eq := by rfl
      }
      cases D.firstContactSoundClosure RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | presentedSameScale P =>
          exact .presentedSameScale P
      | positiveKernelRankTwo hP =>
          rcases hP with ⟨P⟩
          exact .globalProgress
            P.openingProgress.openingProgress.target P.globalProgress
      | factorOneKernelRankTwo hP =>
          rcases hP with ⟨P⟩
          exact .globalProgress P.local.openingProgress.target P.globalProgress
      | blockerRankTwo hP =>
          rcases hP with ⟨P⟩
          exact .globalProgress P.target P.globalProgress
      | stationaryRankTwo S hP =>
          rcases hP with ⟨P⟩
          exact .globalProgress P.target P.globalProgress

  · by_cases hlt :
        W.aligned.endpoint.defect <
          alignedSmithRamificationIndex * source.rawDefect
    · let target := W.aligned.toOuterScaleAwareState source
      exact .alignedClockLoss target
        ⟨W.aligned.certifiedOuterSpend_of_defect_lt source hlt⟩
    · have heq :
          W.aligned.endpoint.defect =
            alignedSmithRamificationIndex * source.rawDefect := by
        exact Nat.le_antisymm hclock (Nat.le_of_not_gt hlt)
      let presented := W.aligned.toOuterScaleAwareState source
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        exact ⟨W.aligned.certifiedOuterInternal_of_defect_eq source heq⟩
      let D : AdaptiveAlignedSmithCanonicalPresentedSurviving
          (K := K) source := {
        presented := presented
        sourcePresentation := hmove
        wall := W
        defect_eq := by rfl
        family_eq := by rfl
        movingSection_eq := by rfl
      }
      cases D.firstContactSoundReduction RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | presentedSameScale P =>
          exact .presentedSameScale P
      | globalProgress target h =>
          exact .globalProgress target h
      | exposureBoundaryPresentation presented E target target_eq hmove =>
          exact E.impossible.elim

  · rcases hboundary with ⟨B⟩
    cases B.firstContactSoundGlobalAbsorption RR complexity hsrepair with
    | zeroDefect hzero =>
        exact .zeroDefect hzero
    | presentedSameScale P =>
        exact .presentedSameScale P
    | globalProgress target h =>
        exact .globalProgress target h
    | outerProgress target h =>
        exact .outerProgress target h
    | ramifiedSpend target h =>
        exact .alignedClockLoss target h
    | exposureBoundaryPresentation presented E target target_eq hmove =>
        exact E.impossible.elim

end

end HC4.Valuation
