import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingFirstContactClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedStrictReason
import Mathlib.Tactic

/-!
# A18.4.54: aligned boundary absorption after first-contact repair

A18.4.36 compressed a boundary-produced canonical endpoint, but its blocker
and surviving consumers still returned generic ramified strict macros.  The
A18.4.51/A18.4.53 closures now retain enough geometry to avoid that loss.

This file reruns the boundary-head absorber with those stronger interfaces.
Every endpoint-side exit is now either fixed-scale progress after a retained
pure presentation or strict progress in the discrete global macro key.  The
only ramified raw spend which can survive is one already present *before* the
represented endpoint is formed; that is the initial aligned-clock obligation
which remains to be discharged separately.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- First-contact-aware result of consuming one aligned-boundary head. -/
inductive AdaptiveAlignedSmithCanonicalFirstContactAlignedBoundaryOutcome
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
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target source)
  | exposureBoundaryPresentation
      (presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) presented)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toPresentedBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target source)

/-- **A18.4.54 aligned-boundary first-contact absorber.** -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.firstContactSoundAbsorption
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalFirstContactAlignedBoundaryOutcome
      RR source complexity := by
  cases trace.toPresentedEndpointOutcome with
  | strictMacro D =>
      cases D.reason RR with
      | outerProgress target h =>
          exact .outerProgress target h
      | rawSpend target h =>
          exact .ramifiedSpend target h

  | blocker D =>
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
          exact .globalProgress
            P.localProgress.openingProgress.target P.globalProgress
      | blockerRankTwo hP =>
          rcases hP with ⟨P⟩
          exact .globalProgress P.target P.globalProgress
      | stationaryRankTwo S hP =>
          rcases hP with ⟨P⟩
          exact .globalProgress P.target P.globalProgress

  | surviving D =>
      cases D.firstContactSoundReduction RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | presentedSameScale P =>
          exact .presentedSameScale P
      | globalProgress target h =>
          exact .globalProgress target h
      | exposureBoundaryPresentation presented E target target_eq hmove =>
          exact .exposureBoundaryPresentation
            presented E target target_eq hmove

/-- Literal section-boundary specialisation of the first-contact absorber. -/
theorem AdaptiveAlignedSmithSectionBoundaryEndpoint.firstContactSoundGlobalAbsorption
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalFirstContactAlignedBoundaryOutcome
      RR source complexity := by
  exact (AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.head
    (RR := RR) B).firstContactSoundAbsorption complexity hsrepair

end

end HC4.Valuation
