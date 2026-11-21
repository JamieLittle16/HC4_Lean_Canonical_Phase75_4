import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryNoSpendClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingFirstContactClosure
import Mathlib.Tactic

/-!
# A18.4.62: first-contact boundary absorption with no ramified-spend output

A18.4.61 removes the last unsafe edge before a canonical endpoint is formed.
A18.4.51 and A18.4.53 had already removed every unsafe edge after blocker or
surviving presentation.

Composing those three facts gives the first boundary absorber whose public
interface has no rational/cross-scale recursive constructor at all.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete no-spend first-contact result of one aligned section-boundary
head.  Pure presentations are retained inside `presentedSameScale`; finite
rank promotion is represented by the already well-founded global key. -/
inductive AdaptiveAlignedSmithCanonicalBoundaryFirstContactNoSpendOutcome
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

/-- **A18.4.62 no-spend boundary first-contact absorber.** -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.firstContactNoSpendAbsorption
    {RR : RepairRanking}
    {source tail : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source tail)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalBoundaryFirstContactNoSpendOutcome
      RR source complexity := by
  cases trace.toPresentedNoSpendOutcome with
  | sameScale target hprogress =>
      exact .presentedSameScale {
        presented := source
        sourcePresentation := HasCertifiedRamifiedEpisodeInternalMove.identity source
        target := target
        progress := hprogress
      }

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
          exact .globalProgress P.local.openingProgress.target P.globalProgress
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

/-- Literal section-boundary entry into the no-spend absorber. -/
theorem AdaptiveAlignedSmithSectionBoundaryEndpoint.firstContactNoSpendGlobalAbsorption
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalBoundaryFirstContactNoSpendOutcome
      RR source complexity := by
  exact (AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.head
    (RR := RR) B).firstContactNoSpendAbsorption complexity hsrepair

end

end HC4.Valuation
