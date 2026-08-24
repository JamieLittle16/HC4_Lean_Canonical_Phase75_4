import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedSurvivingClosure
import Mathlib.Tactic

/-!
# A18.4.36: absorb every aligned section-boundary head

A18.4.29 turns an aligned section-boundary head into either genuine strict
progress or one actual represented canonical blocker/surviving endpoint.
A18.4.31 and A18.4.35 now close those represented endpoints at their literal
current scale.  Therefore an aligned boundary is no longer a recursive state:
it is consumed in one finite macro step.

The blocker side closes completely.  The surviving side closes completely
except for the already-isolated exact Smith-exposure boundary presentation.
Thus the only non-strict output of this file is that single exposure-boundary
geometry.  In particular no aligned boundary, blocker, rigid packet, closing
carrier, or repair-only residue survives.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Final result of consuming one aligned-boundary head. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryAbsorbedOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)
  | exposureBoundaryPresentation
      (presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) presented)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toPresentedBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target source)

/-- **Aligned-boundary absorber.**

The entire aligned-boundary classification is performed before any recursive
call.  Primitive/coupled origin tags are erased only after the represented
canonical endpoint is tied to its actual family/clock/section. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.soundAbsorption
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryAbsorbedOutcome
      RR source complexity := by
  cases trace.toPresentedEndpointOutcome with
  | strictMacro D =>
      exact .ramifiedStrictMacro D

  | blocker D =>
      cases D.soundClosure RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | ramifiedStrictMacro P =>
          exact .ramifiedStrictMacro P

  | surviving D =>
      cases D.soundReduction RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | ramifiedStrictMacro P =>
          exact .ramifiedStrictMacro P
      | exposureBoundaryPresentation presented E target target_eq hmove =>
          exact .exposureBoundaryPresentation
            presented E target target_eq hmove

/-- A literal section-boundary constructor is just the one-head special case
of the absorber above. -/
theorem AdaptiveAlignedSmithSectionBoundaryEndpoint.soundGlobalAbsorption
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryAbsorbedOutcome
      RR source complexity := by
  exact (AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.head
    (RR := RR) B).soundAbsorption complexity hsrepair

end

end HC4.Valuation
