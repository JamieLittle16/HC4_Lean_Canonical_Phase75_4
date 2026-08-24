import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingExactClockReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentationTraceInvariant
import Mathlib.Tactic

/-!
# A18.4.9: consume surviving-exact-clock heads of presentation traces

A18.4.8 reduces one genuine `survivingExactClock` provenance leaf to honest
zero-defect / ramified-strict exits or three concrete packet geometries.  The
A18.4.6 frontier, however, may return a *composed* presentation trace, so that
leaf can be hidden at the left edge of a longer trace.

This file performs the missing structural integration.  We recursively inspect
the leftmost provenance leaf.

* a surviving-exact-clock leaf is consumed by A18.4.8;
* if its reduction gives a genuine exit or concrete packet geometry, the rest
  of the presentation suffix is irrelevant and is discarded;
* if a section-boundary or quarantined legacy rank-two presentation occurs
  first, it is retained as the explicit blocker, together with the untouched
  suffix.

The residual presentation type therefore certifies that its *first unresolved
origin* is section-boundary or legacy rank-two.  A surviving exact-clock leaf
can no longer be hidden at the head of an opaque presentation chain.

No presentation is declared progress and no new repair successor is
manufactured.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A presentation trace whose leftmost unresolved origin is known not to be
`survivingExactClock`.

The first leaf is either a genuine aligned section boundary or the quarantined
legacy rank-two presentation.  An arbitrary already-certified presentation
suffix may follow it.  This is exactly the obstruction remaining after
recursively consuming all leading surviving-exact-clock leaves. -/
inductive AdaptiveAlignedSmithCanonicalBlockedPresentationTrace
    (RR : RepairRanking) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) →
      ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | sectionBoundary
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection) :
      AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR source
        (source.alignedBoundaryScaleAwareReentry B)

  | legacyRankTwo
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer source)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer) :
      AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR source outer

  | trans
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (first :
        AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR source middle)
      (second :
        AdaptiveAlignedSmithCanonicalPresentationTrace RR middle target) :
      AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR source target

/-- Forget the statement that the head is blocked and recover the ordinary
presentation provenance trace. -/
theorem AdaptiveAlignedSmithCanonicalBlockedPresentationTrace.toPresentationTrace
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace :
      AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR source target) :
    AdaptiveAlignedSmithCanonicalPresentationTrace RR source target := by
  induction trace with
  | sectionBoundary B =>
      exact .sectionBoundary B
  | legacyRankTwo outer target hmove hprogress =>
      exact .legacyRankTwo outer target hmove hprogress
  | trans first second ih =>
      exact .trans ih second

/-- A blocked trace is still an honest pure ramified presentation certificate;
only its provenance head has been refined. -/
theorem AdaptiveAlignedSmithCanonicalBlockedPresentationTrace.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace :
      AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source :=
  trace.toPresentationTrace.toInternalMove

/-- Output of recursively consuming every leading surviving-exact-clock leaf
from one presentation trace. -/
inductive AdaptiveAlignedSmithCanonicalGlobalSurvivingTraceReductionOutcome
    (RR : RepairRanking)
    (s target : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | degreeTwoBoundary
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (B : AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint (K := K) s W)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | degreeTwoSaturated
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint (K := K) s W)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | blockedPresentation
      (trace :
        AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR s target)

/-- **Consume the left edge of an arbitrary finite presentation trace.**

A surviving-exact-clock leaf is immediately reduced by A18.4.8.  In a
composite trace we recurse only into the first component.  Once that prefix
produces a genuine exit or concrete packet geometry, the suffix need not be
followed.  If the prefix is blocked, the suffix is reattached behind the
explicit section-boundary/legacy blocker. -/
theorem AdaptiveAlignedSmithCanonicalPresentationTrace.reduceSurvivingHead
    {RR : RepairRanking}
    {s target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingTraceReductionOutcome
      RR s target complexity := by
  induction trace generalizing complexity with
  | survivingExactClock W clock_eq =>
      cases
        AdaptiveAlignedSmithSurvivingStateEndpoint.globalExactClockReduction
          (K := K) RR _ W complexity clock_eq hsrepair with
      | zeroDefectReentry hzero D =>
          exact .zeroDefectReentry hzero D
      | ramifiedStrictMacro D =>
          exact .ramifiedStrictMacro D
      | degreeTwoBoundary W P hD B clock_eq =>
          exact .degreeTwoBoundary W P hD B clock_eq
      | degreeTwoSaturated W P hD S clock_eq =>
          exact .degreeTwoSaturated W P hD S clock_eq
      | rigidPacket W P hD R clock_eq =>
          exact .rigidPacket W P hD R clock_eq

  | sectionBoundary B =>
      exact .blockedPresentation (.sectionBoundary B)

  | legacyRankTwo outer target hmove hprogress =>
      exact .blockedPresentation
        (.legacyRankTwo outer target hmove hprogress)

  | trans first second ihFirst _ihSecond =>
      cases ihFirst complexity hsrepair with
      | zeroDefectReentry hzero D =>
          exact .zeroDefectReentry hzero D
      | ramifiedStrictMacro D =>
          exact .ramifiedStrictMacro D
      | degreeTwoBoundary W P hD B clock_eq =>
          exact .degreeTwoBoundary W P hD B clock_eq
      | degreeTwoSaturated W P hD S clock_eq =>
          exact .degreeTwoSaturated W P hD S clock_eq
      | rigidPacket W P hD R clock_eq =>
          exact .rigidPacket W P hD R clock_eq
      | blockedPresentation blocked =>
          exact .blockedPresentation (.trans blocked second)

/-! ## Global frontier with surviving presentation heads eliminated -/

/-- The A18.4 global frontier after recursively consuming every leading
`survivingExactClock` presentation origin.

The old generic `internalPresentation` constructor has been replaced by
`blockedPresentation`, which proves that the first unresolved presentation
origin is one of only two kinds: aligned section-boundary or quarantined
legacy rank-two. -/
inductive AdaptiveAlignedSmithCanonicalGlobalSurvivingHeadReducedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | pointedRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
          RR s complexity))

  | degreeTwoBoundary
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (B : AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint (K := K) s W)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | degreeTwoSaturated
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint (K := K) s W)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | blockedPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (trace :
        AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR s target)

/-- **A18.4.9 global surviving-head reduction.**

Run the canonical trace-only frontier of A18.4.6.  Genuine exits pass through
unchanged.  Any presentation trace is structurally reduced until either the
surviving-exact-clock origin yields an honest exit/concrete packet, or the
first genuinely unresolved section-boundary/legacy origin is exposed. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalSurvivingHeadReducedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingHeadReducedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalPresentationTraceFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D
  | internalPresentation target trace =>
      cases trace.reduceSurvivingHead complexity hsrepair with
      | zeroDefectReentry hzero D =>
          exact .zeroDefectReentry hzero D
      | ramifiedStrictMacro D =>
          exact .ramifiedStrictMacro D
      | degreeTwoBoundary W P hD B clock_eq =>
          exact .degreeTwoBoundary W P hD B clock_eq
      | degreeTwoSaturated W P hD S clock_eq =>
          exact .degreeTwoSaturated W P hD S clock_eq
      | rigidPacket W P hD R clock_eq =>
          exact .rigidPacket W P hD R clock_eq
      | blockedPresentation blocked =>
          exact .blockedPresentation target blocked

end

end HC4.Valuation
