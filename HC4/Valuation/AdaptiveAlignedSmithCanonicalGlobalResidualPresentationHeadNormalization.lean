import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCanonicalExposureNeutrality
import Mathlib.Tactic

/-!
# A18.4.13: normal form for the residual presentation head

A18.4.12 removes the last arithmetic ambiguity in the canonical surviving
Smith exposure.  The global frontier is now strict except for honest pure
presentations.  One presentation constructor is already explicit (the
canonical Smith exposure boundary), while the older `blockedPresentation`
trace only tells us indirectly that its first unresolved leaf is either

* an aligned section boundary, or
* the quarantined legacy rank-two presentation.

For the next global closure step we want those two origins to be impossible to
confuse.  This file splits the blocked trace into two typed head-normal forms.
The arbitrary already-certified presentation suffix is retained verbatim.

The legacy rank-two normal form intentionally keeps the historical
`target`/`CertifiedSameScaleEpisodeProgress` data only as provenance.  The
presentation itself still ends at `outer`; no recursive successor is inferred
from the old repair-only target.  Thus this normalization does not reintroduce
the bookkeeping bug isolated in A18.1--A18.4.2.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Typed residual heads -/

/-- A finite pure-presentation trace whose first unresolved origin is an
actual aligned section boundary.  Any later presentation suffix is retained
without inspection. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
    (RR : RepairRanking) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) →
      ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | head
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection) :
      AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace RR source
        (source.alignedBoundaryScaleAwareReentry B)

  | trans
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (first :
        AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace RR source middle)
      (second :
        AdaptiveAlignedSmithCanonicalPresentationTrace RR middle target) :
      AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace RR source target

/-- A finite pure-presentation trace whose first unresolved origin is the
historical rank-two macro.

The old same-scale `target` is deliberately retained inside the head witness,
but the presentation endpoint is only `outer`.  Consequently this type cannot
silently promote the bookkeeping target into a recursive state. -/
inductive AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
    (RR : RepairRanking) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) →
      ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | head
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (outer legacyTarget : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer source)
      (hprogress : CertifiedSameScaleEpisodeProgress RR legacyTarget outer) :
      AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace RR source outer

  | trans
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (first :
        AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace RR source middle)
      (second :
        AdaptiveAlignedSmithCanonicalPresentationTrace RR middle target) :
      AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace RR source target

/-! ## Forgetful maps remain honest internal presentations -/

/-- Forget the boundary-head refinement. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.toPresentationTrace
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalPresentationTrace RR source target := by
  induction trace with
  | head B =>
      exact .sectionBoundary B
  | trans first second ih =>
      exact .trans ih second

/-- A boundary-head trace is still only a certified pure ramified
presentation. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source :=
  trace.toPresentationTrace.toInternalMove

/-- Forget the legacy-head refinement. -/
theorem AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace.toPresentationTrace
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalPresentationTrace RR source target := by
  induction trace with
  | head outer legacyTarget hmove hprogress =>
      exact .legacyRankTwo outer legacyTarget hmove hprogress
  | trans first second ih =>
      exact .trans ih second

/-- A legacy-head trace is likewise only a certified pure ramified
presentation.  Its historical repair target is not used here. -/
theorem AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
      RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source :=
  trace.toPresentationTrace.toInternalMove

/-! ## Split the old blocked trace exactly at its first leaf -/

/-- Every A18.4.9 blocked trace has exactly one of the two typed unresolved
head forms.  No surviving-exact-clock origin is hidden in either case. -/
theorem AdaptiveAlignedSmithCanonicalBlockedPresentationTrace.boundaryHead_or_legacyRankTwoHead
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalBlockedPresentationTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace RR source target ∨
      AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace RR source target := by
  induction trace with
  | sectionBoundary B =>
      exact Or.inl (.head B)
  | legacyRankTwo outer legacyTarget hmove hprogress =>
      exact Or.inr (.head outer legacyTarget hmove hprogress)
  | trans first second ih =>
      rcases ih with hboundary | hlegacy
      · exact Or.inl (.trans hboundary second)
      · exact Or.inr (.trans hlegacy second)

/-! ## Global residual presentation normal form -/

/-- The two genuinely geometric boundary presentations are grouped under one
source-honest type.  This is still only an internal presentation: neither
boundary constructor is declared recursive progress. -/
inductive AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | exposure
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) source)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toAbsoluteBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target source) :
      AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation RR source target

  | aligned
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
        RR source target) :
      AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation RR source target

/-- Every grouped boundary object is an honest pure ramified presentation. -/
theorem AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
      RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source := by
  cases B with
  | exposure E target target_eq hmove =>
      exact hmove
  | aligned target trace =>
      exact trace.toInternalMove

/-- A18.4.13 global frontier.

The opaque `blockedPresentation` constructor is gone.  All genuine boundary
geometry is grouped into one constructor, while the historical rank-two head
is isolated separately.  Thus, apart from strict/pointed exits, there are now
only two kinds of non-strict residue:

1. honest boundary presentation;
2. quarantined legacy rank-two presentation.

This is the exact source-level split needed by the final two closure passes. -/
inductive AdaptiveAlignedSmithCanonicalGlobalResidualPresentationHeadOutcome
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

  | boundaryPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (B : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation RR s target)

  | legacyRankTwoPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (trace : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
        RR s target)

/-- **Residual presentation head normalization.**

A18.4.12 already removes every Smith-exposure overshoot.  Splitting the only
remaining blocked trace now yields the sharp final presentation census:
boundary geometry versus legacy rank-two provenance.  In particular, the
next rank-two repair pass no longer has to destruct an arbitrary blocked trace
to discover its origin, and the later boundary pass can work against one
common presentation interface. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalResidualPresentationHeadFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalResidualPresentationHeadOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalCanonicalExposureFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D

  | exactBoundaryPresentation E target target_eq hmove =>
      exact .boundaryPresentation target
        (.exposure E target target_eq hmove)

  | blockedPresentation target trace =>
      rcases trace.boundaryHead_or_legacyRankTwoHead with
        hboundary | hlegacy
      · exact .boundaryPresentation target (.aligned target hboundary)
      · exact .legacyRankTwoPresentation target hlegacy

end

end HC4.Valuation
