import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalResidualPresentationHeadNormalization
import Mathlib.Tactic

/-!
# A18.4.15: lossless origin split for the final presentation residues

A18.4.13 makes the two non-strict global residues explicit: boundary
presentation and quarantined legacy rank-two provenance.  A18.4.14 then
continues the global frontier through an actual boundary presentation, so a
non-strict continuation can only consist of another boundary or a legacy
rank-two head after that presentation.

The next geometric elimination must not reason about an opaque composite
presentation.  This file therefore exposes the exact source of those two
residues without claiming that either is progress.

For a repeated boundary there are exactly four source-honest combinations:

* canonical exposure boundary followed by canonical exposure boundary;
* canonical exposure boundary followed by an aligned section-boundary head;
* aligned section-boundary head followed by canonical exposure boundary;
* aligned section-boundary head followed by another aligned boundary head.

Likewise a boundary followed by legacy rank-two provenance has exactly two
origins according to the first boundary kind.

The file also proves head-factorisation lemmas for the two A18.4.13 typed
traces.  They recover the actual first aligned boundary / legacy producer and
package the remainder only as an honest internal presentation.  These are the
interfaces needed by the final geometric elimination: no repair-only target
is promoted and no presentation is declared recursive progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Recover the actual first producer from typed head traces -/

/-- An aligned-boundary head trace really starts with one concrete aligned
section boundary.  Everything after that first boundary is still only a pure
presentation.

This theorem is intentionally existential in the boundary witness: it strips
arbitrary presentation suffixes while retaining the actual first geometric
wall. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.exists_head_boundary
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    ∃ B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection,
      HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B) := by
  induction trace with
  | head B =>
      exact ⟨B,
        HasCertifiedRamifiedEpisodeInternalMove.identity _⟩
  | trans first second ih =>
      rcases ih with ⟨B, htail⟩
      exact ⟨B, htail.trans second.toInternalMove⟩

/-- A legacy-rank-two head trace really starts with one concrete old producer.
The potentially bookkeeping-only `legacyTarget` is returned only as provenance;
the endpoint of the trace is reached from the honest `outer` by pure
presentation moves. -/
theorem AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace.exists_head_legacy
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
      RR source target) :
    ∃ outer legacyTarget : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedEpisodeInternalMove outer source ∧
      CertifiedSameScaleEpisodeProgress RR legacyTarget outer ∧
      HasCertifiedRamifiedEpisodeInternalMove target outer := by
  induction trace with
  | head outer legacyTarget hmove hprogress =>
      exact ⟨outer, legacyTarget, hmove, hprogress,
        HasCertifiedRamifiedEpisodeInternalMove.identity outer⟩
  | trans first second ih =>
      rcases ih with ⟨outer, legacyTarget, hmove, hprogress, htail⟩
      exact ⟨outer, legacyTarget, hmove, hprogress,
        htail.trans second.toInternalMove⟩

/-! ## Exact four-way split of two consecutive boundary presentations -/

/-- Lossless geometric origin of two consecutive global boundary
presentations.

The four constructors retain the original endpoint witnesses and certified
moves.  In the aligned cases the typed head trace is kept intact, so its first
actual section wall can later be recovered by `exists_head_boundary`.
-/
inductive AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
    (RR : RepairRanking) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) →
      ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | exposureExposure
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (E₁ : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) source)
      (middle_eq : middle = E₁.toAbsoluteBoundaryState)
      (h₁ : HasCertifiedRamifiedEpisodeInternalMove middle source)
      (E₂ : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) middle)
      (target_eq : target = E₂.toAbsoluteBoundaryState)
      (h₂ : HasCertifiedRamifiedEpisodeInternalMove target middle) :
      AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
        RR source target

  | exposureAligned
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) source)
      (middle_eq : middle = E.toAbsoluteBoundaryState)
      (h₁ : HasCertifiedRamifiedEpisodeInternalMove middle source)
      (second : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
        RR middle target) :
      AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
        RR source target

  | alignedExposure
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (first : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
        RR source middle)
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) middle)
      (target_eq : target = E.toAbsoluteBoundaryState)
      (h₂ : HasCertifiedRamifiedEpisodeInternalMove target middle) :
      AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
        RR source target

  | alignedAligned
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (first : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
        RR source middle)
      (second : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
        RR middle target) :
      AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
        RR source target

/-- Two grouped boundary presentations have exactly one of the four explicit
origin forms above. -/
theorem AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin.of_presentations
    {RR : RepairRanking}
    {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (first : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
      RR source middle)
    (second : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
      RR middle target) :
    AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
      RR source target := by
  cases first with
  | exposure E middle middle_eq h₁ =>
      cases second with
      | exposure E₂ target target_eq h₂ =>
          exact .exposureExposure E middle_eq h₁ E₂ target_eq h₂
      | aligned target trace₂ =>
          exact .exposureAligned E middle_eq h₁ trace₂
  | aligned middle trace₁ =>
      cases second with
      | exposure E target target_eq h₂ =>
          exact .alignedExposure trace₁ E target_eq h₂
      | aligned target trace₂ =>
          exact .alignedAligned trace₁ trace₂

/-- A repeated boundary pair is still exactly one pure ramified presentation
from the original source.  No strictness is inferred from the repetition. -/
theorem AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (R : AdaptiveAlignedSmithCanonicalGlobalRepeatedBoundaryOrigin
      RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source := by
  cases R with
  | exposureExposure E₁ middle_eq h₁ E₂ target_eq h₂ =>
      exact h₁.trans h₂
  | exposureAligned E middle_eq h₁ second =>
      exact h₁.trans second.toInternalMove
  | alignedExposure first E target_eq h₂ =>
      exact first.toInternalMove.trans h₂
  | alignedAligned first second =>
      exact first.toInternalMove.trans second.toInternalMove

/-! ## Boundary followed by the quarantined legacy head -/

/-- Exact origin split when a boundary continuation lands in legacy rank-two
provenance.  Again the old repair target is retained only inside the legacy
head trace and is never promoted to a recursive state. -/
inductive AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin
    (RR : RepairRanking) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) →
      ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | exposureLegacy
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) source)
      (middle_eq : middle = E.toAbsoluteBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove middle source)
      (legacy : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
        RR middle target) :
      AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin
        RR source target

  | alignedLegacy
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (boundary : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
        RR source middle)
      (legacy : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
        RR middle target) :
      AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin
        RR source target

/-- Split a grouped boundary followed by a legacy head according to the actual
boundary origin. -/
theorem AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin.of_presentations
    {RR : RepairRanking}
    {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (boundary : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
      RR source middle)
    (legacy : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
      RR middle target) :
    AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin
      RR source target := by
  cases boundary with
  | exposure E middle middle_eq hmove =>
      exact .exposureLegacy E middle_eq hmove legacy
  | aligned middle trace =>
      exact .alignedLegacy trace legacy

/-- Boundary followed by legacy provenance is likewise only a composite pure
presentation from the original source. -/
theorem AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (R : AdaptiveAlignedSmithCanonicalGlobalBoundaryThenLegacyOrigin
      RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source := by
  cases R with
  | exposureLegacy E middle_eq hmove legacy =>
      exact hmove.trans legacy.toInternalMove
  | alignedLegacy boundary legacy =>
      exact boundary.toInternalMove.trans legacy.toInternalMove

end

end HC4.Valuation
