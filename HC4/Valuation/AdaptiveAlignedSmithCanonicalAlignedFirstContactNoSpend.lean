import HC4.Valuation.AdaptiveAlignedSmithCanonicalAlignedEndpointOrigin
import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryFirstContactNoSpend
import Mathlib.Tactic

/-!
# A18.4.63: provenance-sharp aligned first-contact frontier with no spend

A18.4.59 distinguishes the three genuine origins of a one-shot aligned Smith
endpoint.  A18.4.62 consumes a literal section boundary without a rational
recursive edge.  The exact-clock branch can be represented honestly at the
20-fold aligned scale and then consumed by A18.4.51/A18.4.53.  The positive
no-wall primitive order already gives A18.4.58's same-scale `Delta - 4*m`
restart.

After also eliminating the impossible canonical exposure boundary, only three
outputs remain:

* zero raw determinant defect;
* same-scale raw-defect descent after an explicitly retained pure presentation;
* finite global-key descent from a geometry-backed rank-two promotion.

There is no ramified raw spend, generic ramified strict macro, anonymous clock
loss, or surviving boundary presentation in this interface.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Final no-spend result of one provenance-sharp aligned first-contact
classification. -/
inductive AdaptiveAlignedSmithCanonicalAlignedFirstContactNoSpendOutcome
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

/-- The canonical exposure-boundary presentation is impossible, independently
of how many pure presentations preceded it. -/
theorem AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.noSpend_impossible
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) source) : False := by
  exact (E.exposure.noCanonicalSectionBoundary E.W) E.boundary

/-- Consume one already represented blocker into the three no-spend outputs. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.toAlignedNoSpendOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedFirstContactNoSpendOutcome
      RR source complexity := by
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

/-- Consume one already represented surviving wall into the three no-spend
outputs; its sole presentation leaf is contradictory. -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.toAlignedNoSpendOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedFirstContactNoSpendOutcome
      RR source complexity := by
  cases D.firstContactSoundReduction RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | presentedSameScale P =>
      exact .presentedSameScale P
  | globalProgress target h =>
      exact .globalProgress target h
  | exposureBoundaryPresentation presented E target target_eq hmove =>
      exact E.noSpend_impossible.elim

/-- Exact-clock aligned endpoints have only blocker/surviving no-spend
continuations. -/
theorem AdaptiveAlignedSmithCanonicalExactAlignedEndpoint.firstContactNoSpend
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalExactAlignedEndpoint (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedFirstContactNoSpendOutcome
      RR source complexity := by
  let Z := E.endpoint
  let presented := Z.toOuterScaleAwareState source
  have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
    simpa [presented, Z] using
      Z.hasCertifiedOuterInternal_of_exactClock (s := source) E.defect_eq
  cases Z.classifyCanonicalWall with
  | inl hB =>
      rcases hB with ⟨B, hEq⟩
      let D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source := {
        presented := presented
        sourcePresentation := hmove
        blocker := B
        defect_eq := by rw [hEq]; rfl
        family_eq := by rw [hEq]; rfl
        movingSection_eq := by rw [hEq]; rfl
      }
      exact D.toAlignedNoSpendOutcome RR complexity hsrepair
  | inr hW =>
      rcases hW with ⟨W, hEq⟩
      let D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source := {
        presented := presented
        sourcePresentation := hmove
        wall := W
        defect_eq := by rw [hEq]; rfl
        family_eq := by rw [hEq]; rfl
        movingSection_eq := by rw [hEq]; rfl
      }
      exact D.toAlignedNoSpendOutcome RR complexity hsrepair

/-- **A18.4.63 aligned first-contact no-spend theorem.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalFirstContactNoSpend
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedFirstContactNoSpendOutcome
      RR source complexity := by
  cases source.alignedSmithCanonicalEndpointOrigin RR with
  | exactEndpoint E =>
      exact E.firstContactNoSpend RR complexity hsrepair

  | noWallDefectDrop D =>
      exact .presentedSameScale {
        presented := source
        sourcePresentation := HasCertifiedRamifiedEpisodeInternalMove.identity source
        target := D.target
        progress := D.progress
      }

  | sectionBoundary B =>
      cases B.firstContactNoSpendGlobalAbsorption RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | presentedSameScale P =>
          exact .presentedSameScale P
      | globalProgress target h =>
          exact .globalProgress target h
      | exposureBoundaryPresentation presented E target target_eq hmove =>
          exact E.noSpend_impossible.elim

end

end HC4.Valuation
