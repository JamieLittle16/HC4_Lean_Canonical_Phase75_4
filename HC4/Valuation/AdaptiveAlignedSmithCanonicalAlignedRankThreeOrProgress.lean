import HC4.Valuation.AdaptiveAlignedSmithCanonicalAlignedEndpointOrigin
import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneGlobalSuccessor
import Mathlib.Tactic

/-!
# A18.4.107: one complete aligned episode is progress or rank three

The provenance-sharp aligned endpoint has only three origins.

* Exact aligned clock: classify the retained endpoint as a blocker or
  surviving wall, then use A18.4.105 to obtain complete rank-three geometry.
* Positive no-wall primitive order: A18.4.58/A18.4.75 give a literal strict
  same-scale raw-defect drop.
* Genuine section boundary: A18.4.106 gives either the same discrete progress
  or complete rank-three geometry.

This is the final nonrecursive local statement needed by the well-founded
rank-one induction.  No repair-only finite-rank exit remains.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete rank-three geometry produced by one exact or boundary aligned
episode. -/
inductive AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | exactBlocker
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        RR D complexity)
  | exactSurviving
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
        RR D complexity)
  | boundary
      (geometry : AdaptiveAlignedSmithCanonicalBoundaryRankThreeGeometry
        RR source complexity)

/-- Complete local aligned outcome: recurse only on a strict discrete global
key, otherwise retain complete rank-three geometry. -/
inductive AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgressOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
  | rankThree
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        RR source complexity)

/-- **A18.4.107 complete provenance-sharp aligned episode.** -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalRankThreeOrProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgressOutcome
      RR source complexity := by
  cases source.alignedSmithCanonicalEndpointOrigin RR with
  | noWallDefectDrop D =>
      exact .globalProgress D.target
        (source.noWallPrimitive_globalProgress D.primitive D.m_pos)

  | sectionBoundary B =>
      cases B.rankThreeAbsorption RR complexity hsrepair with
      | globalProgress target h => exact .globalProgress target h
      | rankThree G => exact .rankThree (.boundary G)

  | exactEndpoint E =>
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
          exact .rankThree (.exactBlocker D
            (D.allRankThreeGeometry RR complexity hsrepair))
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
          exact .rankThree (.exactSurviving D
            (D.allRankThreeGeometry RR complexity hsrepair))

end

end HC4.Valuation
