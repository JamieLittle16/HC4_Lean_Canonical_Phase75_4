import HC4.Valuation.AdaptiveAlignedSmithCanonicalAlignedEndpointOrigin
import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneGlobalSuccessor
import Mathlib.Tactic

/-!
# A18.4.107/108: one complete aligned episode is strict rank-one restart or rank three

The provenance-sharp aligned endpoint has only three origins.

* Exact aligned clock: classify the retained endpoint as a blocker or
  surviving wall, then obtain complete rank-three geometry.
* Positive no-wall primitive order: the honest unramified quotient has a
  strict natural raw-defect drop with repair metadata unchanged.
* Genuine section boundary: the only recursive branch is a separated right
  wall, again with a strict natural raw-defect drop and unchanged repair.

The recursive constructor deliberately stores these two extra facts instead
of exposing only an abstract global-macro comparison.  This makes the final
well-founded induction a plain induction on `rawDefect : ℕ` and prevents a
repair-only relabelling from ever being used recursively.
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

/-- Complete local aligned outcome.  A recursive target is still canonical
rank one whenever the source is, and has strictly smaller natural raw defect. -/
inductive AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgressOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
      (rawDefect_lt : target.rawDefect < source.rawDefect)
      (repair_eq : target.repair = source.repair)
  | rankThree
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        RR source complexity)

/-- **Complete provenance-sharp aligned episode with a genuinely recursive
rank-one edge.** -/
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
      let target := source.noWallUnramifiedPrimitiveTarget D.primitive
      have hle : 4 * D.primitive.m ≤ source.rawDefect :=
        four_mul_le_defect_of_commonParameterFactor
          D.primitive.m
          D.primitive.smithData.smithFamily
          D.primitive.commonFactor
          source.rawDefect
          D.primitive.smithData.smithFamily_hessianDefect
      have hraw : target.rawDefect < source.rawDefect := by
        change source.rawDefect - 4 * D.primitive.m < source.rawDefect
        omega
      exact .globalProgress target
        (source.noWallPrimitive_globalProgress D.primitive D.m_pos)
        hraw rfl

  | sectionBoundary B =>
      cases B.rankThreeAbsorption RR complexity hsrepair with
      | globalProgress target h hraw hrepair =>
          exact .globalProgress target h hraw hrepair
      | rankThree G =>
          exact .rankThree (.boundary G)

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
