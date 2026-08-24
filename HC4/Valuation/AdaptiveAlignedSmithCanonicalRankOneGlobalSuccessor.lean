import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryCompleteGlobalClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalAlignedEndpointOrigin
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
import Mathlib.Tactic

/-!
# A18.4.75: complete rank-one aligned episode has a global successor

A18.4.70, A18.4.73 and A18.4.74 remove every presentation-only and
cross-scale recursive leaf from exact endpoints and section boundaries.
A18.4.58 gives an explicit same-scale raw-defect drop in the positive no-wall
primitive case.  A18.4.40 supplies actual transverse rank-two Hessian geometry
when the incoming raw defect is zero.

This file assembles those pieces into the clean well-founded statement needed
by the global recursion skeleton: every canonical rank-one collision state has
one strict successor in the discrete global macro order.

The theorem below is intentionally *not* the final HC4 terminal theorem.  The
individual constructors used to build the successor retain their geometric
rank-two witnesses in the preceding files.  A later lossless frontier will use
those witnesses to close the finite-rank endgame rather than treating the
repair tag itself as geometry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Positive no-wall primitive order gives strict global progress directly on
the original scale, with the repair state unchanged by construction. -/
theorem ScaleAwareAdaptiveGeometricRestartState.noWallPrimitive_globalProgress
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
      source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (hm : 0 < D.m) :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      (source.noWallUnramifiedPrimitiveTarget D) source := by
  have hle : 4 * D.m ≤ source.rawDefect :=
    four_mul_le_defect_of_commonParameterFactor
      D.m D.smithData.smithFamily D.commonFactor source.rawDefect
      D.smithData.smithFamily_hessianDefect
  have hlt : source.rawDefect - 4 * D.m < source.rawDefect := by
    omega
  exact
    (certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_rawDefect_lt
      (K := K)
      (t := source.noWallUnramifiedPrimitiveTarget D)
      (s := source)
      rfl rfl (by simpa using hlt)).progress

/-- Exact-clock endpoint closure after all first-contact repairs. -/
theorem AdaptiveAlignedSmithCanonicalExactAlignedEndpoint.completeGlobalSuccessor
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalExactAlignedEndpoint (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
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
      cases D.completeSoundClosure RR complexity hsrepair with
      | globalProgress target h => exact ⟨target, h⟩
      | zeroDefect hzero =>
          let P := source.zeroDefect_globalRankTwoProgress
            RR source complexity hsrepair hzero
          exact ⟨P.target, P.globalProgress⟩
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
      cases D.completeSoundReduction RR complexity hsrepair with
      | globalProgress target h => exact ⟨target, h⟩
      | zeroDefect hzero =>
          let P := source.zeroDefect_globalRankTwoProgress
            RR source complexity hsrepair hzero
          exact ⟨P.target, P.globalProgress⟩
      | exposureBoundaryPresentation presented E target target_eq hmove =>
          exact ((E.exposure.noCanonicalSectionBoundary E.W) E.boundary).elim

/-- **A18.4.75 complete canonical rank-one global successor.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalRankOneGlobalSuccessor
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
  cases source.alignedSmithCanonicalEndpointOrigin RR with
  | exactEndpoint E =>
      exact E.completeGlobalSuccessor RR complexity hsrepair

  | noWallDefectDrop D =>
      let target := source.noWallUnramifiedPrimitiveTarget D.primitive
      exact ⟨target,
        source.noWallPrimitive_globalProgress D.primitive D.m_pos⟩

  | sectionBoundary B =>
      cases B.completeGlobalAbsorption RR complexity hsrepair with
      | globalProgress target h => exact ⟨target, h⟩
      | zeroDefect hzero =>
          let P := source.zeroDefect_globalRankTwoProgress
            RR source complexity hsrepair hzero
          exact ⟨P.target, P.globalProgress⟩

end

end HC4.Valuation
