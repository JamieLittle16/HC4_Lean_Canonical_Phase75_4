import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingCompleteClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryNoSpendClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExposureNoBoundary
import Mathlib.Tactic

/-!
# A18.4.74: aligned section boundary closes by zero or global progress

A18.4.61 already showed that an aligned section-boundary head has only three
geometric origins: separated-right-wall raw-defect descent, a presented
blocker, or a presented surviving wall.  A18.4.70 and A18.4.73 now close the
latter two without any same-scale recursive output.

This file reruns only that finite head classification and consumes each result
immediately.  The separated wall is packaged directly as strict global macro
progress using its literal raw-defect drop and unchanged repair state.  The
canonical exposure-boundary leaf on the surviving side is contradictory.

Hence a genuine aligned section boundary has exactly two final outcomes:
literal zero raw defect, or strict progress in the well-founded global key.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A separated right wall gives strict global progress directly, not merely a
fixed-scale certificate. -/
theorem ScaleAwareAdaptiveGeometricRestartState.globalProgress_of_separatedRightWall
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hsep :
      HasSeparatedRightSmithSectionWall
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
  rcases separatedRightSmithWall_strictAdaptiveGeometricRestart
      s.degreeCap
      (zeroJetNormalizedFamily s.family)
      s.normalized_nonlinearDegreeBound
      s.movingSection hsep
      s.normalized_hessianDefect
      s.normalized_exactCollision
      s.sectionSpecial with
    ⟨Delta', hlt, P', b', hP'def, hP'degree, hP'coll, hb'⟩
  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := Delta'
      scale := s.scale
      scale_pos := s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := P'
      movingSection := b'
      hessianDefect := hP'def
      nonlinearDegreeBound := hP'degree
      exactCollision := by
        simpa [zeroPolynomialSection] using hP'coll
      sectionSpecial := hb' }
  refine ⟨target, ?_⟩
  exact
    (certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_rawDefect_lt
      (K := K) (t := target) (s := s) rfl rfl
      (by simpa [target] using hlt)).progress

/-- Complete global result of consuming one aligned section-boundary head. -/
inductive AdaptiveAlignedSmithCanonicalBoundaryCompleteGlobalOutcome
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)

/-- **A18.4.74 complete aligned-boundary global closure.** -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.completeGlobalAbsorption
    {RR : RepairRanking}
    {source tail : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source tail)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalBoundaryCompleteGlobalOutcome source := by
  rcases trace.exists_head_boundary with ⟨B, htail⟩
  let F := zeroJetNormalizedFamily source.family

  have hright :
      alignedSmithGenuineFirstWall
          F (zeroPolynomialSection (K := K)) source.movingSection B.hwall ∈
        alignedSmithSectionWalls source.movingSection := by
    rcases B.boundary with hleft | hright
    · rcases hleft with ⟨i, hi0, hmem, hne⟩
      exact False.elim
        ((not_mem_alignedSmithSectionWalls_zeroPolynomialSection
            (K := K)
            (alignedSmithGenuineFirstWall
              F (zeroPolynomialSection (K := K)) source.movingSection B.hwall))
          hmem)
    · rcases hright with ⟨i, hi0, hmem, hne⟩
      exact hmem

  by_cases hprimitive : HasPrimitiveZeroSmithSource F
  · cases source.primitiveCanonicalClassifier hprimitive with
    | blocker P Bcan hEq =>
        let presented := P.toScaleOneState
        have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
          simpa [presented] using P.certifiedInternalMove
        let D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source := {
          presented := presented
          sourcePresentation := hmove
          blocker := Bcan
          defect_eq := by
            rw [hEq]
            rfl
          family_eq := by
            rw [hEq]
            rfl
          movingSection_eq := by
            rw [hEq]
            rfl
        }
        cases D.completeSoundClosure RR complexity hsrepair with
        | zeroDefect hzero => exact .zeroDefect hzero
        | globalProgress target h => exact .globalProgress target h

    | surviving P W hEq =>
        let presented := P.toScaleOneState
        have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
          simpa [presented] using P.certifiedInternalMove
        let D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source := {
          presented := presented
          sourcePresentation := hmove
          wall := W.original
          defect_eq := by
            rw [hEq]
            rfl
          family_eq := by
            rw [hEq]
            rfl
          movingSection_eq := by
            rw [hEq]
            rfl
        }
        cases D.completeSoundReduction RR complexity hsrepair with
        | zeroDefect hzero => exact .zeroDefect hzero
        | globalProgress target h => exact .globalProgress target h
        | exposureBoundaryPresentation presented E target target_eq hmove =>
            exact ((E.exposure.noCanonicalSectionBoundary E.W) E.boundary).elim

  · by_cases hcoeff :
        alignedSmithGenuineFirstWall
            F (zeroPolynomialSection (K := K)) source.movingSection B.hwall ∈
          alignedSmithCoefficientWalls F
    · let P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation
          (K := K) source :=
        source.coupledMinimalPresentation B hprimitive
          ⟨B.hwall, hcoeff, Or.inr hright⟩
      let PP := P.toPointedPresentation
      have hminimal := PP.pointedSpecialFiber_symmetricMinimal
      let E₀ : AdaptiveAlignedSmithMinimalEndpoint (K := K) source.degreeCap :=
        { defect := alignedSmithRamificationIndex * source.rawDefect
          family := PP.source.pointedFamily
          movingSection := PP.source.pointedSection
          hessianDefect := PP.hessianDefect
          nonlinearDegreeBound := PP.nonlinearDegreeBound
          exactCollision := PP.exactCollision
          sectionSpecial := PP.sectionSpecial
          symmetricMinimal := hminimal }
      let E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
          (K := K) source.degreeCap :=
        { endpoint := E₀
          zeroSourceJet := PP.zeroSourceJet }
      let presented := E.toOuterScaleAwareState source
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        simpa [presented] using
          E.hasCertifiedOuterInternal_of_exactClock (s := source) (by rfl)
      cases E.classifyCanonicalWall with
      | inl hB =>
          rcases hB with ⟨Bcan, hEq⟩
          let D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source := {
            presented := presented
            sourcePresentation := hmove
            blocker := Bcan
            defect_eq := by rw [hEq]; rfl
            family_eq := by rw [hEq]; rfl
            movingSection_eq := by rw [hEq]; rfl
          }
          cases D.completeSoundClosure RR complexity hsrepair with
          | zeroDefect hzero => exact .zeroDefect hzero
          | globalProgress target h => exact .globalProgress target h
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
          | zeroDefect hzero => exact .zeroDefect hzero
          | globalProgress target h => exact .globalProgress target h
          | exposureBoundaryPresentation presented E target target_eq hmove =>
              exact ((E.exposure.noCanonicalSectionBoundary E.W) E.boundary).elim

    · have hsep : HasSeparatedRightSmithSectionWall F source.movingSection :=
        ⟨B.hwall, hprimitive, hcoeff, hright⟩
      rcases source.globalProgress_of_separatedRightWall
          (by simpa [F] using hsep) with ⟨target, hprogress⟩
      exact .globalProgress target hprogress

/-- Literal section-boundary specialization. -/
theorem AdaptiveAlignedSmithSectionBoundaryEndpoint.completeGlobalAbsorption
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalBoundaryCompleteGlobalOutcome source := by
  exact (AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.head
    (RR := RR) B).completeGlobalAbsorption complexity hsrepair

end

end HC4.Valuation
