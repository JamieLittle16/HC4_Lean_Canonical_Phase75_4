import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedCompleteRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryCompleteGlobalClosure
import Mathlib.Tactic

/-!
# A18.4.106/108: complete aligned section boundary is strict rank-one progress or rank three

A genuine aligned section boundary has exactly two sound behaviours:

* a separated right wall gives a literal strict raw-defect drop on the same
  repair state;
* a coupled/primitive endpoint carries complete retained rank-three geometry.

For the final well-founded induction it is important not to erase the first
fact into a generic global-macro comparison.  The `globalProgress` constructor
therefore retains both the strict natural raw-defect inequality and equality
of the repair state.  Consequently recursive use of this interface can never
silently recurse through a repair-only rank promotion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Rank-three geometry produced by a canonical aligned boundary head. -/
inductive AdaptiveAlignedSmithCanonicalBoundaryRankThreeGeometry
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | blocker
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        RR D complexity)
  | surviving
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
        RR D complexity)

/-- Final geometry-preserving boundary outcome.  The recursive constructor is
an honest rank-one restart: its raw determinant clock strictly decreases and
its repair metadata is unchanged. -/
inductive AdaptiveAlignedSmithCanonicalBoundaryRankThreeOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
      (rawDefect_lt : target.rawDefect < source.rawDefect)
      (repair_eq : target.repair = source.repair)
  | rankThree
      (geometry : AdaptiveAlignedSmithCanonicalBoundaryRankThreeGeometry
        RR source complexity)

/-- **Complete aligned-boundary geometry with lossless recursive provenance.** -/
noncomputable def
    AdaptiveAlignedSmithSectionBoundaryEndpoint.rankThreeAbsorption
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalBoundaryRankThreeOutcome
      RR source complexity := by
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
            simpa [presented] using P.defect_eq
          family_eq := by
            rw [hEq]
            simpa [presented] using P.family_eq
          movingSection_eq := by
            rw [hEq]
            simpa [presented] using P.movingSection_eq
        }
        exact .rankThree (.blocker D (D.allRankThreeGeometry RR complexity hsrepair))

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
            simpa [presented] using P.defect_eq
          family_eq := by
            rw [hEq]
            simpa [presented] using P.family_eq
          movingSection_eq := by
            rw [hEq]
            simpa [presented] using P.movingSection_eq
        }
        exact .rankThree (.surviving D (D.allRankThreeGeometry RR complexity hsrepair))

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
          exact .rankThree (.blocker D (D.allRankThreeGeometry RR complexity hsrepair))
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
          exact .rankThree (.surviving D (D.allRankThreeGeometry RR complexity hsrepair))

    · have hsep : HasSeparatedRightSmithSectionWall F source.movingSection :=
        ⟨B.hwall, hprimitive, hcoeff, hright⟩
      rcases separatedRightSmithWall_strictAdaptiveGeometricRestart
          source.degreeCap
          (zeroJetNormalizedFamily source.family)
          source.normalized_nonlinearDegreeBound
          source.movingSection
          (by simpa [F] using hsep)
          source.normalized_hessianDefect
          source.normalized_exactCollision
          source.sectionSpecial with
        ⟨Delta', hlt, P', b', hP'def, hP'degree, hP'coll, hb'⟩
      let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
        { rawDefect := Delta'
          scale := source.scale
          scale_pos := source.scale_pos
          degreeCap := source.degreeCap
          sourceComplexity := source.sourceComplexity
          repair := source.repair
          family := P'
          movingSection := b'
          hessianDefect := hP'def
          nonlinearDegreeBound := hP'degree
          exactCollision := by
            simpa [zeroPolynomialSection] using hP'coll
          sectionSpecial := hb' }
      have hprogress :
          AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source :=
        (certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_rawDefect_lt
          (K := K) (t := target) (s := source) rfl rfl
          (by simpa [target] using hlt)).progress
      exact .globalProgress target hprogress
        (by simpa [target] using hlt) rfl

end

end HC4.Valuation
