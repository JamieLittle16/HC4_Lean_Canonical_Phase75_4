import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedCompleteRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalBoundaryCompleteGlobalClosure
import Mathlib.Tactic

/-!
# A18.4.106: complete aligned section boundary is progress or rank three

A18.4.74 already proves that a separated right wall is a literal strict drop
in the discrete global key.  Its other boundary heads are canonical blocker or
surviving presentations.  A18.4.105 now consumes either presented endpoint
completely into retained rank-three geometry.

Thus a genuine aligned section boundary has exactly two sound behaviours:

* separated wall: strict global progress;
* coupled/primitive endpoint: complete rank-three geometry.

There is no zero-defect exception, presentation-only branch, rational spend,
or repair-only promotion.
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

/-- Final geometry-preserving boundary outcome. -/
inductive AdaptiveAlignedSmithCanonicalBoundaryRankThreeOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
  | rankThree
      (geometry : AdaptiveAlignedSmithCanonicalBoundaryRankThreeGeometry
        RR source complexity)

/-- **A18.4.106 complete aligned-boundary geometry.** -/
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
      rcases source.globalProgress_of_separatedRightWall
          (by simpa [F] using hsep) with ⟨target, hprogress⟩
      exact .globalProgress target hprogress

end

end HC4.Valuation
