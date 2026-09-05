import HC4.Valuation.AdaptiveAlignedSmithCanonicalCoupledPointedMinimality
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBoundaryEndpoint
import Mathlib.Tactic

/-!
# A18.4.61: the aligned boundary head has no ramified-spend edge

A18.4.60 proves that the determinant-one point normalisation of a genuinely
coupled first wall preserves symmetric Smith minimality.  Therefore the only
source of a ramified raw-defect spend in the A18.4.20 boundary closure is
unreachable.

This file reruns the aligned-boundary head without ever constructing the old
`GlobalRamifiedStrictMacro` wrapper.

There are exactly three outputs:

* an honest same-scale successor with strictly smaller raw determinant defect;
* a canonical blocker represented by a pure presentation of the source;
* a canonical surviving wall represented by a pure presentation of the source.

The first output is the separated-right-wall geometry from A18.4.16, exposed
directly as `CertifiedSameScaleEpisodeProgress`.  The coupled output is
classified directly using A18.4.60.  Thus this interface contains no
ramification spend, no rational defect comparison, and no generic strict-macro
constructor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A separated right wall is not merely a generic global macro: it gives an
actual successor at exactly the incoming absolute scale. -/
theorem ScaleAwareAdaptiveGeometricRestartState.sameScaleProgress_of_separatedRightWall
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hsep :
      HasSeparatedRightSmithSectionWall
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedSameScaleEpisodeProgress RR target s := by
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
  apply certifiedSameScaleEpisodeProgress_of_rawDefect_lt RR
  · rfl
  · simpa [target] using hlt

/-- Lossless no-spend result of one aligned section-boundary head. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBoundaryNoSpendOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | sameScale
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : CertifiedSameScaleEpisodeProgress RR target source)
  | blocker
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
  | surviving
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)

/-- **A18.4.61 no-spend aligned-boundary closure.**

The proof deliberately reuses the literal first boundary rather than passing
through the older macro-valued reductions.  This prevents the already
same-scale separated-wall descent from being forgotten into a generic
cross-scale wrapper. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.toPresentedNoSpendOutcome
    {RR : RepairRanking}
    {source tail : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source tail) :
    AdaptiveAlignedSmithCanonicalPresentedBoundaryNoSpendOutcome RR source := by
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
        exact .blocker {
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
    | surviving P W hEq =>
        let presented := P.toScaleOneState
        have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
          simpa [presented] using P.certifiedInternalMove
        exact .surviving {
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
          exact .blocker {
            presented := presented
            sourcePresentation := hmove
            blocker := Bcan
            defect_eq := by rw [hEq]; rfl
            family_eq := by rw [hEq]; rfl
            movingSection_eq := by rw [hEq]; rfl
          }
      | inr hW =>
          rcases hW with ⟨W, hEq⟩
          exact .surviving {
            presented := presented
            sourcePresentation := hmove
            wall := W
            defect_eq := by rw [hEq]; rfl
            family_eq := by rw [hEq]; rfl
            movingSection_eq := by rw [hEq]; rfl
          }

    · have hsep : HasSeparatedRightSmithSectionWall F source.movingSection :=
        ⟨B.hwall, hprimitive, hcoeff, hright⟩
      rcases source.sameScaleProgress_of_separatedRightWall RR
          (by simpa [F] using hsep) with ⟨target, hprogress⟩
      exact .sameScale target hprogress

end

end HC4.Valuation
