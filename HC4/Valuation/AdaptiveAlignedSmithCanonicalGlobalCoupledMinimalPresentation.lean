import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPrimitiveBoundaryEntry
import Mathlib.Tactic

/-!
# A18.4.18: mixed-degree coupled-wall minimal presentation

A18.4.16 reduced an aligned section-boundary head to genuine strict progress,
a primitive source, or a coupled coefficient/right-section wall.  A18.4.17
consumed the primitive source directly through the canonical minimal-wall
classifier.

The remaining coupled constructor is not a failure of Smith minimality.  By
definition it is already a genuine coefficient first wall, and the existing
coefficient-wall theorem proves symmetric Smith minimality without any source
homogeneity hypothesis.  What prevents immediate canonical classification is
only that the simultaneous right-section wall moves the marked special point
away from `e0`.

This file records exactly that source-honest intermediate object.  A coupled
boundary remembers

* the actual aligned boundary endpoint;
* the simultaneous coefficient-wall witness;
* the genuine right-section-wall witness;
* symmetric minimality of the actual first-wall special fibre; and
* zero-source-jet provenance of that same first-wall family.

No global homogeneity is assumed and the obsolete homogeneous coupled-wall
impossibility theorem is not used.  The next geometric step may therefore
focus solely on pointed normalisation of the marked right section.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The exact mixed-degree data carried by a coupled aligned boundary.

The transformed family is already symmetric-Smith minimal.  Its remaining
noncanonical feature is the simultaneous right-section wall. -/
structure AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop where
  boundary :
    AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection
  coefficientWall :
    alignedSmithGenuineFirstWall
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection boundary.hwall ∈
      alignedSmithCoefficientWalls
        (zeroJetNormalizedFamily s.family)
  rightSectionWall :
    alignedSmithGenuineFirstWall
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection boundary.hwall ∈
      alignedSmithSectionWalls s.movingSection
  symmetricMinimal :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber
          (alignedSmithGenuineFirstWallFamily
            (K := K)
            (zeroJetNormalizedFamily s.family)
            (zeroPolynomialSection (K := K))
            s.movingSection boundary.hwall)))
      0
      (fun _ => (0 : ℤ))
  zeroSourceJet :
    HasZeroSourceJet
      (alignedSmithGenuineFirstWallFamily
        (K := K)
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection boundary.hwall)

/-- A literal coupled boundary on a normalized scale-aware state already
supplies a mixed-degree minimal presentation.  The left-section alternative
inside the generic coupled-wall predicate is impossible because that section
is identically zero, so the simultaneous section wall is genuinely on the
moving right section. -/
theorem ScaleAwareAdaptiveGeometricRestartState.coupledMinimalPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection)
    (hcoupled :
      HasCoupledAlignedSmithWall
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection) :
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s := by
  rcases hcoupled with ⟨hwall, hcoeff, hsection⟩
  have hwall_eq : hwall = B.hwall := Subsingleton.elim _ _
  subst hwall
  have hright :
      alignedSmithGenuineFirstWall
          (zeroJetNormalizedFamily s.family)
          (zeroPolynomialSection (K := K))
          s.movingSection B.hwall ∈
        alignedSmithSectionWalls s.movingSection := by
    rcases hsection with hleft | hright
    · exact False.elim
        ((not_mem_alignedSmithSectionWalls_zeroPolynomialSection
            (K := K)
            (alignedSmithGenuineFirstWall
              (zeroJetNormalizedFamily s.family)
              (zeroPolynomialSection (K := K))
              s.movingSection B.hwall)) hleft)
    · exact hright
  have hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber
            (alignedSmithGenuineFirstWallFamily
              (K := K)
              (zeroJetNormalizedFamily s.family)
              (zeroPolynomialSection (K := K))
              s.movingSection B.hwall)))
        0
        (fun _ => (0 : ℤ)) :=
    genuineCoefficientWall_specialFiber_symmetricMinimal
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection B.hwall hcoeff
  have hzero :
      HasZeroSourceJet
        (alignedSmithGenuineFirstWallFamily
          (K := K)
          (zeroJetNormalizedFamily s.family)
          (zeroPolynomialSection (K := K))
          s.movingSection B.hwall) :=
    (zeroJetNormalizedFamily_hasZeroSourceJet s.family).
      alignedSmithGenuineFirstWallFamily
        (zeroPolynomialSection (K := K))
        s.movingSection B.hwall
  exact
    { boundary := B
      coefficientWall := hcoeff
      rightSectionWall := hright
      symmetricMinimal := hminimal
      zeroSourceJet := hzero }

/-! ## Replace the bare coupled residue by typed minimal data -/

/-- After A18.4.18 every aligned-boundary head is either already recursive
strict progress, a primitive canonical blocker/surviving endpoint, or a
coupled *minimal* first-wall presentation whose only outstanding issue is
point normalisation. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadMinimalOutcome
    (RR : RepairRanking)
    (source target : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | strictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)

  | primitiveBlocker
      (B₀ : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B₀))
      (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation
        (K := K) source)
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) source.degreeCap)
      (aligned_eq : B.aligned = P.endpoint)

  | primitiveSurviving
      (B₀ : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B₀))
      (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation
        (K := K) source)
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) source)
      (aligned_eq : W.original.aligned = P.endpoint)

  | coupledMinimal
      (B₀ : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B₀))
      (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation
        (K := K) source)
      (boundary_eq : P.boundary = B₀)

/-- Consume the bare coupled constructor of A18.4.17 by exposing the actual
minimal first-wall geometry it already contains. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.minimalReduction
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadMinimalOutcome
      RR source target := by
  cases trace.canonicalReduction with
  | strictMacro D =>
      exact .strictMacro D
  | primitiveBlocker B₀ htail P B hEq =>
      exact .primitiveBlocker B₀ htail P B hEq
  | primitiveSurviving B₀ htail P W hEq =>
      exact .primitiveSurviving B₀ htail P W hEq
  | coupled B₀ htail hcoupled =>
      let P := source.coupledMinimalPresentation B₀ hcoupled
      exact .coupledMinimal B₀ htail P rfl

end

end HC4.Valuation
