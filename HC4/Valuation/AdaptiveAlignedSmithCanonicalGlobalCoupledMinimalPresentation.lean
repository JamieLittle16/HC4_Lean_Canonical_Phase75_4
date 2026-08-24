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

For the later pointed-normalisation argument we also retain the logically
important fact that this branch is nonprimitive.  That datum was known in the
A18.4.16 case split but its first output type intentionally did not store it.
Here we re-run the source-honest primitive split at the head: a primitive
source is immediately consumed by the A18.4.17 classifier, while the coupled
constructor is formed only in the complementary nonprimitive branch.

This has a strong homogeneity-free consequence already proved in the tree:
at a positive genuine first wall with no primitive zero Smith source, every
monomial surviving on the first-wall special fibre has strictly negative
symmetric Smith derivative.  We retain that fact explicitly as the finite
low-pattern input for the next pointed-shear patch.

No global homogeneity is assumed and the obsolete homogeneous coupled-wall
impossibility theorem is not used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The exact mixed-degree data carried by a genuinely residual coupled
aligned boundary.

The transformed family is already symmetric-Smith minimal, and indeed every
surviving special-fibre monomial has negative symmetric Smith derivative.  Its
remaining noncanonical feature is the simultaneous right-section wall. -/
structure AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop where
  boundary :
    AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection
  noPrimitive :
    ¬ HasPrimitiveZeroSmithSource (zeroJetNormalizedFamily s.family)
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
  allSpecialFiberNegative :
    ∀ {d : Fin 4 →₀ ℕ},
      d ∈
          (polynomialFamilySpecialFiber
            (alignedSmithGenuineFirstWallFamily
              (K := K)
              (zeroJetNormalizedFamily s.family)
              (zeroPolynomialSection (K := K))
              s.movingSection boundary.hwall)).support →
        smithSeparatorDelta 1 1 (smithAxisProjection d) < 0

/-- A nonprimitive coupled boundary on a normalized scale-aware state already
supplies a mixed-degree minimal presentation.  The left-section alternative
inside the generic coupled-wall predicate is impossible because that section
is identically zero, so the simultaneous section wall is genuinely on the
moving right section. -/
theorem ScaleAwareAdaptiveGeometricRestartState.coupledMinimalPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource (zeroJetNormalizedFamily s.family))
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
  have hNpos :
      0 <
        alignedSmithGenuineFirstWall
          (zeroJetNormalizedFamily s.family)
          (zeroPolynomialSection (K := K))
          s.movingSection B.hwall :=
    alignedSmithSectionWall_step_pos
      s.movingSection
      (specialPoint_axis_transverse_constantCoeff
        s.movingSection s.sectionSpecial)
      hright
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
  have hnegative :
      ∀ {d : Fin 4 →₀ ℕ},
        d ∈
            (polynomialFamilySpecialFiber
              (alignedSmithGenuineFirstWallFamily
                (K := K)
                (zeroJetNormalizedFamily s.family)
                (zeroPolynomialSection (K := K))
                s.movingSection B.hwall)).support →
          smithSeparatorDelta 1 1 (smithAxisProjection d) < 0 := by
    intro d hd
    exact
      genuineFirstWall_specialFiber_negativeSmith_of_noPrimitive
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection B.hwall hNpos hnoPrimitive hd
  exact
    { boundary := B
      noPrimitive := hnoPrimitive
      coefficientWall := hcoeff
      rightSectionWall := hright
      symmetricMinimal := hminimal
      zeroSourceJet := hzero
      allSpecialFiberNegative := hnegative }

/-! ## Replace the bare coupled residue by typed minimal data -/

/-- After A18.4.18 every aligned-boundary head is either already recursive
strict progress, a primitive canonical blocker/surviving endpoint, or a
nonprimitive coupled *minimal* first-wall presentation whose only outstanding
issue is point normalisation. -/
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

/-- Re-run the primitive/nonprimitive split at the literal boundary head.
This both consumes primitive sources through A18.4.17 and restores the
nonprimitive provenance needed by the mixed-degree coupled geometry. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.minimalReduction
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadMinimalOutcome
      RR source target := by
  by_cases hprimitive :
      HasPrimitiveZeroSmithSource (zeroJetNormalizedFamily source.family)
  · rcases trace.exists_head_boundary with ⟨B₀, htail⟩
    cases source.primitiveCanonicalClassifier hprimitive with
    | blocker P B hEq =>
        exact .primitiveBlocker B₀ htail P B hEq
    | surviving P W hEq =>
        exact .primitiveSurviving B₀ htail P W hEq
  · cases trace.geometricReduction with
    | strictMacro D =>
        exact .strictMacro D
    | primitive B₀ htail hprimitive' =>
        exact False.elim (hprimitive hprimitive')
    | coupled B₀ htail hcoupled =>
        let P := source.coupledMinimalPresentation B₀ hprimitive hcoupled
        exact .coupledMinimal B₀ htail P rfl

end

end HC4.Valuation
