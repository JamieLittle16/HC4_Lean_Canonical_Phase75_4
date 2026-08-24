import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMixedDegreeBoundaryReduction
import HC4.Valuation.AdaptiveAlignedSmithStateBridge
import Mathlib.Tactic

/-!
# A18.4.17: primitive aligned-boundary scale-one canonical entry

A18.4.16 removes every separated aligned section wall by a genuine strict
same-scale defect drop.  The only aligned-boundary heads left are primitive
zero-Smith sources and genuinely coupled coefficient/section walls.

The primitive case must not be sent through the old fixed `20`-fold aligned
clock: no aligned transformation is needed there.  A primitive zero-grade
source coefficient already witnesses symmetric Smith minimality on the
zero-jet-normalized source itself.

This file records the correct scale-one provenance.  From a primitive source
we build a zero-jet canonical minimal endpoint with exactly the incoming raw
defect, package its family at the unchanged absolute scale, and certify that
passage as a pure ramification-one internal presentation.  The existing
canonical wall classifier can then be applied directly.  Its output is only

* a canonical blocker, or
* a canonical surviving wall.

In particular the primitive branch can no longer return to the aligned
section-boundary loop.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Scale-one primitive minimal endpoint -/

/-- Source-honest canonical minimal data attached to a primitive zero-Smith
source.  The endpoint is the zero-jet-normalized incoming family itself: no
parameter ramification and no Smith conformal move has occurred. -/
structure AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  endpoint :
    AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap
  defect_eq : endpoint.endpoint.defect = s.rawDefect
  family_eq :
    endpoint.endpoint.family = zeroJetNormalizedFamily s.family
  movingSection_eq : endpoint.endpoint.movingSection = s.movingSection

/-- A primitive zero-Smith source is already a canonical minimal endpoint at
its literal incoming determinant clock. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.primitiveMinimalPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hprimitive :
      HasPrimitiveZeroSmithSource (zeroJetNormalizedFamily s.family)) :
    AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s := by
  let E : AdaptiveAlignedSmithMinimalEndpoint (K := K) s.degreeCap :=
    { defect := s.rawDefect
      family := zeroJetNormalizedFamily s.family
      movingSection := s.movingSection
      hessianDefect := s.normalized_hessianDefect
      nonlinearDegreeBound := s.normalized_nonlinearDegreeBound
      exactCollision := s.normalized_exactCollision
      sectionSpecial := s.sectionSpecial
      symmetricMinimal :=
        primitiveZeroSmithSource_specialFiber_symmetricMinimal
          (zeroJetNormalizedFamily s.family) hprimitive }
  exact
    { endpoint :=
        { endpoint := E
          zeroSourceJet := zeroJetNormalizedFamily_hasZeroSourceJet s.family }
      defect_eq := rfl
      family_eq := rfl
      movingSection_eq := rfl }

/-- The actual scale-aware state represented by a primitive minimal endpoint.
It is recorded at the unchanged absolute scale. -/
noncomputable def AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.toScaleOneState
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect := P.endpoint.endpoint.defect
  scale := s.scale
  scale_pos := s.scale_pos
  degreeCap := s.degreeCap
  sourceComplexity := s.sourceComplexity
  repair := s.repair
  family := P.endpoint.endpoint.family
  movingSection := P.endpoint.endpoint.movingSection
  hessianDefect := P.endpoint.endpoint.hessianDefect
  nonlinearDegreeBound := P.endpoint.endpoint.nonlinearDegreeBound
  exactCollision := by
    simpa [zeroPolynomialSection] using P.endpoint.endpoint.exactCollision
  sectionSpecial := P.endpoint.endpoint.sectionSpecial

@[simp]
theorem AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.toScaleOneState_rawDefect
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s) :
    P.toScaleOneState.rawDefect = P.endpoint.endpoint.defect := rfl

@[simp]
theorem AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.toScaleOneState_scale
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s) :
    P.toScaleOneState.scale = s.scale := rfl

@[simp]
theorem AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.toScaleOneState_repair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s) :
    P.toScaleOneState.repair = s.repair := rfl

/-- Primitive canonical entry is a genuine zero-cost presentation with
ramification factor one.  This is the scale correction missing from the old
fixed-`20` aligned wrapper. -/
theorem AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.certifiedInternalMove
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s) :
    HasCertifiedRamifiedEpisodeInternalMove P.toScaleOneState s := by
  change Nonempty (CertifiedRamifiedEpisodeInternalMove P.toScaleOneState s)
  refine ⟨{
    ramification := 1
    ramification_pos := by omega
    scale_eq := by simp [AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.toScaleOneState]
    raw_eq := by
      simpa [AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation.toScaleOneState]
        using P.defect_eq
    degreeCap_eq := rfl
    sourceComplexity_eq := rfl
    repair_eq := rfl
  }⟩

/-! ## Primitive branch enters the canonical classifier directly -/

/-- Canonical classifier output from a primitive scale-one endpoint.  There is
intentionally no aligned-boundary constructor. -/
inductive AdaptiveAlignedSmithCanonicalPrimitiveClassifierOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | blocker
      (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s)
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (aligned_eq : B.aligned = P.endpoint)

  | surviving
      (P : AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation (K := K) s)
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (aligned_eq : W.original.aligned = P.endpoint)

/-- A primitive zero-Smith source bypasses the aligned boundary search and
lands immediately in the canonical blocker/surviving-wall stack. -/
theorem ScaleAwareAdaptiveGeometricRestartState.primitiveCanonicalClassifier
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hprimitive :
      HasPrimitiveZeroSmithSource (zeroJetNormalizedFamily s.family)) :
    AdaptiveAlignedSmithCanonicalPrimitiveClassifierOutcome (K := K) s := by
  let P := s.primitiveMinimalPresentation hprimitive
  rcases P.endpoint.classifyCanonicalWall with hblock | hsurvive
  · rcases hblock with ⟨B, hB⟩
    exact .blocker P B hB
  · rcases hsurvive with ⟨W, hW⟩
    let W' : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s :=
      { original := W
        wall := W.toAdaptiveWall s
        wall_eq := rfl }
    exact .surviving P W' (by simpa [W'] using hW)

/-! ## Replace the primitive boundary residue by canonical classifier data -/

/-- After A18.4.16, an aligned-boundary head has only three meaningful forms:
strict progress, a scale-one canonical blocker/surviving-wall entry, or a
truly coupled mixed-degree wall. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadCanonicalOutcome
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

  | coupled
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B))
      (hcoupled :
        HasCoupledAlignedSmithWall
          (zeroJetNormalizedFamily source.family)
          (zeroPolynomialSection (K := K))
          source.movingSection)

/-- Consume the primitive constructor of the A18.4.16 head trichotomy by
scale-one canonical classification.  Thus primitive sources are no longer
part of the boundary-presentation recursion. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.canonicalReduction
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadCanonicalOutcome
      RR source target := by
  cases trace.geometricReduction with
  | strictMacro D =>
      exact .strictMacro D
  | coupled B htail hcoupled =>
      exact .coupled B htail hcoupled
  | primitive B₀ htail hprimitive =>
      cases source.primitiveCanonicalClassifier hprimitive with
      | blocker P B hEq =>
          exact .primitiveBlocker B₀ htail P B hEq
      | surviving P W hEq =>
          exact .primitiveSurviving B₀ htail P W hEq

end

end HC4.Valuation
