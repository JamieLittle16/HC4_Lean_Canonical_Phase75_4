import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingWallClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCoupledPointedClosure
import Mathlib.Tactic

/-!
# A18.4.28: exact provenance for canonical endpoints produced by a boundary

A18.4.20 closes the genuinely coupled mixed-degree wall geometrically, but its
public `blocker` / `surviving` constructors remember only the classified
endpoint.  The proof which constructed that endpoint knew three additional
facts which are essential for the final presentation absorber:

* its determinant clock is exactly `20 * source.rawDefect`;
* its family is the literal pointed coupled first-wall family; and
* its moving section is the literal pointed coupled section.

Those facts must not be reconstructed from an existential endpoint after the
fact.  This file exports a lossless version of the same binary-Smith closure
and threads it through the A18.4.20 aligned-boundary head reduction.

The primitive branch already has the corresponding exact scale-one data in
`AdaptiveAlignedSmithCanonicalPrimitiveMinimalPresentation`, so it is retained
unchanged.  Consequently every non-strict aligned-boundary output is now a
canonical blocker or surviving endpoint together with enough information to
construct its honest presented state at the correct absolute scale.

No presentation is declared progress in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Lossless coupled-pointed closure.  Relative to A18.4.20 the endpoint clock,
family, and section equations are retained explicitly. -/
inductive AdaptiveAlignedSmithCanonicalCoupledPointedExactClosureOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (P : AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s) : Prop

  | strictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | blocker
      (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
      (defect_eq :
        E.endpoint.defect = alignedSmithRamificationIndex * s.rawDefect)
      (family_eq : E.endpoint.family = P.source.pointedFamily)
      (movingSection_eq : E.endpoint.movingSection = P.source.pointedSection)
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (aligned_eq : B.aligned = E)

  | surviving
      (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
      (defect_eq :
        E.endpoint.defect = alignedSmithRamificationIndex * s.rawDefect)
      (family_eq : E.endpoint.family = P.source.pointedFamily)
      (movingSection_eq : E.endpoint.movingSection = P.source.pointedSection)
      (W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) s.degreeCap)
      (aligned_eq : W.aligned = E)

/-- The same binary Smith dichotomy used in A18.4.20, now without throwing away
endpoint provenance in the minimal branch. -/
theorem AdaptiveAlignedSmithCanonicalCoupledPointedPresentation.canonicalExactClosure
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s) :
    AdaptiveAlignedSmithCanonicalCoupledPointedExactClosureOutcome RR s P := by
  by_cases hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P.source.pointedFamily))
        0
        (fun _ => (0 : ℤ))
  · let E₀ : AdaptiveAlignedSmithMinimalEndpoint (K := K) s.degreeCap :=
      { defect := alignedSmithRamificationIndex * s.rawDefect
        family := P.source.pointedFamily
        movingSection := P.source.pointedSection
        hessianDefect := P.hessianDefect
        nonlinearDegreeBound := P.nonlinearDegreeBound
        exactCollision := P.exactCollision
        sectionSpecial := P.sectionSpecial
        symmetricMinimal := hminimal }
    let E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap :=
      { endpoint := E₀
        zeroSourceJet := P.zeroSourceJet }
    cases E.classifyCanonicalWall with
    | inl hB =>
        rcases hB with ⟨B, hEq⟩
        exact .blocker E rfl rfl rfl B hEq
    | inr hW =>
        rcases hW with ⟨W, hEq⟩
        exact .surviving E rfl rfl rfl W hEq
  · exact .strictMacro
      (P.globalRamifiedStrictMacro_of_notMinimal RR hminimal)

/-! ## Honest presented states represented by exact endpoint data -/

/-- A coupled exact endpoint is an honest 20-fold internal presentation of the
incoming source at the bookkeeping level, while the family equalities above
retain the geometric identity of what was presented. -/
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.hasCertifiedOuterInternal_of_exactClock
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
    (hclock : E.endpoint.defect = alignedSmithRamificationIndex * s.rawDefect) :
    HasCertifiedRamifiedEpisodeInternalMove (E.toOuterScaleAwareState s) s :=
  ⟨E.certifiedOuterInternal_of_defect_eq s hclock⟩

/-! ## Lossless aligned-boundary head closure -/

/-- A18.4.20 head closure with the coupled endpoint provenance restored.
Primitive endpoints already carry exact scale-one provenance through `P`. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadExactOutcome
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

  | coupledBlocker
      (B₀ : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B₀))
      (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) source)
      (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) source.degreeCap)
      (defect_eq :
        E.endpoint.defect = alignedSmithRamificationIndex * source.rawDefect)
      (family_eq : E.endpoint.family = P.pointedFamily)
      (movingSection_eq : E.endpoint.movingSection = P.pointedSection)
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) source.degreeCap)
      (aligned_eq : B.aligned = E)

  | coupledSurviving
      (B₀ : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B₀))
      (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) source)
      (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) source.degreeCap)
      (defect_eq :
        E.endpoint.defect = alignedSmithRamificationIndex * source.rawDefect)
      (family_eq : E.endpoint.family = P.pointedFamily)
      (movingSection_eq : E.endpoint.movingSection = P.pointedSection)
      (W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) source.degreeCap)
      (aligned_eq : W.aligned = E)

/-- **A18.4.28 exact boundary-head reduction.**

For a coupled A18.4.20 leaf we deliberately rerun the deterministic pointed
binary-Smith closure from the retained coupled presentation.  This is a local
classification, not recursion, and restores the exact endpoint equations that
the older public outcome erased. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.exactClosedReduction
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadExactOutcome
      RR source target := by
  cases trace.closedReduction with
  | strictMacro D =>
      exact .strictMacro D

  | primitiveBlocker B₀ htail P B hEq =>
      exact .primitiveBlocker B₀ htail P B hEq

  | primitiveSurviving B₀ htail P W hEq =>
      exact .primitiveSurviving B₀ htail P W hEq

  | coupledBlocker B₀ htail P Eold Bold hEqOld =>
      let PP := P.toPointedPresentation
      cases PP.canonicalExactClosure RR with
      | strictMacro D =>
          exact .strictMacro D
      | blocker E hdef hfam hsec B hEq =>
          exact .coupledBlocker B₀ htail P E hdef
            (by simpa [PP] using hfam)
            (by simpa [PP] using hsec) B hEq
      | surviving E hdef hfam hsec W hEq =>
          exact .coupledSurviving B₀ htail P E hdef
            (by simpa [PP] using hfam)
            (by simpa [PP] using hsec) W hEq

  | coupledSurviving B₀ htail P Eold Wold hEqOld =>
      let PP := P.toPointedPresentation
      cases PP.canonicalExactClosure RR with
      | strictMacro D =>
          exact .strictMacro D
      | blocker E hdef hfam hsec B hEq =>
          exact .coupledBlocker B₀ htail P E hdef
            (by simpa [PP] using hfam)
            (by simpa [PP] using hsec) B hEq
      | surviving E hdef hfam hsec W hEq =>
          exact .coupledSurviving B₀ htail P E hdef
            (by simpa [PP] using hfam)
            (by simpa [PP] using hsec) W hEq

end

end HC4.Valuation
