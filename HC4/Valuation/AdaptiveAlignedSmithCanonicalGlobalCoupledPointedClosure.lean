import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCoupledPointedZeroJet
import HC4.Valuation.BinarySmithOrderExtraction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSoundAssemblyFrontier
import Mathlib.Tactic

/-!
# A18.4.20: close the mixed-degree coupled wall after pointing

A18.4.18 showed that a residual coupled aligned wall is already a genuine
coefficient first wall, is nonprimitive, and has an all-negative actual
special fibre.  A18.4.19 then applied the existing determinant-one three-shear
normalisation and proved that the resulting pointed family retains

* the exact Hessian clock `20 * Delta`;
* the adaptive nonlinear degree bound;
* the exact zero-left collision;
* the canonical right special point `e0`; and
* the zero source jet.

It is unnecessary to prove that symmetric minimality itself is invariant
under this triangular shear.  The binary Smith-order machinery gives a
stronger source-honest dichotomy for *every* pointed mixed-degree family:

* if the pointed special fibre is symmetric-minimal, classify it immediately
  by the raw canonical wall classifier;
* otherwise the complementary Smith separator extends from the actual
  special fibre to the whole Rees family.  Ramification by ten, the integral
  `(2,2)` Smith transform and one genuine common parameter factor then give
  the actual geometric clock drop

      10 * (20 * Delta)  ->  10 * (20 * Delta) - 4.

This file packages the latter as a real scale-aware family at absolute scale
`(10 * 20) * source.scale`, followed by determinant-one point normalisation.
Thus it is a certified ramified raw-defect spend, not a numerical
`GlobalRestartState` or repair-only relabel.

Consequently the mixed-degree coupled-wall residue disappears completely:
it is either a canonical blocker, a canonical surviving wall, or genuine
strict global progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## The nonminimal pointed branch is genuine ramified progress -/

/-- If the pointed coupled special fibre is not symmetric-minimal, the
binary Smith separator constructs an actual new adaptive family at absolute
ramification factor `10 * 20`, with raw clock smaller by four than the fully
ramified source clock. -/
theorem AdaptiveAlignedSmithCanonicalCoupledPointedPresentation.globalRamifiedStrictMacro_of_notMinimal
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s)
    (hnotMinimal :
      ¬ IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P.source.pointedFamily))
        0
        (fun _ => (0 : ℤ))) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s := by
  let F := P.source.pointedFamily
  let b := P.source.pointedSection
  let base := smithBinaryBase F

  have hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) F)
        0
        (fun e => (base e : ℤ)) := by
    exact Or.resolve_left
      (specialFiber_symmetricMinimal_or_familyStrictImprovement F)
      (by simpa [F] using hnotMinimal)

  let hbase : HasSmithCoefficientOrderLowerBound base F :=
    smithBinaryBase_coefficientOrderLowerBound F
  let Pram := parameterRamificationFamily (K := K) 10 F
  let hsmith :=
    strictSymmetricImprovement_integralSmithDivisibility
      (K := K) base F hbase hstrict
  let S := integralSmithConformalFamily 2 2 Pram hsmith
  let hcommon :=
    strictSymmetricImprovement_commonParameterFactor
      (K := K) base F hbase hstrict hsmith
  let Q := commonParameterFactorFamily 1 S hcommon

  have hPramDef :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram
        (10 * (alignedSmithRamificationIndex * s.rawDefect)) := by
    dsimp [Pram, F]
    exact parameterRamificationFamily_hasHessianDefect
      10 (alignedSmithRamificationIndex * s.rawDefect)
      P.source.pointedFamily P.hessianDefect
  have hSDef :
      HasPolynomialFamilyHessianDefect
        (K := K) S
        (10 * (alignedSmithRamificationIndex * s.rawDefect)) := by
    dsimp [S]
    exact integralSmithConformalFamily_preservesHessianDefect
      2 2 (10 * (alignedSmithRamificationIndex * s.rawDefect))
      Pram hsmith hPramDef
  have hQDef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (10 * (alignedSmithRamificationIndex * s.rawDefect) - 4) := by
    dsimp [Q]
    exact commonParameterFactor_one_hasHessianDefect_sub_four
      S hcommon
      (10 * (alignedSmithRamificationIndex * s.rawDefect)) hSDef

  have hPramDegree : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram, F]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap 10 P.source.pointedFamily P.nonlinearDegreeBound
  have hSDegree : NonlinearDegreeBound s.degreeCap S := by
    dsimp [S]
    exact nonlinearDegreeBound_integralSmithConformal
      s.degreeCap 2 2 Pram hPramDegree hsmith
  have hQDegree : NonlinearDegreeBound s.degreeCap Q := by
    dsimp [Q]
    exact nonlinearDegreeBound_commonParameterFactor
      s.degreeCap 1 S hSDegree hcommon

  have haSpecial :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ : Fin 4 => (0 : K)) := by
    exact polynomialSectionSpecialPoint_zeroPolynomialSection
  have haaxis :
      HasSmithTransverseParameterFactor
        (zeroPolynomialSection (K := K)) :=
    smithTransverseParameterFactor_of_specialPoint_zero
      (zeroPolynomialSection (K := K)) haSpecial
  have hbaxis : HasSmithTransverseParameterFactor b := by
    exact smithTransverseParameterFactor_of_specialPoint_axisZero
      b (by simpa [b] using P.sectionSpecial)

  let aram :=
    parameterRamificationSection
      (K := K) 10 (zeroPolynomialSection (K := K))
  let bram := parameterRamificationSection (K := K) 10 b
  let hadiv :=
    smithTransverseParameterFactor_ramified_integralSection
      (K := K) (zeroPolynomialSection (K := K)) haaxis
  let hbdiv :=
    smithTransverseParameterFactor_ramified_integralSection
      (K := K) b hbaxis
  let asmith := integralSmithConformalSection 2 2 aram hadiv
  let bsmith := integralSmithConformalSection 2 2 bram hbdiv

  have hramColl :
      HasPolynomialFamilyExactGradientCollision Pram aram bram := by
    dsimp [Pram, aram, bram, F, b]
    exact polynomialFamilyExactGradientCollision_parameterRamification
      10 P.source.pointedFamily
      (zeroPolynomialSection (K := K)) P.source.pointedSection
      P.exactCollision
  have hsmithColl :
      HasPolynomialFamilyExactGradientCollision S asmith bsmith := by
    dsimp [S, asmith, bsmith]
    exact polynomialFamilyExactGradientCollision_integralSmithConformal
      2 2 Pram hsmith aram bram hadiv hbdiv hramColl
  have hQCollRaw :
      HasPolynomialFamilyExactGradientCollision Q asmith bsmith := by
    dsimp [Q]
    exact polynomialFamilyExactGradientCollision_commonParameterFactor
      1 S hcommon asmith bsmith hsmithColl

  have haramZero : aram = zeroPolynomialSection (K := K) := by
    funext i
    simp [aram, parameterRamificationSection, zeroPolynomialSection]
  have hasmithZero : asmith = zeroPolynomialSection (K := K) := by
    dsimp [asmith]
    rw [haramZero]
    exact integralSmithConformalSection_zeroPolynomialSection 2 hadiv
  have hQColl :
      HasPolynomialFamilyExactGradientCollision
        Q (zeroPolynomialSection (K := K)) bsmith := by
    rw [← hasmithZero]
    exact hQCollRaw

  have hbramSpecial :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bram, b]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      10 (by omega : 0 < (10 : ℕ)) P.source.pointedSection]
    exact P.sectionSpecial
  have hbsmith0 :
      polynomialSectionSpecialPoint bsmith (0 : Fin 4) = 1 := by
    have hzero :=
      integralSmithConformalSection_zeroCoordinate
        (K := K) 2 bram hbdiv
    have hbram0 := congrFun hbramSpecial (0 : Fin 4)
    change Polynomial.constantCoeff (bsmith 0) = 1
    rw [hzero]
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hbram0

  let Q' := pointedShearNormalisedFamily Q bsmith
  let b' := pointedShearNormalisedSection bsmith

  have hQ'Def :
      HasPolynomialFamilyHessianDefect
        (K := K) Q'
        (10 * (alignedSmithRamificationIndex * s.rawDefect) - 4) := by
    dsimp [Q']
    exact pointedShearNormalisedFamily_preservesHessianDefect Q bsmith hQDef
  have hQ'Degree : NonlinearDegreeBound s.degreeCap Q' := by
    dsimp [Q']
    exact nonlinearDegreeBound_pointedShearNormalisedFamily
      s.degreeCap Q bsmith hQDegree
  have hQ'Coll :
      HasPolynomialFamilyExactGradientCollision
        Q' (zeroPolynomialSection (K := K)) b' := by
    dsimp [Q', b']
    exact pointedShearNormalisedFamily_preservesExactCollision Q bsmith hQColl
  have hb'Special :
      polynomialSectionSpecialPoint b' =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [b']
    exact pointedShearNormalisedSection_specialPoint bsmith hbsmith0

  have hbudget :
      4 ≤ 10 * (alignedSmithRamificationIndex * s.rawDefect) :=
    four_le_defect_of_commonParameterFactor_one
      S hcommon
      (10 * (alignedSmithRamificationIndex * s.rawDefect)) hSDef
  have hraw :
      10 * (alignedSmithRamificationIndex * s.rawDefect) - 4 <
        (10 * alignedSmithRamificationIndex) * s.rawDefect := by
    rw [Nat.mul_assoc]
    omega

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect :=
        10 * (alignedSmithRamificationIndex * s.rawDefect) - 4
      scale := (10 * alignedSmithRamificationIndex) * s.scale
      scale_pos := Nat.mul_pos
        (Nat.mul_pos (by omega : 0 < (10 : ℕ)) alignedSmithRamificationIndex_pos)
        s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Q'
      movingSection := b'
      hessianDefect := hQ'Def
      nonlinearDegreeBound := hQ'Degree
      exactCollision := by simpa [zeroPolynomialSection] using hQ'Coll
      sectionSpecial := hb'Special }

  have hspend :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
    change Nonempty (CertifiedRamifiedRawDefectSpend target s)
    exact ⟨{
      ramification := 10 * alignedSmithRamificationIndex
      ramification_pos := Nat.mul_pos
        (by omega : 0 < (10 : ℕ)) alignedSmithRamificationIndex_pos
      scale_eq := by rfl
      raw_lt := by simpa [target] using hraw
    }⟩
  exact hspend.toGlobalStrictMacro RR

/-! ## Complete local closure of a pointed coupled wall -/

/-- Once pointed, a coupled wall is no longer a residual boundary case.
It either produces genuine ramified strict progress or enters the existing
raw canonical classifier as a blocker/surviving endpoint. -/
inductive AdaptiveAlignedSmithCanonicalCoupledPointedClosureOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | strictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | blocker
      (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (aligned_eq : B.aligned = E)

  | surviving
      (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
      (W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) s.degreeCap)
      (aligned_eq : W.aligned = E)

/-- The binary Smith dichotomy closes the pointed coupled branch completely. -/
theorem AdaptiveAlignedSmithCanonicalCoupledPointedPresentation.canonicalClosure
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s) :
    AdaptiveAlignedSmithCanonicalCoupledPointedClosureOutcome RR s := by
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
        exact .blocker E B hEq
    | inr hW =>
        rcases hW with ⟨W, hEq⟩
        exact .surviving E W hEq
  · exact .strictMacro
      (P.globalRamifiedStrictMacro_of_notMinimal RR hminimal)

/-! ## Remove the coupled constructor from the aligned-boundary head -/

/-- Final head-level outcome after A18.4.20.  There is no bare coupled-wall
constructor.  Every boundary head has become strict recursive progress or an
actual canonical blocker/surviving endpoint. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadClosedOutcome
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
      (W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) source.degreeCap)
      (aligned_eq : W.aligned = E)

/-- A traced aligned-boundary head has no residual coupled constructor after
pointing and the binary Smith dichotomy. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.closedReduction
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadClosedOutcome
      RR source target := by
  cases trace.minimalReduction with
  | strictMacro D =>
      exact .strictMacro D
  | primitiveBlocker B₀ htail P B hEq =>
      exact .primitiveBlocker B₀ htail P B hEq
  | primitiveSurviving B₀ htail P W hEq =>
      exact .primitiveSurviving B₀ htail P W hEq
  | coupledMinimal B₀ htail P hEq =>
      let PP := P.toPointedPresentation
      cases PP.canonicalClosure RR with
      | strictMacro D =>
          exact .strictMacro D
      | blocker E B hBEq =>
          exact .coupledBlocker B₀ htail P E B hBEq
      | surviving E W hWEq =>
          exact .coupledSurviving B₀ htail P E W hWEq

end

end HC4.Valuation
