import HC4.Valuation.AdaptiveAlignedSmithZeroJet
import Mathlib.Tactic

/-!
# Adaptive aligned-Smith classifier dispatcher

The one-shot aligned-Smith macro is already mixed-degree and scale-aware, but
its original minimal endpoint intentionally did not remember how that family
was produced.  For the canonical wall classifier we need one further piece of
provenance: the aligned endpoint still has zero source jet.

This file carries that invariant through the same finite aligned-Smith macro
without changing any of the already-green endpoint structures.  The resulting
minimal endpoint enters the canonical wall classifier on its *raw* special
fibre.

The final theorem is the first genuine dispatcher-facing three-way split:

* canonical Smith blocker;
* integral surviving Smith wall;
* actual aligned section boundary.

No global descent measure is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Provenance-enriched aligned endpoint -/

/-- An aligned-Smith minimal endpoint together with the zero-source-jet
provenance needed to classify its raw special fibre. -/
structure AdaptiveAlignedSmithMinimalZeroJetEndpoint
    (degreeCap : ℕ) where
  endpoint :
    AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap
  zeroSourceJet :
    HasZeroSourceJet endpoint.family

/-- The raw special fibre of a provenance-enriched minimal endpoint has the
normalized axis data required by the state-neutral canonical classifier. -/
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.rawSpecialFiber_axisData
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) degreeCap) :
    HasNormalizedSmithAxisData
      E.endpoint.rawSpecialFiber := by
  simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using
    E.zeroSourceJet.specialFiber_axisData
      E.endpoint.movingSection
      E.endpoint.exactCollision
      E.endpoint.sectionSpecial

/-! ## Explicit classifier output objects -/

/-- The blocker output of the canonical wall classifier, retaining the
aligned endpoint that produced it. -/
structure AdaptiveAlignedSmithBlockerEndpoint
    (degreeCap : ℕ) where
  aligned :
    AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) degreeCap
  exponent : SmithSupportExponent
  mem :
    exponent ∈
      smithProjectedSupport
        (1 : Fin 4) 2 3
        aligned.endpoint.rawSpecialFiber
  level :
    (fun _ => (0 : ℤ)) exponent = 0
  pattern :
    IsPureLongitudinalSmithPattern exponent ∨
    IsLowNegativeFirstSmithPattern exponent ∨
    IsLowNegativeSecondSmithPattern exponent ∨
    IsWLinearSmithPattern exponent
  outcome :
    MixedDegreeSmithExponentOutcome
      aligned.endpoint.rawSpecialFiber exponent

/-- The surviving-wall output of the canonical wall classifier, retaining the
aligned endpoint that produced it. -/
structure AdaptiveAlignedSmithSurvivingWallEndpoint
    (degreeCap : ℕ) where
  aligned :
    AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) degreeCap
  wall :
    IntegralAdaptiveSurvivingSmithWall
      aligned.endpoint.rawSpecialFiber

/-- A zero-jet aligned minimal endpoint enters the canonical integral Smith
wall classifier immediately, with no second family normalization. -/
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.classifyCanonicalWall
    [CharZero K]
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) degreeCap) :
    Nonempty
        (AdaptiveAlignedSmithBlockerEndpoint
          (K := K) degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSurvivingWallEndpoint
          (K := K) degreeCap) := by
  rcases
      classifyCanonicalIntegralWallOfSpecialFiber
        E.endpoint.rawSpecialFiber
        E.rawSpecialFiber_axisData
        E.endpoint.canonicalWallData with
    hblock | hsurvive
  · left
    rcases hblock with
      ⟨e, he, hlevel, hpattern, houtcome⟩
    exact
      ⟨{
        aligned := E
        exponent := e
        mem := he
        level := hlevel
        pattern := hpattern
        outcome := houtcome
      }⟩
  · right
    rcases hsurvive with ⟨W⟩
    exact
      ⟨{
        aligned := E
        wall := W
      }⟩

/-! ## Zero-jet-preserving aligned macro -/

/-- The mixed-degree aligned-Smith macro with zero-source-jet provenance
retained on its minimal branch.

The section-boundary branch uses the existing endpoint object unchanged,
because it exits the canonical-wall classifier rather than re-entering it. -/
theorem adaptiveAlignedSmithEndpoint_zeroLeft_withZeroSourceJet
    [CharZero K]
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hdegree :
      NonlinearDegreeBound degreeCap P)
    (hzero : HasZeroSourceJet P)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    Nonempty
        (AdaptiveAlignedSmithMinimalZeroJetEndpoint
          (K := K) degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K) degreeCap Delta P b) := by
  classical
  by_cases hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b
  · let N :=
      alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
    by_cases hB : N ∈ alignedSmithSectionWalls b
    · right
      have hcoord :=
        genuineRightSectionWall_exposes_nonzero_specialCoordinate
          P (zeroPolynomialSection (K := K)) b hwall
          (by simpa [N] using hB)
      have hboundary :
          HasAlignedSmithSectionBoundary
            P (zeroPolynomialSection (K := K)) b hwall := by
        right
        rcases hcoord with ⟨i, hi0, hne⟩
        exact
          ⟨i, hi0, by simpa [N] using hB, hne⟩
      have hwallDef :
          HasPolynomialFamilyHessianDefect
            (K := K)
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (alignedSmithRamificationIndex * Delta) :=
        alignedSmithGenuineFirstWall_preservesHessianDefect
          P (zeroPolynomialSection (K := K)) b
          hwall Delta hdef
      have hwallDegree :
          NonlinearDegreeBound degreeCap
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall) :=
        nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
          (K := K) degreeCap P
          (zeroPolynomialSection (K := K)) b hwall hdegree
      have hwallCollRaw :=
        alignedSmithGenuineFirstWall_preservesExactCollision
          P (zeroPolynomialSection (K := K)) b hwall hcoll
      have hleft :
          alignedSmithGenuineFirstWallSectionLeft
              (K := K)
              P (zeroPolynomialSection (K := K)) b hwall =
            zeroPolynomialSection (K := K) :=
        alignedSmithGenuineFirstWallSectionLeft_zero
          (K := K) P b hwall
      have hwallColl :
          HasPolynomialFamilyExactGradientCollision
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (zeroPolynomialSection (K := K))
            (alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall) := by
        simpa only [hleft] using hwallCollRaw
      exact
        ⟨{
          hwall := hwall
          boundary := hboundary
          hessianDefect := hwallDef
          nonlinearDegreeBound := hwallDegree
          exactCollision := hwallColl
        }⟩
    · left
      have hcases :=
        alignedSmithGenuineFirstWall_cases
          P (zeroPolynomialSection (K := K)) b hwall
      have hcoeff :
          N ∈ alignedSmithCoefficientWalls P := by
        rcases hcases with hcoeff | hA | hBright
        · simpa [N] using hcoeff
        · have hnotA :
              N ∉
                alignedSmithSectionWalls
                  (zeroPolynomialSection (K := K)) :=
            not_mem_alignedSmithSectionWalls_zeroPolynomialSection
              (K := K) N
          exact False.elim (hnotA (by simpa [N] using hA))
        · exact False.elim (hB (by simpa [N] using hBright))
      have hnotA :
          alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall ∉
            alignedSmithSectionWalls
              (zeroPolynomialSection (K := K)) := by
        exact
          not_mem_alignedSmithSectionWalls_zeroPolynomialSection
            (K := K)
            (alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall)
      have hnotB :
          alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall ∉
            alignedSmithSectionWalls b := by
        simpa [N] using hB
      have ha :
          polynomialSectionSpecialPoint
              (zeroPolynomialSection (K := K)) =
            (fun _ => (0 : K)) :=
        polynomialSectionSpecialPoint_zeroPolynomialSection
      have hpoints :=
        pureCoefficientWall_specialPoints_canonical
          P (zeroPolynomialSection (K := K)) b
          hwall hnotA hnotB ha hb
      have hwallDef :
          HasPolynomialFamilyHessianDefect
            (K := K)
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (alignedSmithRamificationIndex * Delta) :=
        alignedSmithGenuineFirstWall_preservesHessianDefect
          P (zeroPolynomialSection (K := K)) b
          hwall Delta hdef
      have hwallDegree :
          NonlinearDegreeBound degreeCap
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall) :=
        nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
          (K := K) degreeCap P
          (zeroPolynomialSection (K := K)) b hwall hdegree
      have hwallCollRaw :=
        alignedSmithGenuineFirstWall_preservesExactCollision
          P (zeroPolynomialSection (K := K)) b hwall hcoll
      have hleft :
          alignedSmithGenuineFirstWallSectionLeft
              (K := K)
              P (zeroPolynomialSection (K := K)) b hwall =
            zeroPolynomialSection (K := K) :=
        alignedSmithGenuineFirstWallSectionLeft_zero
          (K := K) P b hwall
      have hwallColl :
          HasPolynomialFamilyExactGradientCollision
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (zeroPolynomialSection (K := K))
            (alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall) := by
        simpa only [hleft] using hwallCollRaw
      have hminimal :
          IsSymmetricSmithPoleMinimal
            (smithProjectedSupport
              (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber
                (alignedSmithGenuineFirstWallFamily
                  P (zeroPolynomialSection (K := K)) b hwall)))
            0
            (fun _ => (0 : ℤ)) :=
        genuineCoefficientWall_specialFiber_symmetricMinimal
          P (zeroPolynomialSection (K := K)) b hwall
          (by simpa [N] using hcoeff)
      let E :
          AdaptiveAlignedSmithMinimalEndpoint
            (K := K) degreeCap :=
        {
          defect := alignedSmithRamificationIndex * Delta
          family :=
            alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall
          movingSection :=
            alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall
          hessianDefect := hwallDef
          nonlinearDegreeBound := hwallDegree
          exactCollision := hwallColl
          sectionSpecial := hpoints.2
          symmetricMinimal := hminimal
        }
      have hEzero :
          HasZeroSourceJet E.family := by
        dsimp [E]
        exact
          hzero.alignedSmithGenuineFirstWallFamily
            (zeroPolynomialSection (K := K)) b hwall
      exact
        ⟨{
          endpoint := E
          zeroSourceJet := hEzero
        }⟩
  · left
    rcases
        noWallPrimitiveSmithFamily_zeroLeft_canonicalCollision
          P b Delta hdef hwall hcoll hb with
      ⟨b', hcoll', hb'⟩
    let Q :=
      noWallPrimitiveSmithFamily
        P (zeroPolynomialSection (K := K)) b
        Delta hdef hwall
    let hne :=
      zeroSmithSourceSupport_nonempty_of_noGenuineWall
        P (zeroPolynomialSection (K := K)) b
        Delta hdef hwall
    let m := minimalZeroSmithParameterOrder P hne
    let Delta' :=
      alignedSmithRamificationIndex * Delta -
        4 * (alignedSmithRamificationIndex * m)
    have hQdef :
        HasPolynomialFamilyHessianDefect
          (K := K) Q Delta' := by
      dsimp [Q, Delta', hne, m]
      exact
        noWallPrimitiveSmithFamily_hasHessianDefect
          P (zeroPolynomialSection (K := K)) b
          Delta hdef hwall
    have hQdegree :
        NonlinearDegreeBound degreeCap Q := by
      dsimp [Q]
      exact
        nonlinearDegreeBound_noWallPrimitiveSmithFamily
          (K := K) degreeCap P
          (zeroPolynomialSection (K := K)) b
          Delta hdef hwall hdegree
    have hminimal :
        IsSymmetricSmithPoleMinimal
          (smithProjectedSupport
            (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber Q))
          0
          (fun _ => (0 : ℤ)) := by
      dsimp [Q]
      exact
        noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
          P (zeroPolynomialSection (K := K)) b
          Delta hdef hwall
    let E :
        AdaptiveAlignedSmithMinimalEndpoint
          (K := K) degreeCap :=
      {
        defect := Delta'
        family := Q
        movingSection := b'
        hessianDefect := hQdef
        nonlinearDegreeBound := hQdegree
        exactCollision := hcoll'
        sectionSpecial := hb'
        symmetricMinimal := hminimal
      }
    have hEzero :
        HasZeroSourceJet E.family := by
      dsimp [E, Q]
      exact
        hzero.noWallPrimitiveSmithFamily
          (zeroPolynomialSection (K := K)) b
          Delta hdef hwall
    exact
      ⟨{
        endpoint := E
        zeroSourceJet := hEzero
      }⟩

/-! ## Scale-aware dispatcher -/

/-- Apply the zero-jet-preserving aligned macro to the actual normalized
family of a scale-aware adaptive state. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithEndpoint_withZeroSourceJet
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Nonempty
        (AdaptiveAlignedSmithMinimalZeroJetEndpoint
          (K := K) s.degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection) := by
  exact
    adaptiveAlignedSmithEndpoint_zeroLeft_withZeroSourceJet
      (K := K)
      s.degreeCap
      (zeroJetNormalizedFamily s.family)
      s.movingSection
      s.rawDefect
      s.normalized_hessianDefect
      s.normalized_nonlinearDegreeBound
      (zeroJetNormalizedFamily_hasZeroSourceJet s.family)
      s.normalized_exactCollision
      s.sectionSpecial

/-- **First assembled adaptive Smith dispatcher.**

A scale-aware adaptive state, after one finite mixed-degree aligned-Smith
macro-step, lands in exactly the interfaces required by the already-existing
downstream machinery:

* a canonical blocker;
* an integral surviving Smith wall; or
* an actual aligned section boundary.

This theorem is exhaustive at the Smith-classification level.  It still makes
no claim that any particular scalar global measure decreases. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithClassifierDispatcher
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Nonempty
        (AdaptiveAlignedSmithBlockerEndpoint
          (K := K) s.degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSurvivingWallEndpoint
          (K := K) s.degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection) := by
  rcases s.alignedSmithEndpoint_withZeroSourceJet with
    hminimal | hboundary
  · rcases hminimal with ⟨E⟩
    rcases E.classifyCanonicalWall with hblock | hsurvive
    · exact Or.inl hblock
    · exact Or.inr (Or.inl hsurvive)
  · exact Or.inr (Or.inr hboundary)

end

end HC4.Valuation
