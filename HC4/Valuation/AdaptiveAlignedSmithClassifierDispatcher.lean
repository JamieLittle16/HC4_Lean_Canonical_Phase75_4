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
  /-- The surviving wall comes from the canonical zero Smith base. -/
  wall_level_eq_zero : wall.level = 0
  /-- Its underlying transverse realisation is the zero weight. -/
  wall_transverseWeight_eq_zero :
    wall.realization.transverseWeight = fun _ => 0
  /-- The affine realisation has zero offset. -/
  wall_offset_eq_zero : wall.realization.offset = 0

/-- The canonical surviving wall therefore has the fixed combined source
weight sum `0 + 2 + 2 + 4 = 8`. -/
@[simp]
theorem AdaptiveAlignedSmithSurvivingWallEndpoint.combinedSourceWeight_sum
    {degreeCap : ℕ}
    (W : AdaptiveAlignedSmithSurvivingWallEndpoint
      (K := K) degreeCap) :
    (∑ i : Fin 4, W.wall.realization.combinedSourceWeight i) = 8 := by
  rw [Fin.sum_univ_four]
  simp [HasIntegralAdaptiveSmithWallWeight.combinedSourceWeight,
    W.wall_transverseWeight_eq_zero]

/-- Its affine combined source level is the fixed integer `4`. -/
@[simp]
theorem AdaptiveAlignedSmithSurvivingWallEndpoint.combinedSourceLevel_eq_four
    {degreeCap : ℕ}
    (W : AdaptiveAlignedSmithSurvivingWallEndpoint
      (K := K) degreeCap) :
    W.wall.realization.combinedSourceLevel W.wall.level = 4 := by
  simp [HasIntegralAdaptiveSmithWallWeight.combinedSourceLevel,
    W.wall_level_eq_zero, W.wall_offset_eq_zero]

/-- A zero-jet aligned minimal endpoint enters the canonical integral Smith
wall classifier immediately, with no second family normalization. -/
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.classifyCanonicalWall
    [CharZero K]
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) degreeCap) :
    (∃ B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap,
        B.aligned = E) ∨
      (∃ W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) degreeCap,
        W.aligned = E) := by
  rcases
      classifyCanonicalIntegralWallOfSpecialFiber_withProvenance
        E.endpoint.rawSpecialFiber
        E.rawSpecialFiber_axisData
        E.endpoint.canonicalWallData with
    hblock | hsurvive
  · left
    rcases hblock with
      ⟨e, he, hlevel, hpattern, houtcome⟩
    refine ⟨{
      aligned := E
      exponent := e
      mem := he
      level := hlevel
      pattern := hpattern
      outcome := houtcome
    }, ?_⟩
    rfl
  · right
    rcases hsurvive with ⟨W⟩
    refine ⟨{
      aligned := E
      wall := W.wall
      wall_level_eq_zero := W.level_eq_zero
      wall_transverseWeight_eq_zero := W.transverseWeight_eq_zero
      wall_offset_eq_zero := W.offset_eq_zero
    }, ?_⟩
    rfl

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
    (∃ E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) degreeCap,
        E.endpoint.defect ≤ alignedSmithRamificationIndex * Delta) ∨
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
      refine ⟨{
        endpoint := E
        zeroSourceJet := hEzero
      }, ?_⟩
      change
        alignedSmithRamificationIndex * Delta ≤
          alignedSmithRamificationIndex * Delta
      exact le_rfl
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
    refine ⟨{
      endpoint := E
      zeroSourceJet := hEzero
    }, ?_⟩
    change Delta' ≤ alignedSmithRamificationIndex * Delta
    dsimp [Delta']
    exact Nat.sub_le _ _

/-! ## Scale-aware dispatcher -/

/-- Apply the zero-jet-preserving aligned macro to the actual normalized
family of a scale-aware adaptive state, retaining the absolute aligned-clock
bound needed by scale-sound outer progress. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithEndpoint_withZeroSourceJet_withClockBound
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (∃ E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap,
        E.endpoint.defect ≤ alignedSmithRamificationIndex * s.rawDefect) ∨
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

/-- Compatibility projection: forget the aligned-clock bound and recover the
original endpoint API used by the already-green downstream stack. -/
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
  rcases s.alignedSmithEndpoint_withZeroSourceJet_withClockBound with
    ⟨E, _hclock⟩ | hboundary
  · exact Or.inl ⟨E⟩
  · exact Or.inr hboundary

/-- Provenance-preserving first Smith classifier.  On either non-boundary
branch the exact aligned endpoint still carries the universal outer-clock
bound `endpoint.defect ≤ 20 * s.rawDefect`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithClassifierDispatcher_withClockBound
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (∃ B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap,
        B.aligned.endpoint.defect ≤
          alignedSmithRamificationIndex * s.rawDefect) ∨
      (∃ W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) s.degreeCap,
        W.aligned.endpoint.defect ≤
          alignedSmithRamificationIndex * s.rawDefect) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection) := by
  rcases s.alignedSmithEndpoint_withZeroSourceJet_withClockBound with
    ⟨E, hclock⟩ | hboundary
  · rcases E.classifyCanonicalWall with ⟨B, hB⟩ | ⟨W, hW⟩
    · left
      refine ⟨B, ?_⟩
      rw [hB]
      exact hclock
    · right
      left
      refine ⟨W, ?_⟩
      rw [hW]
      exact hclock
  · exact Or.inr (Or.inr hboundary)

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
  rcases s.alignedSmithClassifierDispatcher_withClockBound with
    ⟨B, _hclock⟩ | ⟨W, _hclock⟩ | hboundary
  · exact Or.inl ⟨B⟩
  · exact Or.inr (Or.inl ⟨W⟩)
  · exact Or.inr (Or.inr hboundary)

end

end HC4.Valuation
