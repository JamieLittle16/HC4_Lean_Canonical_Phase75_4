import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleSoundKernelDispatcher
import HC4.Valuation.AdaptiveAlignedSmithBoundaryReentry
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import Mathlib.Tactic

/-!
# Exact outer-clock normal form for the canonical aligned-Smith macro

The provenance-preserving classifier gives the universal estimate

    endpoint.defect ≤ alignedSmithRamificationIndex * incoming.rawDefect.

At the absolute post-alignment scale

    alignedSmithRamificationIndex * incoming.scale,

strict inequality is already a genuine ramified defect spend from the incoming
state.  Hence every non-spending aligned endpoint necessarily has the *exact*
outer clock

    endpoint.defect = alignedSmithRamificationIndex * incoming.rawDefect.

The same observation applies to both blocker and surviving-wall endpoints.
The genuine aligned section-boundary branch has that exact clock by
construction, and after the determinant-one boundary shear is therefore a
pure cross-scale re-presentation rather than an unchecked recursive re-entry.

This file packages those facts and proves the macro composition rule needed by
the final assembly: a ramified zero-cost presentation followed by a ramified
strict spend is itself a ramified strict spend from the original state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Absolute-scale aligned endpoint presentation -/

/-- Regard an aligned minimal endpoint at the literal absolute scale produced
by the one-shot aligned-Smith ramification. -/
noncomputable def AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect := E.endpoint.defect
  scale := alignedSmithRamificationIndex * s.scale
  scale_pos := Nat.mul_pos alignedSmithRamificationIndex_pos s.scale_pos
  degreeCap := s.degreeCap
  sourceComplexity := s.sourceComplexity
  repair := s.repair
  family := E.endpoint.family
  movingSection := E.endpoint.movingSection
  hessianDefect := E.endpoint.hessianDefect
  nonlinearDegreeBound := E.endpoint.nonlinearDegreeBound
  exactCollision := by
    simpa [zeroPolynomialSection] using E.endpoint.exactCollision
  sectionSpecial := E.endpoint.sectionSpecial

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    (E.toOuterScaleAwareState s).rawDefect = E.endpoint.defect := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    (E.toOuterScaleAwareState s).scale =
      alignedSmithRamificationIndex * s.scale := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState_degreeCap
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    (E.toOuterScaleAwareState s).degreeCap = s.degreeCap := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState_sourceComplexity
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    (E.toOuterScaleAwareState s).sourceComplexity = s.sourceComplexity := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    (E.toOuterScaleAwareState s).repair = s.repair := rfl

/-! ## Ramified zero-cost macro moves -/

/-- A scale-changing presentation which is *exactly* a pure ramification at
the episode-bookkeeping level.  This is not recursive progress by itself.
The data fields are retained so that a later strict spend can be composed back
to the original state without losing the absolute scale. -/
structure CertifiedRamifiedEpisodeInternalMove
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type where
  ramification : ℕ
  ramification_pos : 0 < ramification
  scale_eq : t.scale = ramification * s.scale
  raw_eq : t.rawDefect = ramification * s.rawDefect
  degreeCap_eq : t.degreeCap = s.degreeCap
  sourceComplexity_eq : t.sourceComplexity = s.sourceComplexity
  repair_eq : t.repair = s.repair

/-- Propositional wrapper for a data-bearing ramified internal move. -/
def HasCertifiedRamifiedEpisodeInternalMove
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  Nonempty (CertifiedRamifiedEpisodeInternalMove t s)

/-- A certified ramified internal move represents exactly the same normalized
Hessian defect. -/
theorem CertifiedRamifiedEpisodeInternalMove.scaledDefect_equivalent
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : CertifiedRamifiedEpisodeInternalMove t s) :
    ScaledDefect.Equivalent t.scaledDefect s.scaledDefect := by
  unfold ScaledDefect.Equivalent
  change t.rawDefect * s.scale = s.rawDefect * t.scale
  rw [h.raw_eq, h.scale_eq]
  ac_rfl

/-- **Cross-scale zero-cost composition.**

A pure ramified re-presentation followed by an honest ramified raw-defect
spend is an honest ramified raw-defect spend from the original state. -/
def CertifiedRamifiedEpisodeInternalMove.then_spend
    {s u t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : CertifiedRamifiedEpisodeInternalMove u s)
    (hspend : CertifiedRamifiedRawDefectSpend t u) :
    CertifiedRamifiedRawDefectSpend t s where
  ramification := hspend.ramification * hmove.ramification
  ramification_pos := Nat.mul_pos hspend.ramification_pos hmove.ramification_pos
  scale_eq := by
    calc
      t.scale = hspend.ramification * u.scale := hspend.scale_eq
      _ = hspend.ramification * (hmove.ramification * s.scale) := by
        rw [hmove.scale_eq]
      _ = (hspend.ramification * hmove.ramification) * s.scale := by
        ac_rfl
  raw_lt := by
    calc
      t.rawDefect < hspend.ramification * u.rawDefect := hspend.raw_lt
      _ = hspend.ramification * (hmove.ramification * s.rawDefect) := by
        rw [hmove.raw_eq]
      _ = (hspend.ramification * hmove.ramification) * s.rawDefect := by
        ac_rfl

/-- Propositional form of `then_spend`. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.then_spend
    {s u t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : HasCertifiedRamifiedEpisodeInternalMove u s)
    (hspend :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        t u) :
    AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
      t s := by
  change Nonempty (CertifiedRamifiedEpisodeInternalMove u s) at hmove
  change Nonempty (CertifiedRamifiedRawDefectSpend t u) at hspend
  change Nonempty (CertifiedRamifiedRawDefectSpend t s)
  rcases hmove with ⟨hmove⟩
  rcases hspend with ⟨hspend⟩
  exact ⟨hmove.then_spend hspend⟩

/-- Strict loss already inside the aligned endpoint clock is an absolute-scale
spend, before any later Schur or packet geometry is inspected. -/
def AdaptiveAlignedSmithMinimalZeroJetEndpoint.certifiedOuterSpend_of_defect_lt
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
    (hlt : E.endpoint.defect < alignedSmithRamificationIndex * s.rawDefect) :
    CertifiedRamifiedRawDefectSpend (E.toOuterScaleAwareState s) s where
  ramification := alignedSmithRamificationIndex
  ramification_pos := alignedSmithRamificationIndex_pos
  scale_eq := rfl
  raw_lt := hlt

/-- Equality in the aligned outer-clock bound is a certified ramified
zero-cost presentation. -/
def AdaptiveAlignedSmithMinimalZeroJetEndpoint.certifiedOuterInternal_of_defect_eq
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
    (heq : E.endpoint.defect = alignedSmithRamificationIndex * s.rawDefect) :
    CertifiedRamifiedEpisodeInternalMove (E.toOuterScaleAwareState s) s where
  ramification := alignedSmithRamificationIndex
  ramification_pos := alignedSmithRamificationIndex_pos
  scale_eq := rfl
  raw_eq := heq
  degreeCap_eq := rfl
  sourceComplexity_eq := rfl
  repair_eq := rfl

/-! ## Genuine aligned section-boundary as a ramified internal move -/

/-- The determinant-one normalization of a genuine aligned section boundary,
recorded at its true absolute post-alignment scale. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryScaleAwareReentry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let a := s.alignedBoundaryReentry B
  exact
    { rawDefect := alignedSmithRamificationIndex * s.rawDefect
      scale := alignedSmithRamificationIndex * s.scale
      scale_pos := Nat.mul_pos alignedSmithRamificationIndex_pos s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := a.family
      movingSection := a.movingSection
      hessianDefect := by
        simpa [a] using a.hessianDefect
      nonlinearDegreeBound := by
        simpa [a] using a.nonlinearDegreeBound
      exactCollision := by
        simpa [a] using a.exactCollision
      sectionSpecial := by
        simpa [a] using a.sectionSpecial }

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryScaleAwareReentry_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection) :
    (s.alignedBoundaryScaleAwareReentry B).rawDefect =
      alignedSmithRamificationIndex * s.rawDefect := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryScaleAwareReentry_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection) :
    (s.alignedBoundaryScaleAwareReentry B).scale =
      alignedSmithRamificationIndex * s.scale := rfl

/-- A genuine aligned section boundary is therefore a certified cross-scale
zero-cost macro move, not an arbitrary recursive re-entry. -/
def ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryCertifiedInternalMove
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection) :
    CertifiedRamifiedEpisodeInternalMove
      (s.alignedBoundaryScaleAwareReentry B) s where
  ramification := alignedSmithRamificationIndex
  ramification_pos := alignedSmithRamificationIndex_pos
  scale_eq := rfl
  raw_eq := rfl
  degreeCap_eq := rfl
  sourceComplexity_eq := rfl
  repair_eq := rfl

/-! ## Exact-clock stationary frontier -/

namespace AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-- The scale-sound stationary blocker still retains the canonical least
positive longitudinal departure over its unchanged Smith exponent. -/
theorem firstLongitudinalDeparture
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily)
      S.blocker.exponent := by
  rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
  exact S.blocker.firstLongitudinalDeparture

end AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-- Canonical first-macro outcome after consuming every strict loss already
visible in the aligned endpoint clock itself.

Every unresolved endpoint now lies on the exact outer clock.  A section
boundary is retained only as a certified nonrecursive internal presentation. -/
inductive AdaptiveAlignedSmithCanonicalExactClockOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | stationaryExactClock
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- **Exact-clock scale-sound canonical dispatcher.**

Any strict loss in the initial aligned clock is immediately returned as an
absolute-scale ramified spend.  Consequently every surviving blocker or wall
has exact clock `20 * s.rawDefect`, while a genuine section boundary is an
explicit ramified zero-cost internal move. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockDispatcher
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    AdaptiveAlignedSmithCanonicalExactClockOutcome s := by
  by_cases hz : s.rawDefect = 0
  · exact .zeroDefect hz
  have hspos : 0 < s.rawDefect := Nat.pos_of_ne_zero hz
  rcases s.alignedSmithCanonicalScaleSoundKernelDispatcher with
    ⟨target, hspend⟩ | ⟨S⟩ | ⟨W, hclock⟩ | ⟨B⟩

  · exact .ramifiedSpend target hspend

  · have hle := S.defect_le_alignedClock
    by_cases hlt :
        S.blocker.aligned.endpoint.defect <
          alignedSmithRamificationIndex * s.rawDefect
    · let target := S.blocker.aligned.toOuterScaleAwareState s
      exact .ramifiedSpend target
        ⟨S.blocker.aligned.certifiedOuterSpend_of_defect_lt s hlt⟩
    · have heq :
          S.blocker.aligned.endpoint.defect =
            alignedSmithRamificationIndex * s.rawDefect := by
        exact Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
      have hpos : 0 < S.blocker.aligned.endpoint.defect := by
        rw [heq]
        exact Nat.mul_pos alignedSmithRamificationIndex_pos hspos
      exact .stationaryExactClock S heq hpos

  · have hle := hclock
    by_cases hlt :
        W.original.aligned.endpoint.defect <
          alignedSmithRamificationIndex * s.rawDefect
    · let target := W.original.aligned.toOuterScaleAwareState s
      exact .ramifiedSpend target
        ⟨W.original.aligned.certifiedOuterSpend_of_defect_lt s hlt⟩
    · have heq :
          W.original.aligned.endpoint.defect =
            alignedSmithRamificationIndex * s.rawDefect := by
        exact Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
      exact .survivingExactClock W heq

  · exact .sectionBoundaryInternal B

end

end HC4.Valuation
