import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalGeometryCarryingRankTwoFrontier
import HC4.Valuation.AdaptiveAlignedSmithStationaryPointedFamilyReflection
import Mathlib.Tactic

/-!
# A18.3: actual pointed-family presentation of the zero-Schur rank-two geometry

A18.2 retains the complete source-honest zero-Schur geometry, but its finite
Hessian chart is naturally written on the right-recentered family

    P(b(τ) + X).

That family has the right endpoint at the negative coordinate axis, so it is
not itself an `ScaleAwareAdaptiveGeometricRestartState`, whose marked section
is required to specialize to `e₀`.

The stationary pointed-reflection machinery already supplies the exact
family-level normalization needed here:

    P♯(X) = P(b(τ) - X).

It preserves the Hessian clock, nonlinear degree bound and ordered exact
collision `0 ~ b(τ)`, and its marked section is again based at `e₀`.

This file turns every A18.2 zero-Schur rank-two geometry into an *actual*
scale-aware HC4 presentation state at the aligned absolute scale.  Moreover,
the special fibre of that state is exactly simultaneous source negation of
the right-recentered special fibre on which the A17 chart was computed.

Thus the rank-two geometry is no longer floating beside the recursive state:
it is attached to a genuine family-changing ramified presentation.  This file
still does not claim strict progress from the presentation alone; that would
again confuse an internal geometric normalization with a recursive decrease.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry

/-- Honest pointed-reflection family attached to the stationary blocker which
generated the A17 zero-Schur chart. -/
noncomputable def pointedReflectionFamily
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  polynomialFamilyPointedReflection
    (K := K)
    G.problem.stationary.blocker.aligned.endpoint.movingSection
    G.problem.stationary.blocker.aligned.endpoint.family

/-- The corresponding actual scale-aware state.

Its raw clock is the endpoint clock and its scale is the incoming scale
multiplied by the fixed aligned-Smith ramification.  All finite bookkeeping
coordinates are unchanged. -/
noncomputable def pointedReflectionState
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect :=
    G.problem.stationary.blocker.aligned.endpoint.defect
  scale := alignedSmithRamificationIndex * s.scale
  scale_pos :=
    Nat.mul_pos alignedSmithRamificationIndex_pos s.scale_pos
  degreeCap := s.degreeCap
  sourceComplexity := s.sourceComplexity
  repair := s.repair
  family := G.pointedReflectionFamily
  movingSection :=
    G.problem.stationary.blocker.aligned.endpoint.movingSection
  hessianDefect := by
    dsimp [pointedReflectionFamily]
    exact
      polynomialFamilyPointedReflection_preservesHessianDefect
        (K := K)
        G.problem.stationary.blocker.aligned.endpoint.movingSection
        G.problem.stationary.blocker.aligned.endpoint.family
        G.problem.stationary.blocker.aligned.endpoint.hessianDefect
  nonlinearDegreeBound := by
    dsimp [pointedReflectionFamily]
    exact
      nonlinearDegreeBound_polynomialFamilyPointedReflection
        (K := K)
        s.degreeCap
        G.problem.stationary.blocker.aligned.endpoint.movingSection
        G.problem.stationary.blocker.aligned.endpoint.family
        G.problem.stationary.blocker.aligned.endpoint.nonlinearDegreeBound
  exactCollision := by
    dsimp [pointedReflectionFamily]
    exact
      polynomialFamilyPointedReflection_exactCollision
        (K := K)
        G.problem.stationary.blocker.aligned.endpoint.family
        G.problem.stationary.blocker.aligned.endpoint.movingSection
        G.problem.stationary.blocker.aligned.endpoint.exactCollision
  sectionSpecial :=
    G.problem.stationary.blocker.aligned.endpoint.sectionSpecial

@[simp]
theorem pointedReflectionState_rawDefect
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    G.pointedReflectionState.rawDefect =
      G.problem.stationary.blocker.aligned.endpoint.defect :=
  rfl

@[simp]
theorem pointedReflectionState_scale
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    G.pointedReflectionState.scale =
      alignedSmithRamificationIndex * s.scale :=
  rfl

@[simp]
theorem pointedReflectionState_repair
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    G.pointedReflectionState.repair = s.repair :=
  rfl

/-- The actual pointed-reflection state is a certified geometric
ramified-presentation move from the incoming state.

This is an internal move, not a recursive decrease.  Its raw/scale equality is
exactly the A17 retained clock equation. -/
theorem pointedReflectionState_internalMove
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    HasCertifiedRamifiedEpisodeInternalMove
      G.pointedReflectionState s := by
  change
    Nonempty
      (CertifiedRamifiedEpisodeInternalMove
        G.pointedReflectionState s)
  exact ⟨{
    ramification := alignedSmithRamificationIndex
    ramification_pos := alignedSmithRamificationIndex_pos
    scale_eq := rfl
    raw_eq := by
      simpa [pointedReflectionState] using G.clock_eq
    degreeCap_eq := rfl
    sourceComplexity_eq := rfl
    repair_eq := rfl
  }⟩

/-- The new state's special fibre is exactly the simultaneous-sign image of
the honest right-recentered special fibre on which the A17 zero-Schur chart
was computed.

This is the key A18.3 representation identity.  It attaches the finite
rank-two geometry to the actual presentation state by an invertible linear
source change, with no new existential family and no repair relabeling. -/
theorem pointedReflectionState_specialFiber_eq_sign_recentered
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    polynomialFamilySpecialFiber G.pointedReflectionState.family =
      allSourceSignHom (R := K)
        (polynomialFamilySpecialFiber G.problem.carrier.family) := by
  have hcarrier :
      G.problem.carrier.family =
        G.problem.stationary.blocker.aligned.endpoint.rightRecenteredFamily :=
    rfl
  rw [hcarrier]
  change
    polynomialFamilySpecialFiber
        (polynomialFamilyPointedReflection
          (K := K)
          G.problem.stationary.blocker.aligned.endpoint.movingSection
          G.problem.stationary.blocker.aligned.endpoint.family) =
      allSourceSignHom (R := K)
        (polynomialFamilySpecialFiber
          G.problem.stationary.blocker.aligned.endpoint.rightRecenteredFamily)
  rw [polynomialFamilyPointedReflection_specialFiber
    (K := K)
    G.problem.stationary.blocker.aligned.endpoint.family
    G.problem.stationary.blocker.aligned.endpoint.movingSection
    G.problem.stationary.blocker.aligned.endpoint.sectionSpecial]
  unfold fullPointedLongitudinalReflectionHom
  rw [G.problem.stationary.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
  simp [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber]

/-- In particular the pointed presentation has the same exact endpoint clock
as the chart geometry. -/
theorem pointedReflectionState_hessianDefect
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      G.pointedReflectionState.family
      G.problem.stationary.blocker.aligned.endpoint.defect :=
  G.pointedReflectionState.hessianDefect

end AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry

/-- A zero-Schur rank-two event realized on an actual scale-aware polynomial
family state.

The `geometry` field retains the complete A18.2 witness.  The remaining fields
certify that its canonical pointed reflection is an honest ramified
presentation of the incoming HC4 state and that the chart special fibre is
related to the presentation special fibre by the explicit involution
`X ↦ -X`. -/
structure AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  geometry :
    AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity
  internalMove :
    HasCertifiedRamifiedEpisodeInternalMove
      geometry.pointedReflectionState s
  specialFiber_eq :
    polynomialFamilySpecialFiber geometry.pointedReflectionState.family =
      allSourceSignHom (R := K)
        (polynomialFamilySpecialFiber geometry.problem.carrier.family)

/-- Every A18.2 zero-Schur geometry has an actual pointed-family
presentation. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry.toPointedPresentation
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation
      RR s complexity where
  geometry := G
  internalMove := G.pointedReflectionState_internalMove
  specialFiber_eq := G.pointedReflectionState_specialFiber_eq_sign_recentered

/-- A18.3 global outcome.

The old legacy rank-two macro is still quarantined.  The new zero-Schur branch
now contains a genuine family state rather than only a chart on an auxiliary
recentered representation. -/
inductive AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | legacyRankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | zeroSchurPointedRankTwo
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation
          RR s complexity))

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.3 actual-family rank-two presentation frontier.**

Every A18.2 source-honest zero-Schur geometry is now attached to an actual
scale-aware pointed-reflection state.  No successor is obtained from repair
progress in this theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalPointedRankTwoFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalGeometryCarryingFrontier
      RR complexity hsrepair with
  | zeroDefectReentry D =>
      exact .zeroDefectReentry D
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | legacyRankTwoMacro outer target hmove hprogress =>
      exact .legacyRankTwoMacro outer target hmove hprogress
  | zeroSchurRankTwoGeometry hG =>
      rcases hG with ⟨G⟩
      exact .zeroSchurPointedRankTwo ⟨G.toPointedPresentation⟩
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end
end HC4.Valuation
