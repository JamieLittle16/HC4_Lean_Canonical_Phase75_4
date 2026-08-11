import HC4.Valuation.AdaptiveAlignedSmithClassifierDispatcher
import HC4.Valuation.AdaptiveGeometricRestartState
import Mathlib.Tactic

/-!
# Aligned-Smith endpoint bridge to the legacy adaptive wall machinery

The new scale-aware aligned-Smith dispatcher classifies the *raw* special
fibre of a zero-source-jet endpoint.  The older, already-developed surviving
wall / exposure / packet machinery is indexed by an
`AdaptiveGeometricRestartState` and its `normalizedSpecialFiber`.

These two interfaces coincide exactly.

A family with zero source jet is a fixed point of `zeroJetNormalizedFamily`.
Hence an aligned minimal endpoint can be re-packaged as a legacy adaptive
state without altering its family, collision, determinant clock, or degree
cap, and its normalized special fibre is definitionally the raw special fibre
on which the new classifier produced its wall.

No progress relation is introduced here; this is only an interface bridge.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Zero-jet normalization is idempotent on zero-source-jet families -/

/-- A family whose source constant and linear coefficients already vanish is
fixed by full zero-jet normalization. -/
theorem HasZeroSourceJet.zeroJetNormalizedFamily_eq_self
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hP : HasZeroSourceJet P) :
    zeroJetNormalizedFamily P = P := by
  classical
  have hgrad :
      ∀ i : Fin 4, polynomialFamilyGradientAtZero P i = 0 := by
    intro i
    simpa [polynomialFamilyGradientAtZero] using hP.gradientAtZero i
  have hlinear :
      polynomialFamilyLinearPartAtZero P = 0 := by
    unfold polynomialFamilyLinearPartAtZero
    simp [hgrad]
  have hvalue :
      polynomialFamilyValueAtZero P = 0 := by
    simpa [polynomialFamilyValueAtZero] using hP.valueAtZero
  unfold zeroJetNormalizedFamily zeroGradientNormalizedFamily
  rw [hlinear, hvalue]
  simp

/-! ## Re-package an aligned endpoint as an ordinary adaptive state -/

/-- Forget only the scale provenance of the *incoming* state and use the
actual aligned endpoint family as a legacy adaptive state.

The finite source-complexity and repair coordinates are inherited unchanged;
the determinant defect is the exact defect carried by the aligned endpoint
itself. -/
noncomputable def AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    AdaptiveGeometricRestartState (K := K) where
  defect := E.endpoint.defect
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
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_family
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    (E.toAdaptiveState s).family = E.endpoint.family := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_defect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    (E.toAdaptiveState s).defect = E.endpoint.defect := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_degreeCap
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    (E.toAdaptiveState s).degreeCap = s.degreeCap := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_sourceComplexity
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    (E.toAdaptiveState s).sourceComplexity = s.sourceComplexity := rfl

@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    (E.toAdaptiveState s).repair = s.repair := rfl

/-- The decisive interface identity: for a zero-source-jet aligned endpoint,
the legacy state's normalized special fibre is exactly the raw special fibre
already classified by the aligned dispatcher. -/
@[simp]
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_normalizedSpecialFiber
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
      (K := K) s.degreeCap) :
    (E.toAdaptiveState s).normalizedSpecialFiber =
      E.endpoint.rawSpecialFiber := by
  change
    polynomialFamilySpecialFiber
        (zeroJetNormalizedFamily E.endpoint.family) =
      polynomialFamilySpecialFiber E.endpoint.family
  rw [E.zeroSourceJet.zeroJetNormalizedFamily_eq_self]

/-! ## Surviving-wall transport -/

/-- The surviving wall produced on the raw aligned special fibre is therefore
already a wall on the exact normalized special fibre expected by the legacy
adaptive exposure machinery. -/
noncomputable def AdaptiveAlignedSmithSurvivingWallEndpoint.toAdaptiveWall
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingWallEndpoint
      (K := K) s.degreeCap) :
    IntegralAdaptiveSurvivingSmithWall
      (W.aligned.toAdaptiveState s).normalizedSpecialFiber := by
  simpa using W.wall

/-- Dispatcher-facing surviving output with the legacy-compatible wall
certificate attached. -/
structure AdaptiveAlignedSmithSurvivingStateEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  original :
    AdaptiveAlignedSmithSurvivingWallEndpoint
      (K := K) s.degreeCap
  wall :
    IntegralAdaptiveSurvivingSmithWall
      (original.aligned.toAdaptiveState s).normalizedSpecialFiber

/-- Upgrade the already-green three-way Smith dispatcher so that its
surviving branch lands directly in the input interface of the existing
adaptive wall/exposure stack. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithLegacyClassifierDispatcher
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Nonempty
        (AdaptiveAlignedSmithBlockerEndpoint
          (K := K) s.degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSurvivingStateEndpoint
          (K := K) s) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection) := by
  rcases s.alignedSmithClassifierDispatcher with
    hblock | hsurvive | hboundary
  · exact Or.inl hblock
  · right
    left
    rcases hsurvive with ⟨W⟩
    exact
      ⟨{
        original := W
        wall := W.toAdaptiveWall s
      }⟩
  · exact Or.inr (Or.inr hboundary)

end

end HC4.Valuation
