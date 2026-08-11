import HC4.Valuation.AdaptiveDegreeTwoKernelRestart

/-!
# Canonical realizable Smith wall for an adaptive special fibre

The constant scalar grade is already an honest integral Smith grade.  On a
nonempty projected support, the fixed symmetric separator gives the exact
dichotomy needed by the global dispatcher: either this canonical wall is
minimal and enters the adaptive classifier, or the existing strict Smith
improvement branch applies.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The constant-zero Smith grade is induced by the zero transverse source
weight and hence is geometrically realizable for every polynomial. -/
def constantZeroIntegralAdaptiveSmithWallWeight
    (F : MvPolynomial (Fin 4) K) :
    HasIntegralAdaptiveSmithWallWeight F (fun _ => (0 : ℤ)) where
  transverseWeight := fun _ => 0
  offset := 0
  realizes := by
    intro e he
    simp

/-- Complete input certificate for the canonical scalar wall `base = 0`,
`level = 0`. -/
structure CanonicalAdaptiveSmithWallData
    (F : MvPolynomial (Fin 4) K) : Prop where
  minimal :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport (1 : Fin 4) 2 3 F) 0
      (fun _ => (0 : ℤ))
  attained :
    ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
      (fun _ => (0 : ℤ)) e = 0

def CanonicalAdaptiveSmithWallData.realization
    {F : MvPolynomial (Fin 4) K}
    (_h : CanonicalAdaptiveSmithWallData F) :
    HasIntegralAdaptiveSmithWallWeight F (fun _ => (0 : ℤ)) :=
  constantZeroIntegralAdaptiveSmithWallWeight F

theorem CanonicalAdaptiveSmithWallData.lowerBound
    {F : MvPolynomial (Fin 4) K}
    (_h : CanonicalAdaptiveSmithWallData F) :
    ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
      (0 : ℤ) ≤ (fun _ => (0 : ℤ)) e := by
  simp

/-- Every nonempty projected support has either a canonical realizable
minimal wall or the already-defined strict symmetric improvement. -/
theorem canonicalAdaptiveSmithWall_or_strictImprovement
    (F : MvPolynomial (Fin 4) K)
    (hne : (smithProjectedSupport (1 : Fin 4) 2 3 F).Nonempty) :
    CanonicalAdaptiveSmithWallData F ∨
      HasStrictSymmetricSmithImprovement
        (smithProjectedSupport (1 : Fin 4) 2 3 F) 0
        (fun _ => (0 : ℤ)) := by
  rcases symmetricSmithPoleMinimal_or_strictImprovement
      (smithProjectedSupport (1 : Fin 4) 2 3 F) 0
      (fun _ => (0 : ℤ)) with hminimal | hstrict
  · left
    rcases hne with ⟨e, he⟩
    exact ⟨hminimal, ⟨e, he, rfl⟩⟩
  · exact Or.inr hstrict

/-- State-neutral normalized axis data consumed by the adaptive Smith wall
splitter. -/
def HasNormalizedSmithAxisData
    (F : MvPolynomial (Fin 4) K) : Prop :=
  HasExactGradientCollision F
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) ∧
    (∀ i : Fin 4,
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv i F) = 0) ∧
    MvPolynomial.eval
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0

/-- Canonical integral wall classification depends only on a normalized
special-fibre polynomial and its axis data, not on the representation of the
global determinant clock. -/
theorem classifyCanonicalIntegralWallOfSpecialFiber
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (haxis : HasNormalizedSmithAxisData F)
    (hwall : CanonicalAdaptiveSmithWallData F) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        (fun _ => (0 : ℤ)) e = 0 ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome F e) ∨
      Nonempty (IntegralAdaptiveSurvivingSmithWall F) := by
  rcases haxis with ⟨hcoll, hzero, hvalue⟩
  exact adaptiveWall_blocker_or_integralSurvivingWall
    F (fun _ => (0 : ℤ)) 0 hwall.realization hwall.lowerBound
    hwall.attained hwall.minimal hcoll hzero hvalue

/-- On its minimal side, the canonical wall plugs directly into the honest
integral adaptive wall classifier without any externally chosen grade. -/
theorem AdaptiveGeometricRestartState.classifyCanonicalIntegralWall
    [CharZero K]
    (s : AdaptiveGeometricRestartState (K := K))
    (hwall : CanonicalAdaptiveSmithWallData s.normalizedSpecialFiber) :
    (∃ e ∈ smithProjectedSupport
        (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        (fun _ => (0 : ℤ)) e = 0 ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome s.normalizedSpecialFiber e) ∨
      Nonempty
        (IntegralAdaptiveSurvivingSmithWall
          s.normalizedSpecialFiber) := by
  exact classifyCanonicalIntegralWallOfSpecialFiber
    s.normalizedSpecialFiber s.normalizedSpecialFiber_axisData hwall

/-! ## Scale-aware wrapper -/

/-- Zero-jet-normalized special fibre of a scale-aware state.  This operation
does not inspect or alter `rawDefect` or `scale`. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.normalizedSpecialFiber
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber (zeroJetNormalizedFamily s.family)

theorem ScaleAwareAdaptiveGeometricRestartState.normalizedSpecialFiber_axisData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    HasNormalizedSmithAxisData s.normalizedSpecialFiber := by
  simpa [HasNormalizedSmithAxisData,
    ScaleAwareAdaptiveGeometricRestartState.normalizedSpecialFiber] using
    zeroJetNormalizedSpecialFiber_axisData
      s.family s.movingSection s.exactCollision s.sectionSpecial

/-- Scale-aware states use the same state-neutral canonical classifier while
retaining their ramification scale definitionally. -/
theorem ScaleAwareAdaptiveGeometricRestartState.classifyCanonicalIntegralWall
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hwall : CanonicalAdaptiveSmithWallData s.normalizedSpecialFiber) :
    (∃ e ∈ smithProjectedSupport
        (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        (fun _ => (0 : ℤ)) e = 0 ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome s.normalizedSpecialFiber e) ∨
      Nonempty
        (IntegralAdaptiveSurvivingSmithWall
          s.normalizedSpecialFiber) := by
  exact classifyCanonicalIntegralWallOfSpecialFiber
    s.normalizedSpecialFiber s.normalizedSpecialFiber_axisData hwall

end

end HC4.Valuation
