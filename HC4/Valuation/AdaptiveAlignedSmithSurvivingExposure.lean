import HC4.Valuation.AdaptiveAlignedSmithStateBridge
import HC4.Valuation.AdaptiveSmithWallExposure
import Mathlib.Tactic

/-!
# Surviving aligned-Smith wall to an actual coefficientwise exposure

The aligned classifier's surviving branch has now been transported back to
the legacy adaptive-state interface.  The next existing constructor,
`adaptiveSmithExposureRamificationData`, requires the incoming Hessian clock
to be positive.

The adaptive state type itself does not assert positivity.  Accordingly the
honest interface is a dichotomy:

* the retained determinant defect is already zero; or
* one obtains a genuine integral adaptive Smith exposure, with its exact
  Hessian clock and exact balanced-subface special fibre.

No global interpretation of the zero-defect branch is made here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- All data needed to run the already-proved coefficientwise adaptive Smith
exposure from one surviving wall. -/
structure AdaptiveSurvivingWallExposureData
    (a : AdaptiveGeometricRestartState (K := K))
    (wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber) where
  commonLevel : ℕ
  commonLevel_eq :
    (commonLevel : ℤ) =
      wall.realization.combinedSourceLevel wall.level
  ramification :
    AdaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight
      commonLevel
      a.defect
  integrality :
    HasIntegralAdaptiveSmithExposure
      ramification.R
      wall.realization.combinedSourceWeight
      commonLevel
      (zeroJetNormalizedFamily a.family)

/-- The actual exposed family determined by the exposure data. -/
noncomputable def AdaptiveSurvivingWallExposureData.family
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  adaptiveSmithExposureFamily
    d.ramification.R
    wall.realization.combinedSourceWeight
    d.commonLevel
    (zeroJetNormalizedFamily a.family)
    d.integrality

/-- Exact determinant order of the exposed family. -/
def AdaptiveSurvivingWallExposureData.defect
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) : ℕ :=
  d.ramification.R * a.defect +
    2 * ∑ i : Fin 4, wall.realization.combinedSourceWeight i -
    4 * d.commonLevel

/-- The actual exposed family carries the exact transformed Hessian clock. -/
theorem AdaptiveSurvivingWallExposureData.hessianDefect
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    HasPolynomialFamilyHessianDefect
      (K := K) d.family d.defect := by
  unfold AdaptiveSurvivingWallExposureData.family
    AdaptiveSurvivingWallExposureData.defect
  exact
    adaptiveSmithExposureFamily_hasHessianDefect
      d.ramification.R
      wall.realization.combinedSourceWeight
      d.commonLevel
      a.defect
      d.ramification
      rfl
      (zeroJetNormalizedFamily a.family)
      d.integrality
      a.normalized_hessianDefect

/-- The special fibre of the actual exposure is exactly the balanced Smith
subface selected by the surviving wall. -/
theorem AdaptiveSurvivingWallExposureData.specialFiber_eq_balancedSubface
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    polynomialFamilySpecialFiber d.family =
      smithSubfacePolynomial (1 : Fin 4) 2 3
        (smithSymmetricBalancedSubface
          (smithProjectedSupport
            (1 : Fin 4) 2 3 a.normalizedSpecialFiber)
          wall.level wall.base)
        a.normalizedSpecialFiber := by
  let P := zeroJetNormalizedFamily a.family
  have hspecial :=
    HC4.Valuation.IntegralAdaptiveSurvivingSmithWall.specialFiber_adaptiveSmithExposureFamily
      P
      wall
      d.commonLevel
      d.commonLevel_eq
      d.ramification
      d.integrality
  simpa [AdaptiveSurvivingWallExposureData.family,
    P, AdaptiveGeometricRestartState.normalizedSpecialFiber] using hspecial

/-- Every surviving wall with positive determinant clock therefore produces
an honest coefficientwise exposure. -/
noncomputable def adaptiveSurvivingWallExposureData
    (a : AdaptiveGeometricRestartState (K := K))
    (wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber)
    (hdefect : 0 < a.defect) :
    AdaptiveSurvivingWallExposureData a wall := by
  let z : ℤ :=
    wall.realization.combinedSourceLevel wall.level
  have hz : 0 ≤ z := by
    dsimp [z]
    exact
      HC4.Valuation.IntegralAdaptiveSurvivingSmithWall.combinedSourceLevel_nonnegative
        wall
  let m : ℕ := z.toNat
  have hm : (m : ℤ) = z := by
    dsimp [m]
    exact Int.toNat_of_nonneg hz
  let ram :
      AdaptiveSmithExposureRamificationData
        wall.realization.combinedSourceWeight m a.defect :=
    adaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight
      m a.defect hdefect
  let P := zeroJetNormalizedFamily a.family
  have hint :
      HasIntegralAdaptiveSmithExposure
        ram.R wall.realization.combinedSourceWeight m P := by
    exact
      HC4.Valuation.IntegralAdaptiveSurvivingSmithWall.hasIntegralAdaptiveSmithExposure
        P wall m (by simpa [z] using hm) ram
  exact
    {
      commonLevel := m
      commonLevel_eq := by simpa [z] using hm
      ramification := ram
      integrality := by simpa [P] using hint
    }

/-- **Surviving-branch exposure dichotomy.**

The only obstruction to immediately constructing the old coefficientwise
exposure from the newly assembled aligned-Smith surviving branch is the
literal zero determinant clock.  In the positive-clock case the full
exposure data is constructed, not assumed. -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.zeroDefect_or_exposure
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint
      (K := K) s) :
    (W.original.aligned.toAdaptiveState s).defect = 0 ∨
      Nonempty
        (AdaptiveSurvivingWallExposureData
          (W.original.aligned.toAdaptiveState s)
          W.wall) := by
  let a := W.original.aligned.toAdaptiveState s
  by_cases hzero : a.defect = 0
  · exact Or.inl hzero
  · right
    have hpos : 0 < a.defect := Nat.pos_of_ne_zero hzero
    exact
      ⟨adaptiveSurvivingWallExposureData
        a W.wall hpos⟩

end

end HC4.Valuation
