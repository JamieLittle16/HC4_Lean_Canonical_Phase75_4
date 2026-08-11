import HC4.Valuation.AdaptiveAlignedSmithSurvivingExposure
import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Valuation.AdaptiveDegreeTwoKernelActivity
import Mathlib.Tactic

/-!
# Pointed geometry of an adaptive surviving-wall exposure

The coefficientwise adaptive Smith exposure already carries the exact
Hessian clock and exact balanced-subface special fibre.  To feed it into the
degree-two saturated-kernel machinery we must also retain the moving
collision.

The existing adaptive exposure covariance theorem transports the exact
collision through one common ramification and the integral source diagonal.
The longitudinal source weight is exactly zero, so the right marked point
always retains first coordinate `1`.  Transverse coordinates can, however,
become nonzero after division by their source weights.

Accordingly the honest geometric output is:

* the exposed right section still has special point `e₀`, hence the exposed
  family is again an `AdaptiveGeometricRestartState`; or
* some transverse coordinate of the exposed right special point is nonzero,
  i.e. a genuine section-boundary event has occurred.

This file packages that dichotomy.  No global progress claim is made.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Support and degree-cap transport -/

/-- Adaptive Smith exposure introduces no new source exponent. -/
theorem support_adaptiveSmithExposureFamily_subset
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P) :
    (adaptiveSmithExposureFamily R W m P hint).support ⊆ P.support := by
  intro d hd
  by_contra hnot
  have hcoeff :
      MvPolynomial.coeff d
          (adaptiveSmithExposureFamily R W m P hint) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [coeff_adaptiveSmithExposureFamily] at hcoeff
  unfold adaptiveSmithExposureCoefficientQuotient at hcoeff
  simp [hnot] at hcoeff

/-- Hence the exposed family preserves every nonlinear source-degree cap. -/
theorem nonlinearDegreeBound_adaptiveSmithExposureFamily
    (degreeCap R m : ℕ)
    (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (hP : NonlinearDegreeBound degreeCap P) :
    NonlinearDegreeBound degreeCap
      (adaptiveSmithExposureFamily R W m P hint) := by
  exact
    nonlinearDegreeBound_of_support_subset hP
      (support_adaptiveSmithExposureFamily_subset R W m P hint)

/-! ## Canonical transformed sections attached to one exposure datum -/

/-- The integral left section of an adaptive surviving-wall exposure. -/
noncomputable def AdaptiveSurvivingWallExposureData.leftSection
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    Fin 4 → Polynomial K :=
  let W := wall.realization.combinedSourceWeight
  let aram :=
    parameterRamificationSection
      (K := K) d.ramification.R
      (zeroPolynomialSection (K := K))
  let hdiv :
      HasIntegralAdaptiveSmithSection W aram :=
    parameterRamificationSection_hasIntegralAdaptiveSmithSection
      d.ramification.R W
      d.ramification.sectionWeightsCovered
      (zeroPolynomialSection (K := K))
      (fun i => Or.inr (by simp [zeroPolynomialSection]))
  integralAdaptiveSmithSection W aram hdiv

/-- The integral right section of an adaptive surviving-wall exposure. -/
noncomputable def AdaptiveSurvivingWallExposureData.rightSection
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    Fin 4 → Polynomial K :=
  let W := wall.realization.combinedSourceWeight
  let bram :=
    parameterRamificationSection
      (K := K) d.ramification.R a.movingSection
  let hspecial :
      ∀ i, W i = 0 ∨
        Polynomial.constantCoeff (a.movingSection i) = 0 := by
    intro i
    by_cases hi : i = (0 : Fin 4)
    · left
      subst i
      exact wall.realization.combinedSourceWeight_zero
    · right
      have h := congrFun a.sectionSpecial i
      simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using h
  let hdiv :
      HasIntegralAdaptiveSmithSection W bram :=
    parameterRamificationSection_hasIntegralAdaptiveSmithSection
      d.ramification.R W
      d.ramification.sectionWeightsCovered
      a.movingSection hspecial
  integralAdaptiveSmithSection W bram hdiv

/-- The exposed left section is still literally zero. -/
theorem AdaptiveSurvivingWallExposureData.leftSection_eq_zero
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    d.leftSection = zeroPolynomialSection (K := K) := by
  funext i
  let W := wall.realization.combinedSourceWeight
  let aram :=
    parameterRamificationSection
      (K := K) d.ramification.R
      (zeroPolynomialSection (K := K))
  let hdiv :
      HasIntegralAdaptiveSmithSection W aram :=
    parameterRamificationSection_hasIntegralAdaptiveSmithSection
      d.ramification.R W
      d.ramification.sectionWeightsCovered
      (zeroPolynomialSection (K := K))
      (fun j => Or.inr (by simp [zeroPolynomialSection]))
  have hreinflate :=
    congrFun
      (adaptiveSmithInflateSection_integralSection_eq
        W aram hdiv) i
  have hramzero : aram i = 0 := by
    simp [aram, parameterRamificationSection,
      parameterRamificationHom, zeroPolynomialSection]
  have heq :
      Polynomial.X ^ W i *
          integralAdaptiveSmithSection W aram hdiv i =
        Polynomial.X ^ W i * 0 := by
    simpa [adaptiveSmithInflateSection, hramzero] using hreinflate
  have hcancel :=
    polynomial_X_pow_mul_cancel (K := K) (W i) heq
  simpa [AdaptiveSurvivingWallExposureData.leftSection,
    W, aram, hdiv, zeroPolynomialSection] using hcancel

/-- The actual exact collision survives on the two integral exposed sections. -/
theorem AdaptiveSurvivingWallExposureData.exactCollision
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    HasPolynomialFamilyExactGradientCollision
      d.family d.leftSection d.rightSection := by
  let W := wall.realization.combinedSourceWeight
  let P := zeroJetNormalizedFamily a.family
  have haSpecial :
      ∀ i, W i = 0 ∨
        Polynomial.constantCoeff
          ((zeroPolynomialSection (K := K)) i) = 0 := by
    intro i
    exact Or.inr (by simp [zeroPolynomialSection])
  have hbSpecial :
      ∀ i, W i = 0 ∨
        Polynomial.constantCoeff (a.movingSection i) = 0 := by
    intro i
    by_cases hi : i = (0 : Fin 4)
    · left
      subst i
      exact wall.realization.combinedSourceWeight_zero
    · right
      have h := congrFun a.sectionSpecial i
      simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using h
  have hcollP :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) a.movingSection := by
    simpa [P, zeroPolynomialSection] using
      polynomialFamilyExactGradientCollision_zeroJetNormalizedFamily
        a.family
        (fun _ : Fin 4 => (0 : Polynomial K))
        a.movingSection
        a.exactCollision
  have h :=
    polynomialFamilyExactGradientCollision_ramifiedAdaptiveSmithExposure
      d.ramification.R W d.commonLevel
      d.ramification.R_pos
      P d.integrality
      (zeroPolynomialSection (K := K))
      a.movingSection
      d.ramification.sectionWeightsCovered
      haSpecial hbSpecial hcollP
  simpa [AdaptiveSurvivingWallExposureData.family,
    AdaptiveSurvivingWallExposureData.leftSection,
    AdaptiveSurvivingWallExposureData.rightSection,
    W, P] using h

/-- The exposed family retains the inherited nonlinear degree cap. -/
theorem AdaptiveSurvivingWallExposureData.nonlinearDegreeBound
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    NonlinearDegreeBound a.degreeCap d.family := by
  unfold AdaptiveSurvivingWallExposureData.family
  exact
    nonlinearDegreeBound_adaptiveSmithExposureFamily
      a.degreeCap d.ramification.R d.commonLevel
      wall.realization.combinedSourceWeight
      (zeroJetNormalizedFamily a.family)
      d.integrality
      a.normalized_nonlinearDegreeBound

/-! ## The right marked point: canonical or boundary -/

/-- Coordinate zero of the exposed right marked point is always `1`. -/
theorem AdaptiveSurvivingWallExposureData.rightSpecial_zero
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    polynomialSectionSpecialPoint d.rightSection (0 : Fin 4) = 1 := by
  let W := wall.realization.combinedSourceWeight
  let bram :=
    parameterRamificationSection
      (K := K) d.ramification.R a.movingSection
  let hspecial :
      ∀ i, W i = 0 ∨
        Polynomial.constantCoeff (a.movingSection i) = 0 := by
    intro i
    by_cases hi : i = (0 : Fin 4)
    · left
      subst i
      exact wall.realization.combinedSourceWeight_zero
    · right
      have h := congrFun a.sectionSpecial i
      simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using h
  let hdiv :
      HasIntegralAdaptiveSmithSection W bram :=
    parameterRamificationSection_hasIntegralAdaptiveSmithSection
      d.ramification.R W
      d.ramification.sectionWeightsCovered
      a.movingSection hspecial
  have hreinflate :=
    congrFun
      (adaptiveSmithInflateSection_integralSection_eq
        W bram hdiv) (0 : Fin 4)
  have hW0 : W (0 : Fin 4) = 0 :=
    wall.realization.combinedSourceWeight_zero
  have hsection0 :
      integralAdaptiveSmithSection W bram hdiv (0 : Fin 4) =
        bram (0 : Fin 4) := by
    simpa [adaptiveSmithInflateSection, hW0] using hreinflate
  have hramSpecial :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      d.ramification.R d.ramification.R_pos a.movingSection]
    exact a.sectionSpecial
  have hram0 := congrFun hramSpecial (0 : Fin 4)
  change Polynomial.constantCoeff (d.rightSection (0 : Fin 4)) = 1
  rw [show d.rightSection (0 : Fin 4) =
      integralAdaptiveSmithSection W bram hdiv (0 : Fin 4) by
        rfl]
  rw [hsection0]
  simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hram0

/-- A genuine transverse special-point departure created by the adaptive
source exposure. -/
structure AdaptiveSmithExposureSectionBoundary
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) : Type where
  coordinate : Fin 4
  coordinate_ne_zero : coordinate ≠ (0 : Fin 4)
  special_ne_zero :
    polynomialSectionSpecialPoint d.rightSection coordinate ≠ 0

/-- The exposed right section either remains at `e₀`, or it has an actual
nonzero transverse special coordinate. -/
theorem AdaptiveSurvivingWallExposureData.canonicalSpecial_or_boundary
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    polynomialSectionSpecialPoint d.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4) ∨
      Nonempty (AdaptiveSmithExposureSectionBoundary d) := by
  classical
  by_cases hspecial :
      polynomialSectionSpecialPoint d.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4)
  · exact Or.inl hspecial
  · right
    have hex :
        ∃ i : Fin 4, i ≠ (0 : Fin 4) ∧
          polynomialSectionSpecialPoint d.rightSection i ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hspecial
      funext i
      by_cases hi : i = (0 : Fin 4)
      · subst i
        simpa [coordinateAxisPoint] using d.rightSpecial_zero
      · have hz := hnone i hi
        simpa [coordinateAxisPoint, hi] using hz
    rcases hex with ⟨i, hi, hne⟩
    exact ⟨{ coordinate := i
             coordinate_ne_zero := hi
             special_ne_zero := hne }⟩

/-! ## Re-entry as an ordinary adaptive state -/

/-- If no section boundary appears, the exposed family is again an ordinary
adaptive geometric restart state. -/
noncomputable def AdaptiveSurvivingWallExposureData.toAdaptiveState
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall)
    (hspecial :
      polynomialSectionSpecialPoint d.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    AdaptiveGeometricRestartState (K := K) where
  defect := d.defect
  degreeCap := a.degreeCap
  sourceComplexity := a.sourceComplexity
  repair := a.repair
  family := d.family
  movingSection := d.rightSection
  hessianDefect := d.hessianDefect
  nonlinearDegreeBound := d.nonlinearDegreeBound
  exactCollision := by
    simpa [d.leftSection_eq_zero, zeroPolynomialSection] using d.exactCollision
  sectionSpecial := hspecial

/-- The re-entry state's special fibre is the exact balanced Smith subface
already computed by the exposure theorem. -/
theorem AdaptiveSurvivingWallExposureData.toAdaptiveState_specialFiber
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall)
    (hspecial :
      polynomialSectionSpecialPoint d.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialFamilySpecialFiber (d.toAdaptiveState hspecial).family =
      smithSubfacePolynomial (1 : Fin 4) 2 3
        (smithSymmetricBalancedSubface
          (smithProjectedSupport
            (1 : Fin 4) 2 3 a.normalizedSpecialFiber)
          wall.level wall.base)
        a.normalizedSpecialFiber := by
  exact d.specialFiber_eq_balancedSubface

end

end HC4.Valuation
