import HC4.Valuation.AdaptiveSectionBoundaryCollisionCovariance
import Mathlib.Tactic

/-!
# Hessian-defect covariance and adaptive re-entry for a section boundary

The elementary-shear layer already proves

`elementaryShearHom_preservesHessianDefect`.

The canonical boundary normalisation is a composition of the three transverse
determinant-one elementary shears in coordinates `1`, `2`, and `3`.
Accordingly the exact polynomial-family Hessian defect is unchanged by the
whole boundary shear.

Combined with the already-green results:

* canonical special point `e₀`;
* nonlinear degree-cap preservation;
* exact zero-left gradient collision;

this packages the sheared boundary family as a genuine
`AdaptiveGeometricRestartState`.

Thus an exposure-created section boundary is not terminal: it is removable
by a determinant-one source-coordinate change.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The canonical three-shear boundary transform preserves the exact
polynomial-family Hessian defect. -/
theorem hessianDefect_pointedBoundaryShearFamily
    (Delta : ℕ)
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : HasPolynomialFamilyHessianDefect P Delta) :
    HasPolynomialFamilyHessianDefect
      (pointedBoundaryShearFamily b P) Delta := by
  let c1 :=
    pointedBoundaryShearPolynomialCoefficient b (1 : Fin 4)
  let c2 :=
    pointedBoundaryShearPolynomialCoefficient b (2 : Fin 4)
  let c3 :=
    pointedBoundaryShearPolynomialCoefficient b (3 : Fin 4)

  have h1 :
      HasPolynomialFamilyHessianDefect
        (elementaryShearHom (K := K) (1 : Fin 4) c1 P)
        Delta := by
    exact
      elementaryShearHom_preservesHessianDefect
        (K := K) (Delta := Delta)
        (1 : Fin 4) (by decide) c1 P hP

  have h2 :
      HasPolynomialFamilyHessianDefect
        (elementaryShearHom (K := K) (2 : Fin 4) c2
          (elementaryShearHom (K := K) (1 : Fin 4) c1 P))
        Delta := by
    exact
      elementaryShearHom_preservesHessianDefect
        (K := K) (Delta := Delta)
        (2 : Fin 4) (by decide) c2
        (elementaryShearHom (K := K) (1 : Fin 4) c1 P)
        h1

  have h3 :
      HasPolynomialFamilyHessianDefect
        (elementaryShearHom (K := K) (3 : Fin 4) c3
          (elementaryShearHom (K := K) (2 : Fin 4) c2
            (elementaryShearHom (K := K) (1 : Fin 4) c1 P)))
        Delta := by
    exact
      elementaryShearHom_preservesHessianDefect
        (K := K) (Delta := Delta)
        (3 : Fin 4) (by decide) c3
        (elementaryShearHom (K := K) (2 : Fin 4) c2
          (elementaryShearHom (K := K) (1 : Fin 4) c1 P))
        h2

  simpa [pointedBoundaryShearFamily, c1, c2, c3] using h3

/-- The actual boundary-sheared exposure keeps exactly the same Hessian
defect as the coefficientwise Smith exposure. -/
theorem AdaptiveSurvivingWallExposureData.boundaryShearedFamily_hessianDefect
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    HasPolynomialFamilyHessianDefect
      d.boundaryShearedFamily d.defect := by
  unfold AdaptiveSurvivingWallExposureData.boundaryShearedFamily
  exact
    hessianDefect_pointedBoundaryShearFamily
      d.defect d.rightSection d.family d.hessianDefect

/-- **Boundary re-entry state.**

After the canonical determinant-one source shear, every exposed boundary
family becomes an ordinary adaptive geometric restart state with:

* unchanged exact Hessian defect;
* inherited degree cap and repair bookkeeping;
* exact zero-left collision;
* right special point exactly `e₀`.

No JC₂ input and no terminal assumption are used. -/
noncomputable def AdaptiveSurvivingWallExposureData.boundaryShearedAdaptiveState
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    AdaptiveGeometricRestartState (K := K) where
  defect := d.defect
  degreeCap := a.degreeCap
  sourceComplexity := a.sourceComplexity
  repair := a.repair
  family := d.boundaryShearedFamily
  movingSection := d.boundaryUnshearedSection
  hessianDefect := d.boundaryShearedFamily_hessianDefect
  nonlinearDegreeBound := d.boundaryShearedFamily_degreeBound
  exactCollision := by
    simpa [zeroPolynomialSection] using
      d.boundaryShearedFamily_exactCollision
  sectionSpecial := d.boundaryUnshearedSection_special

/-- The boundary re-entry state has exactly the exposure defect. -/
@[simp]
theorem AdaptiveSurvivingWallExposureData.boundaryShearedAdaptiveState_defect
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    d.boundaryShearedAdaptiveState.defect = d.defect := rfl

/-- Its degree ceiling is exactly the inherited degree ceiling. -/
@[simp]
theorem AdaptiveSurvivingWallExposureData.boundaryShearedAdaptiveState_degreeCap
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    d.boundaryShearedAdaptiveState.degreeCap = a.degreeCap := rfl

/-- Consequently an actual exposure section-boundary certificate always
admits canonical adaptive re-entry. -/
noncomputable def AdaptiveSmithExposureSectionBoundary.toAdaptiveState
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    {d : AdaptiveSurvivingWallExposureData a wall}
    (B : AdaptiveSmithExposureSectionBoundary d) :
    AdaptiveGeometricRestartState (K := K) :=
  d.boundaryShearedAdaptiveState

end

end HC4.Valuation
