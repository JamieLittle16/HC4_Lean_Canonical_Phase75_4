import HC4.Valuation.AdaptiveSectionBoundaryNormalization
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Canonical three-shear family attached to a section boundary

The marked-point normalization constructed in
`AdaptiveSectionBoundaryNormalization` is the inverse section action of a
single determinant-one unipotent source change

    y_i ↦ y_i + b_i(0) y_0,    i = 1,2,3.

The current repository already contains an elementary source shear
`elementaryShearHom k c` and the corresponding inverse section action
`elementaryUnshearSection k c`.  Since the three transverse shears use
distinct target coordinates and the common longitudinal coordinate `0`,
their composition gives the desired simultaneous unipotent change.

This file fixes the orientation of that composition and proves the two
purely algebraic facts needed before covariance is attached:

* the inverse section action is exactly `pointedBoundaryUnshearSection`;
* the source-degree ceiling is preserved.

No Hessian/collision covariance claim is made here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Polynomial coefficient used by the elementary source shear in transverse
coordinate `i`. -/
def pointedBoundaryShearPolynomialCoefficient
    (b : Fin 4 → Polynomial K) (i : Fin 4) : Polynomial K :=
  Polynomial.C (polynomialSectionSpecialPoint b i)

/-- The determinant-one source shear associated to the special point of `b`.

The order `1`, then `2`, then `3` is fixed only to make the Lean term
canonical.  Mathematically these three transvections commute. -/
def pointedBoundaryShearFamily
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  elementaryShearHom (K := K) (3 : Fin 4)
      (pointedBoundaryShearPolynomialCoefficient b (3 : Fin 4))
    (elementaryShearHom (K := K) (2 : Fin 4)
      (pointedBoundaryShearPolynomialCoefficient b (2 : Fin 4))
      (elementaryShearHom (K := K) (1 : Fin 4)
        (pointedBoundaryShearPolynomialCoefficient b (1 : Fin 4))
        P))

/-- Sequential inverse action of the same three elementary source shears on
a polynomial section. -/
def pointedBoundarySequentialUnshearSection
    (b : Fin 4 → Polynomial K) : Fin 4 → Polynomial K :=
  elementaryUnshearSection (3 : Fin 4)
      (pointedBoundaryShearPolynomialCoefficient b (3 : Fin 4))
    (elementaryUnshearSection (2 : Fin 4)
      (pointedBoundaryShearPolynomialCoefficient b (2 : Fin 4))
      (elementaryUnshearSection (1 : Fin 4)
        (pointedBoundaryShearPolynomialCoefficient b (1 : Fin 4))
        b))

/-- The sequential inverse action is exactly the simultaneous section
normalization from the previous module. -/
theorem pointedBoundarySequentialUnshearSection_eq
    (b : Fin 4 → Polynomial K) :
    pointedBoundarySequentialUnshearSection b =
      pointedBoundaryUnshearSection b := by
  funext i
  fin_cases i <;>
    simp [pointedBoundarySequentialUnshearSection,
      pointedBoundaryUnshearSection,
      pointedBoundaryShearPolynomialCoefficient,
      elementaryUnshearSection,
      polynomialSectionSpecialPoint]

/-- In particular the sequential inverse action has special point `e₀`
whenever the longitudinal special coordinate of `b` is `1`. -/
theorem pointedBoundarySequentialUnshearSection_special_eq_axis
    (b : Fin 4 → Polynomial K)
    (hb0 :
      polynomialSectionSpecialPoint b (0 : Fin 4) = 1) :
    polynomialSectionSpecialPoint
        (pointedBoundarySequentialUnshearSection b) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  rw [pointedBoundarySequentialUnshearSection_eq]
  exact pointedBoundaryUnshearSection_special_eq_axis b hb0

/-- The canonical three-shear source change preserves every nonlinear
source-degree ceiling. -/
theorem nonlinearDegreeBound_pointedBoundaryShearFamily
    (degreeCap : ℕ)
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound degreeCap P) :
    NonlinearDegreeBound degreeCap
      (pointedBoundaryShearFamily b P) := by
  unfold pointedBoundaryShearFamily
  apply nonlinearDegreeBound_elementaryShear
  apply nonlinearDegreeBound_elementaryShear
  apply nonlinearDegreeBound_elementaryShear
  exact hP

/-- Zero is fixed by the canonical source shear.  This is the section/family
base-point compatibility needed for the later exact-collision covariance
adapter. -/
@[simp]
theorem pointedBoundaryShearFamily_zero
    (b : Fin 4 → Polynomial K) :
    pointedBoundaryShearFamily b
        (0 : MvPolynomial (Fin 4) (Polynomial K)) = 0 := by
  simp [pointedBoundaryShearFamily]

/-! ## Application to an actual exposure boundary -/

/-- The family attached to one exposed section boundary. -/
noncomputable def AdaptiveSurvivingWallExposureData.boundaryShearedFamily
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  pointedBoundaryShearFamily d.rightSection d.family

/-- Its canonical right section is the inverse image of the exposed right
section under the same three elementary shears. -/
noncomputable def AdaptiveSurvivingWallExposureData.boundaryUnshearedSection
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    Fin 4 → Polynomial K :=
  pointedBoundarySequentialUnshearSection d.rightSection

/-- The transformed marked section is canonically based at `e₀`. -/
theorem AdaptiveSurvivingWallExposureData.boundaryUnshearedSection_special
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    polynomialSectionSpecialPoint d.boundaryUnshearedSection =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  unfold AdaptiveSurvivingWallExposureData.boundaryUnshearedSection
  apply pointedBoundarySequentialUnshearSection_special_eq_axis
  exact d.rightSpecial_zero

/-- The transformed family retains the inherited nonlinear degree cap. -/
theorem AdaptiveSurvivingWallExposureData.boundaryShearedFamily_degreeBound
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    NonlinearDegreeBound a.degreeCap d.boundaryShearedFamily := by
  unfold AdaptiveSurvivingWallExposureData.boundaryShearedFamily
  exact
    nonlinearDegreeBound_pointedBoundaryShearFamily
      a.degreeCap d.rightSection d.family d.nonlinearDegreeBound

end

end HC4.Valuation
