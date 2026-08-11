import HC4.Valuation.AdaptiveSectionBoundaryShearFamily
import Mathlib.Tactic

/-!
# Exact collision covariance for the canonical boundary shear

The elementary-shear layer already contains the exact gradient-collision
covariance theorem

`polynomialFamilyExactGradientCollision_elementaryShear`.

The previous draft of this file unnecessarily redeclared that theorem and
several of its supporting evaluation/derivative lemmas.  This module now does
only the genuinely new work: compose the existing one-shear covariance through
the three canonical transverse shears attached to a section boundary.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- One elementary inverse shear fixes the literal zero polynomial section. -/
private theorem zeroSection_elementaryUnshear
    (k : Fin 4) (c : Polynomial K) :
    elementaryUnshearSection k c
        (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  simp [elementaryUnshearSection, zeroPolynomialSection]

/-- Iterating the already-compiled one-shear exact-collision covariance
through the canonical boundary three-shear preserves the exact zero-left
collision. -/
theorem polynomialFamilyExactGradientCollision_pointedBoundaryShear
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b) :
    HasPolynomialFamilyExactGradientCollision
      (pointedBoundaryShearFamily b P)
      (zeroPolynomialSection (K := K))
      (pointedBoundarySequentialUnshearSection b) := by
  let c1 :=
    pointedBoundaryShearPolynomialCoefficient b (1 : Fin 4)
  let c2 :=
    pointedBoundaryShearPolynomialCoefficient b (2 : Fin 4)
  let c3 :=
    pointedBoundaryShearPolynomialCoefficient b (3 : Fin 4)

  have h1 :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K) (1 : Fin 4) (by decide) c1
      P (zeroPolynomialSection (K := K)) b hcoll

  have h1' :
      HasPolynomialFamilyExactGradientCollision
        (elementaryShearHom (K := K) (1 : Fin 4) c1 P)
        (zeroPolynomialSection (K := K))
        (elementaryUnshearSection (1 : Fin 4) c1 b) := by
    rw [zeroSection_elementaryUnshear] at h1
    exact h1

  have h2 :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K) (2 : Fin 4) (by decide) c2
      (elementaryShearHom (K := K) (1 : Fin 4) c1 P)
      (zeroPolynomialSection (K := K))
      (elementaryUnshearSection (1 : Fin 4) c1 b)
      h1'

  have h2' :
      HasPolynomialFamilyExactGradientCollision
        (elementaryShearHom (K := K) (2 : Fin 4) c2
          (elementaryShearHom (K := K) (1 : Fin 4) c1 P))
        (zeroPolynomialSection (K := K))
        (elementaryUnshearSection (2 : Fin 4) c2
          (elementaryUnshearSection (1 : Fin 4) c1 b)) := by
    rw [zeroSection_elementaryUnshear] at h2
    exact h2

  have h3 :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K) (3 : Fin 4) (by decide) c3
      (elementaryShearHom (K := K) (2 : Fin 4) c2
        (elementaryShearHom (K := K) (1 : Fin 4) c1 P))
      (zeroPolynomialSection (K := K))
      (elementaryUnshearSection (2 : Fin 4) c2
        (elementaryUnshearSection (1 : Fin 4) c1 b))
      h2'

  rw [zeroSection_elementaryUnshear] at h3
  simpa [pointedBoundaryShearFamily,
    pointedBoundarySequentialUnshearSection,
    c1, c2, c3] using h3

/-- The canonical boundary-sheared exposure retains the exact zero-left
gradient collision. -/
theorem AdaptiveSurvivingWallExposureData.boundaryShearedFamily_exactCollision
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    HasPolynomialFamilyExactGradientCollision
      d.boundaryShearedFamily
      (zeroPolynomialSection (K := K))
      d.boundaryUnshearedSection := by
  unfold AdaptiveSurvivingWallExposureData.boundaryShearedFamily
    AdaptiveSurvivingWallExposureData.boundaryUnshearedSection
  exact
    polynomialFamilyExactGradientCollision_pointedBoundaryShear
      d.family d.rightSection
      (by
        simpa [d.leftSection_eq_zero, zeroPolynomialSection] using
          d.exactCollision)

end

end HC4.Valuation
