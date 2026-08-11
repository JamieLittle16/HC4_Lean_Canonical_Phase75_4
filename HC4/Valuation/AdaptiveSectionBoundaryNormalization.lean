import HC4.Valuation.AdaptiveAlignedSmithExposureGeometry
import Mathlib.Tactic

/-!
# Canonicalising a section-boundary marked point

A section-boundary endpoint is not a failure of the pointed geometry.  Its
right special point has first coordinate `1`, but one or more transverse
coordinates may be nonzero.

There is a canonical constant unipotent source shear that sends such a point
back to `e₀`.  At the level of polynomial sections its inverse action is
particularly simple:

    b'_0 = b_0,
    b'_i = b_i - b_i(0) b_0        (i ≠ 0).

Because `b_0(0)=1`, every transverse constant coefficient of `b'` vanishes.

This file proves only this pointed-section normalization and records the
constant shear coefficients.  The next file will transport the polynomial
family through the corresponding source shear and use the already compiled
linear-covariance API for the Hessian/gradient identities.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The transverse coefficient of the canonical unipotent shear determined
by the special point of `b`.  The longitudinal coefficient is forced to
zero. -/
def pointedBoundaryShearCoefficient
    (b : Fin 4 → Polynomial K) (i : Fin 4) : K :=
  if i = (0 : Fin 4) then 0
  else polynomialSectionSpecialPoint b i

@[simp]
theorem pointedBoundaryShearCoefficient_zero
    (b : Fin 4 → Polynomial K) :
    pointedBoundaryShearCoefficient b (0 : Fin 4) = 0 := by
  simp [pointedBoundaryShearCoefficient]

/-- Inverse action of the canonical boundary shear on a polynomial section.

This definition is deliberately simultaneous rather than a composition of
three elementary shears.  It therefore avoids any order dependence in the
pointed-section bookkeeping. -/
def pointedBoundaryUnshearSection
    (b : Fin 4 → Polynomial K) : Fin 4 → Polynomial K :=
  fun i =>
    if i = (0 : Fin 4) then b i
    else
      b i -
        Polynomial.C (polynomialSectionSpecialPoint b i) *
          b (0 : Fin 4)

@[simp]
theorem pointedBoundaryUnshearSection_zero
    (b : Fin 4 → Polynomial K) :
    pointedBoundaryUnshearSection b (0 : Fin 4) = b (0 : Fin 4) := by
  simp [pointedBoundaryUnshearSection]

/-- Every transverse coordinate has zero special value after the canonical
unshear, provided the original longitudinal special value is `1`. -/
theorem pointedBoundaryUnshearSection_special_transverse_zero
    (b : Fin 4 → Polynomial K)
    (hb0 :
      polynomialSectionSpecialPoint b (0 : Fin 4) = 1)
    (i : Fin 4)
    (hi : i ≠ (0 : Fin 4)) :
    polynomialSectionSpecialPoint
      (pointedBoundaryUnshearSection b) i = 0 := by
  have hb0' : (b (0 : Fin 4)).coeff 0 = 1 := by
    simpa [polynomialSectionSpecialPoint] using hb0
  simp only [polynomialSectionSpecialPoint]
  rw [show pointedBoundaryUnshearSection b i =
      b i -
        Polynomial.C
            (polynomialSectionSpecialPoint b i) *
          b (0 : Fin 4) by
        simp [pointedBoundaryUnshearSection, hi]]
  simp [polynomialSectionSpecialPoint, hb0']

/-- The longitudinal special coordinate is unchanged by the canonical
unshear. -/
theorem pointedBoundaryUnshearSection_special_zero
    (b : Fin 4 → Polynomial K) :
    polynomialSectionSpecialPoint
        (pointedBoundaryUnshearSection b) (0 : Fin 4) =
      polynomialSectionSpecialPoint b (0 : Fin 4) := by
  simp [polynomialSectionSpecialPoint,
    pointedBoundaryUnshearSection]

/-- **Canonical pointed normalization.**

Any polynomial section whose special point has longitudinal coordinate `1`
is sent by the canonical inverse unipotent shear to a section with special
point exactly `e₀`. -/
theorem pointedBoundaryUnshearSection_special_eq_axis
    (b : Fin 4 → Polynomial K)
    (hb0 :
      polynomialSectionSpecialPoint b (0 : Fin 4) = 1) :
    polynomialSectionSpecialPoint
        (pointedBoundaryUnshearSection b) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  funext i
  by_cases hi : i = (0 : Fin 4)
  · subst i
    simpa [coordinateAxisPoint] using
      pointedBoundaryUnshearSection_special_zero b |>.trans hb0
  · have hz :=
      pointedBoundaryUnshearSection_special_transverse_zero
        b hb0 i hi
    simpa [coordinateAxisPoint, hi] using hz

/-! ## Application to the actual adaptive Smith exposure boundary -/

/-- The canonical unshear sends the exposed right section back to the
standard pointed special point. -/
theorem AdaptiveSurvivingWallExposureData.pointedBoundaryUnshearSection_special
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      HC4.Newton.IntegralAdaptiveSurvivingSmithWall
        a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    polynomialSectionSpecialPoint
        (pointedBoundaryUnshearSection d.rightSection) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  apply pointedBoundaryUnshearSection_special_eq_axis
  exact d.rightSpecial_zero

/-- A recorded section boundary is therefore *coordinate-removable at the
marked-point level*: after the canonical inverse shear, the right marked
section is again based at `e₀`.

No statement about the transformed polynomial family is made here; that is
the next covariance adapter. -/
theorem AdaptiveSmithExposureSectionBoundary.canonicalMarkedSection
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall :
      HC4.Newton.IntegralAdaptiveSurvivingSmithWall
        a.normalizedSpecialFiber}
    {d : AdaptiveSurvivingWallExposureData a wall}
    (B : AdaptiveSmithExposureSectionBoundary d) :
    polynomialSectionSpecialPoint
        (pointedBoundaryUnshearSection d.rightSection) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  exact d.pointedBoundaryUnshearSection_special

end

end HC4.Valuation
