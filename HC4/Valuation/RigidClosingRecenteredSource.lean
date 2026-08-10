import HC4.Valuation.RigidClosingExactCollisionSource
import HC4.Valuation.MovingCollisionRecentering

/-!
# Canonically recentered source data at a rigid closing

Phase 75.15 retained the actual defect-preserving polynomial family and its
two moving collision sections.  The terminal associated-graded fibre is a
local/affine object, so the next exact operation is to translate by the left
moving section.

This file packages the resulting family

    Q_tau(Y) = P^sharp_tau(Y + a^sharp(tau)).

It has:

* identically-zero left moving section;
* right moving section `b^sharp-a^sharp`;
* right special point exactly `e0`;
* the same pure Hessian defect;
* an exact moving gradient collision;
* a distinct special-fibre collision at `0` and `e0`.

No claim of weighted homogeneity is made here: translation deliberately
breaks ordinary homogeneity.  Weighted homogeneity belongs to the subsequent
source-lattice initial-form theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

namespace CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData

variable [CharZero K]
variable {D complexity : ℕ}
variable {f : CanonicalSmithDepartureFrontier (K := K) D complexity}

/-- The actual family recentered at the left moving collision section. -/
noncomputable def recenteredFamily
    (S : f.RigidClosingExactCollisionSourceData) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  polynomialFamilyTranslationHom
    (K := K)
    f.defectSmithExposureLeftSection
    f.defectSmithExposureFamily

/-- The right moving point in recentered coordinates. -/
def recenteredRightSection
    (S : f.RigidClosingExactCollisionSourceData) :
    Fin 4 -> Polynomial K :=
  polynomialSectionDifference
    f.defectSmithExposureLeftSection
    f.defectSmithExposureRightSection

/-- Exact collision after affine recentering. -/
theorem recenteredExactCollision
    (S : f.RigidClosingExactCollisionSourceData) :
    HasPolynomialFamilyExactGradientCollision
      S.recenteredFamily
      (zeroPolynomialSection (K := K))
      S.recenteredRightSection := by
  exact
    polynomialFamilyExactGradientCollision_recenter
      (K := K)
      f.defectSmithExposureFamily
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection
      S.exactCollision

/-- The pure determinant clock is unchanged by recentering. -/
theorem recenteredHessianDefect
    (S : f.RigidClosingExactCollisionSourceData) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      S.recenteredFamily
      (alignedSmithRamificationIndex * f.defect) := by
  exact
    polynomialFamilyTranslationHom_preservesHessianDefect
      (K := K)
      f.defectSmithExposureLeftSection
      f.defectSmithExposureFamily
      S.hessianDefect

/-- The recentered right moving section still reduces to the canonical
axis point `e0`. -/
theorem recenteredRightSpecial
    (S : f.RigidClosingExactCollisionSourceData) :
    polynomialSectionSpecialPoint S.recenteredRightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  exact
    polynomialSectionSpecialPoint_difference_eq_axis
      (K := K)
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection
      S.leftSpecial
      S.rightSpecial

/-- Hence the recentered special points are genuinely distinct. -/
theorem recenteredSpecialPoints_ne
    (S : f.RigidClosingExactCollisionSourceData) :
    (fun _ : Fin 4 => (0 : K)) ≠
      polynomialSectionSpecialPoint S.recenteredRightSection := by
  rw [S.recenteredRightSpecial]
  exact (coordinateAxisPoint_zero_ne_zeroPoint (K := K)).symm

/-- The recentered special fibre carries the canonical exact collision
`0 ~ e0`. -/
theorem recenteredSpecialFiber_exactCollision
    (S : f.RigidClosingExactCollisionSourceData) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber S.recenteredFamily)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have h :=
    recenteredPolynomialFamily_specialFiber_exactCollision
      (K := K)
      f.defectSmithExposureFamily
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection
      S.exactCollision
  change
    HasExactGradientCollision
      (polynomialFamilySpecialFiber S.recenteredFamily)
      (fun _ : Fin 4 => (0 : K))
      (polynomialSectionSpecialPoint S.recenteredRightSection) at h
  rw [S.recenteredRightSpecial] at h
  exact h

end CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData

/-- Canonical affine source data presented to the terminal lattice step.

Unlike `RigidClosingExactCollisionSourceData`, the left moving section has
already been absorbed into the source coordinates.  This is the correct
carrier for a Taylor/Newton associated graded: the left section is literally
zero and the surviving right section still reduces to `e0`. -/
structure CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Type _ where
  original : f.RigidClosingExactCollisionSourceData
  family : MvPolynomial (Fin 4) (Polynomial K)
  rightSection : Fin 4 -> Polynomial K
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) family
      (alignedSmithRamificationIndex * f.defect)
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family
      (fun _ : Fin 4 => (0 : Polynomial K))
      rightSection
  rightSpecial :
    polynomialSectionSpecialPoint rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Every source-level rigid closing datum has a canonical affine
recentring. -/
noncomputable def
    CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData.recenteredSourceData
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingExactCollisionSourceData) :
    f.RigidClosingRecenteredSourceData where
  original := S
  family := S.recenteredFamily
  rightSection := S.recenteredRightSection
  hessianDefect := S.recenteredHessianDefect
  exactCollision := S.recenteredExactCollision
  rightSpecial := S.recenteredRightSpecial

/-- The canonical recentered source has a distinct special-fibre collision
at `0` and `e0`. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.specialPoints_ne
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData) :
    (fun _ : Fin 4 => (0 : K)) ≠
      polynomialSectionSpecialPoint S.rightSection := by
  rw [S.rightSpecial]
  exact (coordinateAxisPoint_zero_ne_zeroPoint (K := K)).symm

/-- Its special fibre therefore carries the exact canonical collision. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.specialFiber_exactCollision
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber S.family)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have h :=
    polynomialFamilyExactGradientCollision_specialFiber
      S.family
      (fun _ : Fin 4 => (0 : Polynomial K))
      S.rightSection
      S.exactCollision
  have hzero :
      polynomialSectionSpecialPoint
          (fun _ : Fin 4 => (0 : Polynomial K)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext i
    simp [polynomialSectionSpecialPoint]
  rw [hzero, S.rightSpecial] at h
  exact h

end

end HC4.Valuation
