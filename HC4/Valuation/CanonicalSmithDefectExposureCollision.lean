import HC4.Valuation.CanonicalSmithDefectExposure
import HC4.Valuation.SeparatedSmithBoundaryClosure
import Mathlib.Tactic

/-!
# Exact marked collision on the defect-preserving Smith exposure

The defect-preserving family from `CanonicalSmithDefectExposure` was built
first at the potential level: ramify the true determinant parameter by twenty
and then take one integral symmetric Smith step `(2,2)`.

For terminal extraction we also need the *marked exact collision* on that
same family.  This file proves the missing section integrality and transports
the two moving sections through exactly the same ramification/Smith move.

The fixed ramification by twenty is deliberately much larger than the one-step
source exponents `(0,2,2,4)`.  Since the canonical marked points reduce to
`0` and `e₀`, every transverse moving coordinate has positive parameter order;
a single aligned Smith step therefore remains strictly before every section
wall.  Consequently the transformed sections are integral and their special
points remain exactly `0` and `e₀`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  One-step section integrality from canonical transverse special values
------------------------------------------------------------------------ -/

/-- A section whose transverse special coordinates are zero is integral under
ramification by twenty followed by the one-step symmetric Smith move `(2,2)`.

This is the marked-section analogue of
`CanonicalSmithLosslessFrontier.oneStepSmith_integralCoefficients`. -/
theorem oneStepSmith_sectionDivisibility_of_transverseSpecial_zero
    (c : Fin 4 → Polynomial K)
    (htrans :
      ∀ i : Fin 4, i ≠ 0 →
        Polynomial.constantCoeff (c i) = 0) :
    HasIntegralSmithConformalSectionDivisibility
      (K := K) 2 2
      (parameterRamificationSection
        (K := K) alignedSmithRamificationIndex c) := by
  simpa using
    (alignedSmith_sectionDivisibility_of_nonnegative
      (K := K) c 1 (by
        intro i hi0 hine
        have hpos :
            0 < sectionCoordinateParameterOrder (c i) :=
          sectionCoordinateParameterOrder_pos_of_constantCoeff_zero
            (c i) hine (htrans i hi0)
        by_cases hi3 : i = 3
        · rw [if_pos hi3]
          exact alignedSmithSectionValueFour_nonnegative
            (sectionCoordinateParameterOrder (c i)) 1 (by omega)
        · rw [if_neg hi3]
          exact alignedSmithSectionValueTwo_nonnegative
            (sectionCoordinateParameterOrder (c i)) 1 (by omega)))

/-- One one-step transformed section still has the same special point when
all original transverse special coordinates vanish. -/
theorem oneStepSmith_sectionSpecialPoint_eq_of_transverseSpecial_zero
    (c : Fin 4 → Polynomial K)
    (htrans :
      ∀ i : Fin 4, i ≠ 0 →
        Polynomial.constantCoeff (c i) = 0)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (K := K) 2 2
        (parameterRamificationSection
          (K := K) alignedSmithRamificationIndex c)) :
    polynomialSectionSpecialPoint
        (integralSmithConformalSection
          2 2
          (parameterRamificationSection
            (K := K) alignedSmithRamificationIndex c)
          hdiv) =
      polynomialSectionSpecialPoint c := by
  have hdivOne :
      HasIntegralSmithConformalSectionDivisibility
        (K := K) (2 * 1) (2 * 1)
        (parameterRamificationSection
          (K := K) alignedSmithRamificationIndex c) := by
    simpa using hdiv
  funext i
  by_cases hi0 : i = 0
  · subst i
    simpa [polynomialSectionSpecialPoint] using
      (alignedSmithSection_zeroCoordinate_constantCoeff
        (K := K) c 1 hdivOne)
  · have hc0 : Polynomial.constantCoeff (c i) = 0 :=
      htrans i hi0
    by_cases hz : c i = 0
    · have hq :=
        alignedSmithSection_zeroCoordinate
          (K := K) c 1 hdivOne hz
      change
        Polynomial.constantCoeff
            (integralSmithConformalSection
              2 2
              (parameterRamificationSection
                (K := K) alignedSmithRamificationIndex c)
              hdiv i) =
          Polynomial.constantCoeff (c i)
      rw [hc0]
      have hq' :
          integralSmithConformalSection
              2 2
              (parameterRamificationSection
                (K := K) alignedSmithRamificationIndex c)
              hdiv i = 0 := by
        simpa using hq
      rw [hq']
      simp
    · have hpos :
          0 < sectionCoordinateParameterOrder (c i) :=
        sectionCoordinateParameterOrder_pos_of_constantCoeff_zero
          (c i) hz hc0
      have hbefore :
          1 < alignedSmithSectionWallStep i (c i) := by
        unfold alignedSmithSectionWallStep
        by_cases hi3 : i = 3
        · rw [if_pos hi3]
          omega
        · rw [if_neg hi3]
          omega
      have hq0 :=
        alignedSmithSection_beforeWall_constantCoeff_zero
          (K := K) c 1 hdivOne hi0 hz hbefore
      change
        Polynomial.constantCoeff
            (integralSmithConformalSection
              2 2
              (parameterRamificationSection
                (K := K) alignedSmithRamificationIndex c)
              hdiv i) =
          Polynomial.constantCoeff (c i)
      have hq0' :
          Polynomial.constantCoeff
            (integralSmithConformalSection
              2 2
              (parameterRamificationSection
                (K := K) alignedSmithRamificationIndex c)
              hdiv i) = 0 := by
        simpa using hq0
      rw [hq0', hc0]

/-! -----------------------------------------------------------------------
  Canonical lossless frontier: transformed marked sections
------------------------------------------------------------------------ -/

/-- The left canonical marked section is legal for the one-step defect
exposure. -/
theorem CanonicalSmithLosslessFrontier.oneStepSmith_leftSectionDivisibility
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    HasIntegralSmithConformalSectionDivisibility
      (K := K) 2 2
      (parameterRamificationSection
        (K := K) alignedSmithRamificationIndex f.leftSection) := by
  exact
    oneStepSmith_sectionDivisibility_of_transverseSpecial_zero
      f.leftSection
      (specialPoint_zero_transverse_constantCoeff
        f.leftSection f.leftSpecial)

/-- The right canonical marked section is legal for the one-step defect
exposure. -/
theorem CanonicalSmithLosslessFrontier.oneStepSmith_rightSectionDivisibility
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    HasIntegralSmithConformalSectionDivisibility
      (K := K) 2 2
      (parameterRamificationSection
        (K := K) alignedSmithRamificationIndex f.rightSection) := by
  exact
    oneStepSmith_sectionDivisibility_of_transverseSpecial_zero
      f.rightSection
      (specialPoint_axis_transverse_constantCoeff
        f.rightSection f.rightSpecial)

/-- Left moving section on the actual defect-preserving exposure family. -/
noncomputable def CanonicalSmithLosslessFrontier.defectSmithExposureLeftSection
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    Fin 4 → Polynomial K :=
  integralSmithConformalSection
    2 2
    (parameterRamificationSection
      (K := K) alignedSmithRamificationIndex f.leftSection)
    f.oneStepSmith_leftSectionDivisibility

/-- Right moving section on the actual defect-preserving exposure family. -/
noncomputable def CanonicalSmithLosslessFrontier.defectSmithExposureRightSection
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    Fin 4 → Polynomial K :=
  integralSmithConformalSection
    2 2
    (parameterRamificationSection
      (K := K) alignedSmithRamificationIndex f.rightSection)
    f.oneStepSmith_rightSectionDivisibility

/-- The exact moving gradient collision survives the same ramification and
Smith step used to construct the defect-preserving exposure family. -/
theorem CanonicalSmithLosslessFrontier.defectSmithExposure_exactCollision
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    HasPolynomialFamilyExactGradientCollision
      f.defectSmithExposureFamily
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection := by
  have hram :
      HasPolynomialFamilyExactGradientCollision
        (parameterRamificationFamily
          (K := K) alignedSmithRamificationIndex f.family)
        (parameterRamificationSection
          (K := K) alignedSmithRamificationIndex f.leftSection)
        (parameterRamificationSection
          (K := K) alignedSmithRamificationIndex f.rightSection) :=
    polynomialFamilyExactGradientCollision_parameterRamification
      alignedSmithRamificationIndex
      f.family f.leftSection f.rightSection f.exactCollision
  simpa [CanonicalSmithLosslessFrontier.defectSmithExposureFamily,
    CanonicalSmithLosslessFrontier.defectSmithExposureLeftSection,
    CanonicalSmithLosslessFrontier.defectSmithExposureRightSection] using
    (polynomialFamilyExactGradientCollision_integralSmithConformal
      2 2
      (parameterRamificationFamily
        (K := K) alignedSmithRamificationIndex f.family)
      f.oneStepSmith_integralCoefficients
      (parameterRamificationSection
        (K := K) alignedSmithRamificationIndex f.leftSection)
      (parameterRamificationSection
        (K := K) alignedSmithRamificationIndex f.rightSection)
      f.oneStepSmith_leftSectionDivisibility
      f.oneStepSmith_rightSectionDivisibility
      hram)

/-- The transformed left section still reduces to the canonical origin. -/
theorem CanonicalSmithLosslessFrontier.defectSmithExposure_leftSpecial
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    polynomialSectionSpecialPoint f.defectSmithExposureLeftSection =
      (fun _ => (0 : K)) := by
  have hsame :=
    oneStepSmith_sectionSpecialPoint_eq_of_transverseSpecial_zero
      f.leftSection
      (specialPoint_zero_transverse_constantCoeff
        f.leftSection f.leftSpecial)
      f.oneStepSmith_leftSectionDivisibility
  have hsame' :
      polynomialSectionSpecialPoint f.defectSmithExposureLeftSection =
        polynomialSectionSpecialPoint f.leftSection := by
    simpa [CanonicalSmithLosslessFrontier.defectSmithExposureLeftSection]
      using hsame
  exact hsame'.trans f.leftSpecial

/-- The transformed right section still reduces to the canonical axis point
`e₀`. -/
theorem CanonicalSmithLosslessFrontier.defectSmithExposure_rightSpecial
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    polynomialSectionSpecialPoint f.defectSmithExposureRightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  have hsame :=
    oneStepSmith_sectionSpecialPoint_eq_of_transverseSpecial_zero
      f.rightSection
      (specialPoint_axis_transverse_constantCoeff
        f.rightSection f.rightSpecial)
      f.oneStepSmith_rightSectionDivisibility
  have hsame' :
      polynomialSectionSpecialPoint f.defectSmithExposureRightSection =
        polynomialSectionSpecialPoint f.rightSection := by
    simpa [CanonicalSmithLosslessFrontier.defectSmithExposureRightSection]
      using hsame
  exact hsame'.trans f.rightSpecial

/-! -----------------------------------------------------------------------
  Departure-frontier wrappers
------------------------------------------------------------------------ -/

noncomputable def CanonicalSmithDepartureFrontier.defectSmithExposureLeftSection
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    Fin 4 → Polynomial K :=
  f.lossless.defectSmithExposureLeftSection

noncomputable def CanonicalSmithDepartureFrontier.defectSmithExposureRightSection
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    Fin 4 → Polynomial K :=
  f.lossless.defectSmithExposureRightSection

/-- Exact marked collision on the very family consumed by the rigid Schur
clock. -/
theorem CanonicalSmithDepartureFrontier.defectSmithExposure_exactCollision
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    HasPolynomialFamilyExactGradientCollision
      f.defectSmithExposureFamily
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection := by
  exact f.lossless.defectSmithExposure_exactCollision

@[simp] theorem CanonicalSmithDepartureFrontier.defectSmithExposure_leftSpecial
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    polynomialSectionSpecialPoint f.defectSmithExposureLeftSection =
      (fun _ => (0 : K)) := by
  exact f.lossless.defectSmithExposure_leftSpecial

@[simp] theorem CanonicalSmithDepartureFrontier.defectSmithExposure_rightSpecial
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    polynomialSectionSpecialPoint f.defectSmithExposureRightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  exact f.lossless.defectSmithExposure_rightSpecial


/-- Full source homogeneity is also retained by the actual defect-preserving
exposure family.  Ramification changes only coefficients and the integral
Smith move is diagonal in the source variables, so ordinary source degree is
unchanged. -/
theorem CanonicalSmithDepartureFrontier.defectSmithExposure_isHomogeneous
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    f.defectSmithExposureFamily.IsHomogeneous D := by
  unfold CanonicalSmithDepartureFrontier.defectSmithExposureFamily
  unfold CanonicalSmithLosslessFrontier.defectSmithExposureFamily
  apply integralSmithConformalFamily_isHomogeneous
  exact f.homogeneous.map _

/-- The marked sections on the defect-preserving exposure still reduce to
two distinct source points. -/
theorem CanonicalSmithDepartureFrontier.defectSmithExposure_specialPoints_ne
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    polynomialSectionSpecialPoint f.defectSmithExposureLeftSection ≠
      polynomialSectionSpecialPoint f.defectSmithExposureRightSection := by
  rw [f.defectSmithExposure_leftSpecial,
    f.defectSmithExposure_rightSpecial]
  exact
    Ne.symm
      (coordinateAxisPoint_zero_ne_zeroPoint (K := K))

end

end HC4.Valuation
