import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionTransport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalUniformRamification
import Mathlib.Tactic

/-!
# A19.21: canonical re-entry after the positive Rees section frontier

The maximal section-frontier exposure of A19.19--20 already retains the exact
moving collision.  The old determinant-one three-shear can therefore be
applied unconditionally to its transported right section.  If the special
point is already `e0` the shear is the identity; otherwise A19.20 certifies an
actual transverse section boundary and the same shear is precisely the old
boundary normalization.

This yields one canonical scale-aware state at absolute scale `2 * s.scale`
and raw defect

    2 * (s.rawDefect - r),

where `r` is the maximal transportable transverse section weight.  Positive
source clock forces `r > 0`, so this state is an honest certified ramified
raw-defect spend from `s`.  If `r = s.rawDefect` its raw defect is zero.  If
`r < s.rawDefect`, A19.20 supplies the concrete boundary certificate.

Thus the post-clearing positive-clock branch has exactly the honest dichotomy
needed by final assembly: zero-defect exposure or removable section boundary.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The frontier family after the canonical three transverse source shears. -/
noncomputable def canonicalPositiveTransverseSectionFrontierShearedFamily
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  pointedBoundaryShearFamily
    (canonicalPositiveTransverseSectionFrontierRightSection
      (K := K) s.rawDefect s.movingSection)
    (canonicalPositiveTransverseSectionFrontierFamily
      s.rawDefect s.family hbound s.movingSection)

/-- The corresponding inverse action on the transported right section. -/
noncomputable def canonicalPositiveTransverseSectionFrontierShearedSection
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Fin 4 → Polynomial K :=
  pointedBoundarySequentialUnshearSection
    (canonicalPositiveTransverseSectionFrontierRightSection
      (K := K) s.rawDefect s.movingSection)

/-- The frontier exposure preserves the inherited nonlinear source-degree
ceiling. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontier_degreeBound
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    NonlinearDegreeBound s.degreeCap
      (canonicalPositiveTransverseSectionFrontierFamily
        s.rawDefect s.family hbound s.movingSection) := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  have hr : r ≤ s.rawDefect :=
    canonicalPositiveTransverseSectionFrontierWeight_le
      s.rawDefect s.movingSection
  let hbnd := hbound.mono hr
  change NonlinearDegreeBound s.degreeCap
    (adaptiveSmithExposureFamily
      2 (canonicalPositiveTransverseReesWeight r) (2 * r)
      s.family hbnd.integralExposure)
  exact nonlinearDegreeBound_adaptiveSmithExposureFamily
    s.degreeCap 2 (2 * r)
    (canonicalPositiveTransverseReesWeight r)
    s.family hbnd.integralExposure s.nonlinearDegreeBound

/-- The canonical three-shear keeps the same exact frontier Hessian clock. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierSheared_hessianDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    let r := canonicalPositiveTransverseSectionFrontierWeight
      s.rawDefect s.movingSection
    HasPolynomialFamilyHessianDefect (K := K)
      (canonicalPositiveTransverseSectionFrontierShearedFamily s hbound)
      (2 * (s.rawDefect - r)) := by
  dsimp
  exact hessianDefect_pointedBoundaryShearFamily
    (2 * (s.rawDefect -
      canonicalPositiveTransverseSectionFrontierWeight
        s.rawDefect s.movingSection))
    (canonicalPositiveTransverseSectionFrontierRightSection
      (K := K) s.rawDefect s.movingSection)
    (canonicalPositiveTransverseSectionFrontierFamily
      s.rawDefect s.family hbound s.movingSection)
    (canonicalPositiveTransverseSectionFrontierFamily_hessianDefect
      (K := K) s.rawDefect s.family s.hessianDefect hbound s.movingSection)

/-- The canonical three-shear preserves the inherited degree ceiling. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierSheared_degreeBound
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    NonlinearDegreeBound s.degreeCap
      (canonicalPositiveTransverseSectionFrontierShearedFamily s hbound) := by
  unfold canonicalPositiveTransverseSectionFrontierShearedFamily
  exact nonlinearDegreeBound_pointedBoundaryShearFamily
    s.degreeCap
    (canonicalPositiveTransverseSectionFrontierRightSection
      (K := K) s.rawDefect s.movingSection)
    (canonicalPositiveTransverseSectionFrontierFamily
      s.rawDefect s.family hbound s.movingSection)
    (s.canonicalPositiveTransverseSectionFrontier_degreeBound hbound)

/-- The canonical three-shear preserves the exact zero-left collision. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierSheared_exactCollision
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    HasPolynomialFamilyExactGradientCollision
      (canonicalPositiveTransverseSectionFrontierShearedFamily s hbound)
      (zeroPolynomialSection (K := K))
      (canonicalPositiveTransverseSectionFrontierShearedSection s) := by
  have hfrontier := s.canonicalPositiveTransverseSectionFrontier_exactCollision hbound
  have hfrontierZero :
      HasPolynomialFamilyExactGradientCollision
        (canonicalPositiveTransverseSectionFrontierFamily
          s.rawDefect s.family hbound s.movingSection)
        (zeroPolynomialSection (K := K))
        (canonicalPositiveTransverseSectionFrontierRightSection
          (K := K) s.rawDefect s.movingSection) := by
    simpa [canonicalPositiveTransverseSectionFrontierLeftSection_eq_zero
      (K := K) s.rawDefect s.movingSection] using hfrontier
  simpa [canonicalPositiveTransverseSectionFrontierShearedFamily,
    canonicalPositiveTransverseSectionFrontierShearedSection] using
    polynomialFamilyExactGradientCollision_pointedBoundaryShear
      (canonicalPositiveTransverseSectionFrontierFamily
        s.rawDefect s.family hbound s.movingSection)
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) s.rawDefect s.movingSection)
      hfrontierZero

/-- The sheared transported section is again canonically pointed at `e0`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierSheared_special
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    polynomialSectionSpecialPoint
        (canonicalPositiveTransverseSectionFrontierShearedSection s) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  unfold canonicalPositiveTransverseSectionFrontierShearedSection
  apply pointedBoundarySequentialUnshearSection_special_eq_axis
  exact canonicalPositiveTransverseSectionFrontierRightSpecial_zero
    (K := K) s.rawDefect s.movingSection s.sectionSpecial

/-- The canonical scale-aware state obtained after maximal section transport
and the old determinant-one boundary normalization. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  exact
    {
      rawDefect := 2 * (s.rawDefect - r)
      scale := 2 * s.scale
      scale_pos := Nat.mul_pos (by norm_num) s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := canonicalPositiveTransverseSectionFrontierShearedFamily s hbound
      movingSection := canonicalPositiveTransverseSectionFrontierShearedSection s
      hessianDefect := s.canonicalPositiveTransverseSectionFrontierSheared_hessianDefect hbound
      nonlinearDegreeBound :=
        s.canonicalPositiveTransverseSectionFrontierSheared_degreeBound hbound
      exactCollision :=
        s.canonicalPositiveTransverseSectionFrontierSheared_exactCollision hbound
      sectionSpecial :=
        s.canonicalPositiveTransverseSectionFrontierSheared_special
    }

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseSectionFrontierState hbound).rawDefect =
      2 * (s.rawDefect -
        canonicalPositiveTransverseSectionFrontierWeight
          s.rawDefect s.movingSection) := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseSectionFrontierState hbound).scale =
      2 * s.scale := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseSectionFrontierState hbound).repair =
      s.repair := rfl

/-- A transverse section coordinate vanishing at the parameter origin acquires
at least two parameter powers after ramification by two, so its capped order
is positive at every positive target clock. -/
theorem canonicalPositiveTransverseSectionOrderCap_parameterRamification_pos
    (Delta : ℕ) (p : Polynomial K)
    (hDelta : 0 < Delta)
    (hconst : Polynomial.constantCoeff p = 0) :
    0 < canonicalPositiveTransverseSectionOrderCap Delta
      (parameterRamificationHom (K := K) 2 p) := by
  classical
  by_cases hp : p = 0
  · subst p
    simpa [canonicalPositiveTransverseSectionOrderCap] using hDelta
  · have hX : Polynomial.X ∣ p := Polynomial.X_dvd_iff.mpr hconst
    have hX1 : Polynomial.X ^ 1 ∣ p := by simpa using hX
    have hram :
        Polynomial.X ^ 2 ∣ parameterRamificationHom (K := K) 2 p := by
      simpa using parameterRamification_pow_dvd (K := K) 2 1 p hX1
    have hne : parameterRamificationHom (K := K) 2 p ≠ 0 :=
      parameterRamificationHom_ne_zero_of_pos 2 (by norm_num) hp
    have horder :
        2 ≤ polynomialParameterOrder
          (parameterRamificationHom (K := K) 2 p) hne :=
      polynomial_X_pow_dvd_le_parameterOrder
        (parameterRamificationHom (K := K) 2 p) hne 2 hram
    unfold canonicalPositiveTransverseSectionOrderCap
    rw [dif_neg hne]
    apply lt_min
    · exact hDelta
    · omega

/-- Positive incoming clock forces the maximal common moving-section frontier
to spend a positive transverse weight. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierWeight_pos
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect) :
    0 < canonicalPositiveTransverseSectionFrontierWeight
      s.rawDefect s.movingSection := by
  have h1zero : Polynomial.constantCoeff (s.movingSection (1 : Fin 4)) = 0 := by
    have h := congrFun s.sectionSpecial (1 : Fin 4)
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using h
  have h2zero : Polynomial.constantCoeff (s.movingSection (2 : Fin 4)) = 0 := by
    have h := congrFun s.sectionSpecial (2 : Fin 4)
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using h
  have h3zero : Polynomial.constantCoeff (s.movingSection (3 : Fin 4)) = 0 := by
    have h := congrFun s.sectionSpecial (3 : Fin 4)
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using h
  have h1 := canonicalPositiveTransverseSectionOrderCap_parameterRamification_pos
    (K := K) s.rawDefect (s.movingSection (1 : Fin 4)) hpositive h1zero
  have h2 := canonicalPositiveTransverseSectionOrderCap_parameterRamification_pos
    (K := K) s.rawDefect (s.movingSection (2 : Fin 4)) hpositive h2zero
  have h3 := canonicalPositiveTransverseSectionOrderCap_parameterRamification_pos
    (K := K) s.rawDefect (s.movingSection (3 : Fin 4)) hpositive h3zero
  unfold canonicalPositiveTransverseSectionFrontierWeight
  simpa [parameterRamificationSection] using (lt_min h1 (lt_min h2 h3))

/-- The canonical frontier state is an honest ramified raw-defect spend from
any positive-clock source. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState_ramifiedSpend
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect)
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    CertifiedRamifiedRawDefectSpend
      (s.canonicalPositiveTransverseSectionFrontierState hbound) s := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  have hrpos : 0 < r :=
    s.canonicalPositiveTransverseSectionFrontierWeight_pos hpositive
  have hrle : r ≤ s.rawDefect :=
    canonicalPositiveTransverseSectionFrontierWeight_le
      s.rawDefect s.movingSection
  refine
    { ramification := 2
      ramification_pos := by norm_num
      scale_eq := rfl
      raw_lt := ?_ }
  change 2 * (s.rawDefect - r) < 2 * s.rawDefect
  omega

/-- The frontier state has raw defect zero exactly when section transport
reaches the full determinant-closing weight. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState_rawDefect_zero_iff
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseSectionFrontierState hbound).rawDefect = 0 ↔
      canonicalPositiveTransverseSectionFrontierWeight
        s.rawDefect s.movingSection = s.rawDefect := by
  have hrle := canonicalPositiveTransverseSectionFrontierWeight_le
    s.rawDefect s.movingSection
  simp only [ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierState_rawDefect]
  omega

/-- **Post-clearing positive-clock section dichotomy.**

Either maximal section transport reaches the determinant-closing weight and
hence raw defect zero, or it stops early at a concrete transverse boundary.
In both cases the canonically sheared state is already constructed; in the
early case it carries the certified ramified spend back into the existing
first-contact/descent architecture. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontier_zero_or_boundarySpend
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect)
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseSectionFrontierState hbound).rawDefect = 0 ∨
      (Nonempty
        (CanonicalPositiveTransverseSectionFrontierBoundary
          (K := K) s.rawDefect s.movingSection) ∧
       Nonempty
        (CertifiedRamifiedRawDefectSpend
          (s.canonicalPositiveTransverseSectionFrontierState hbound) s)) := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  have hrle : r ≤ s.rawDefect :=
    canonicalPositiveTransverseSectionFrontierWeight_le
      s.rawDefect s.movingSection
  by_cases hr : r = s.rawDefect
  · left
    exact (s.canonicalPositiveTransverseSectionFrontierState_rawDefect_zero_iff hbound).2 hr
  · right
    have hrlt : r < s.rawDefect := by omega
    refine ⟨?_, ?_⟩
    · exact canonicalPositiveTransverseSectionFrontier_boundary_of_lt
        (K := K) s.rawDefect s.movingSection hrlt
    · exact ⟨s.canonicalPositiveTransverseSectionFrontierState_ramifiedSpend
        hpositive hbound⟩

/-- **A19.21 positive-clock trichotomy.**

There are now only three honest outcomes, all source-facing:

* coefficient clearing fails at one of the four concrete low Smith patterns;
* the maximal transported Rees exposure reaches raw defect zero; or
* an actual transverse section boundary appears and the old determinant-one
  shear produces a certified ramified re-entry.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseRees_trichotomy
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect) :
    Nonempty
        (CanonicalPositiveTransverseReesLowLayer s.rawDefect s.family) ∨
      ∃ hbound : HasCanonicalPositiveTransverseReesCoefficientBound
          s.rawDefect s.family,
        (s.canonicalPositiveTransverseSectionFrontierState hbound).rawDefect = 0 ∨
          (Nonempty
            (CanonicalPositiveTransverseSectionFrontierBoundary
              (K := K) s.rawDefect s.movingSection) ∧
           Nonempty
            (CertifiedRamifiedRawDefectSpend
              (s.canonicalPositiveTransverseSectionFrontierState hbound) s)) := by
  classical
  by_cases hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound s.rawDefect s.family
  · right
    exact ⟨hbound,
      s.canonicalPositiveTransverseSectionFrontier_zero_or_boundarySpend
        hpositive hbound⟩
  · left
    exact canonicalPositiveTransverseReesLowLayer_of_not_bound
      hpositive hbound

end

end HC4.Valuation
