import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionTransport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalUniformRamification
import Mathlib.Tactic

/-!
# A19.21: determinant-one re-entry for the positive Rees section frontier

A19.20 proves the exact source-facing trichotomy after coefficient clearing:
the maximal transverse section transport either reaches the full determinant-
closing weight, or it stops at a genuine transverse special-point boundary.

No new boundary geometry is needed.  The already-green canonical three-shear
normalization applies to the transported right section itself.  Its covariance
theorems preserve the exact Hessian clock, nonlinear source-degree bound and
zero-left exact gradient collision, while restoring the right special point to
`e0`.

This file packages that normalized family as a scale-aware adaptive state.  The
fixed parameter ramification is exactly two, and the frontier weight is
strictly positive at every positive incoming clock.  Consequently the re-entry
state has raw clock

    2 * (Delta - r) < 2 * Delta

at absolute scale `2 * source.scale`: it is an honest certified ramified raw-
defect spend, precisely the existing A18 interface.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A nonzero polynomial with zero constant coefficient has positive exact
parameter order.  Hence its capped order is positive at every positive cap. -/
theorem canonicalPositiveTransverseSectionOrderCap_pos_of_constantCoeff_zero
    (Delta : ℕ) (p : Polynomial K)
    (hDelta : 0 < Delta)
    (hconst : Polynomial.constantCoeff p = 0) :
    0 < canonicalPositiveTransverseSectionOrderCap Delta p := by
  classical
  by_cases hp : p = 0
  · simp [canonicalPositiveTransverseSectionOrderCap, hp, hDelta]
  · have hX : Polynomial.X ∣ p := Polynomial.X_dvd_iff.mpr hconst
    have hX1 : Polynomial.X ^ 1 ∣ p := by simpa using hX
    have horder : 1 ≤ polynomialParameterOrder p hp :=
      polynomial_X_pow_dvd_le_parameterOrder p hp 1 hX1
    have horderPos : 0 < polynomialParameterOrder p hp := by omega
    simpa [canonicalPositiveTransverseSectionOrderCap, hp] using
      (lt_min hDelta horderPos)

/-- The maximal common transverse section weight is strictly positive on a
positive-clock canonical marked section.  Ramification by two preserves the
zero transverse special coordinates before the exact-order cap is taken. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontierWeight_pos
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect) :
    0 < canonicalPositiveTransverseSectionFrontierWeight
      s.rawDefect s.movingSection := by
  let bram := parameterRamificationSection (K := K) 2 s.movingSection
  have hconst :
      ∀ i : Fin 4, i ≠ (0 : Fin 4) →
        Polynomial.constantCoeff (bram i) = 0 := by
    intro i hi
    unfold bram parameterRamificationSection
    rw [constantCoeff_parameterRamificationHom (K := K) 2 (by norm_num)]
    have h := congrFun s.sectionSpecial i
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using h
  unfold canonicalPositiveTransverseSectionFrontierWeight
  exact lt_min
    (canonicalPositiveTransverseSectionOrderCap_pos_of_constantCoeff_zero
      s.rawDefect (bram (1 : Fin 4)) hpositive (hconst 1 (by decide)))
    (lt_min
      (canonicalPositiveTransverseSectionOrderCap_pos_of_constantCoeff_zero
        s.rawDefect (bram (2 : Fin 4)) hpositive (hconst 2 (by decide)))
      (canonicalPositiveTransverseSectionOrderCap_pos_of_constantCoeff_zero
        s.rawDefect (bram (3 : Fin 4)) hpositive (hconst 3 (by decide))))

/-- The maximal section-frontier family inherits the incoming nonlinear source
degree cap. -/
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

/-- Canonical determinant-one three-shear normalization of the transported
section-frontier family. -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseBoundaryReentryState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  let P := canonicalPositiveTransverseSectionFrontierFamily
    s.rawDefect s.family hbound s.movingSection
  let b := canonicalPositiveTransverseSectionFrontierRightSection
    (K := K) s.rawDefect s.movingSection
  have hfrontDef :
      HasPolynomialFamilyHessianDefect (K := K) P
        (2 * (s.rawDefect - r)) := by
    simpa [P, r] using
      canonicalPositiveTransverseSectionFrontierFamily_hessianDefect
        s.rawDefect s.family s.hessianDefect hbound s.movingSection
  have hfrontDegree : NonlinearDegreeBound s.degreeCap P := by
    simpa [P] using s.canonicalPositiveTransverseSectionFrontier_degreeBound hbound
  have hfrontColl := s.canonicalPositiveTransverseSectionFrontier_exactCollision hbound
  have hleft := canonicalPositiveTransverseSectionFrontierLeftSection_eq_zero
    (K := K) s.rawDefect s.movingSection
  have hfrontCollZero :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b := by
    rw [hleft] at hfrontColl
    simpa [P, b] using hfrontColl
  have hb0 : polynomialSectionSpecialPoint b (0 : Fin 4) = 1 := by
    simpa [b] using
      canonicalPositiveTransverseSectionFrontierRightSpecial_zero
        (K := K) s.rawDefect s.movingSection s.sectionSpecial
  exact {
    rawDefect := 2 * (s.rawDefect - r)
    scale := 2 * s.scale
    scale_pos := Nat.mul_pos (by norm_num) s.scale_pos
    degreeCap := s.degreeCap
    sourceComplexity := s.sourceComplexity
    repair := s.repair
    family := pointedBoundaryShearFamily b P
    movingSection := pointedBoundarySequentialUnshearSection b
    hessianDefect :=
      hessianDefect_pointedBoundaryShearFamily
        (K := K) (2 * (s.rawDefect - r)) b P hfrontDef
    nonlinearDegreeBound :=
      nonlinearDegreeBound_pointedBoundaryShearFamily
        s.degreeCap b P hfrontDegree
    exactCollision :=
      polynomialFamilyExactGradientCollision_pointedBoundaryShear
        P b hfrontCollZero
    sectionSpecial :=
      pointedBoundarySequentialUnshearSection_special_eq_axis b hb0
  }

@[simp]
theorem
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseBoundaryReentryState_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseBoundaryReentryState hbound).rawDefect =
      2 * (s.rawDefect -
        canonicalPositiveTransverseSectionFrontierWeight
          s.rawDefect s.movingSection) := rfl

@[simp]
theorem
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseBoundaryReentryState_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseBoundaryReentryState hbound).scale =
      2 * s.scale := rfl

@[simp]
theorem
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseBoundaryReentryState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    (s.canonicalPositiveTransverseBoundaryReentryState hbound).repair =
      s.repair := rfl

/-- **Successful positive Rees coefficient clearing gives an honest existing
A18 ramified-spend edge.**

The frontier weight is positive, so after the fixed factor-two ramification
the exact clock has strictly decreased from `2*Delta` to `2*(Delta-r)`.  The
canonical section shear changes neither that clock nor the absolute scale. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseBoundaryReentry_certifiedRamifiedSpend
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect)
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    CertifiedRamifiedRawDefectSpend
      (s.canonicalPositiveTransverseBoundaryReentryState hbound) s := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  have hrpos : 0 < r :=
    s.canonicalPositiveTransverseSectionFrontierWeight_pos hpositive
  have hrle : r ≤ s.rawDefect :=
    canonicalPositiveTransverseSectionFrontierWeight_le
      s.rawDefect s.movingSection
  refine {
    ramification := 2
    ramification_pos := by norm_num
    scale_eq := ?_
    raw_lt := ?_
  }
  · rfl
  · change 2 * (s.rawDefect - r) < 2 * s.rawDefect
    omega

/-- **A19.21 source-facing positive-clock adapter.**

There are now only two outcomes before entering already-proved machinery:

* coefficient clearing fails, yielding the concrete A19.17 low Smith layer;
* coefficient clearing succeeds, and after maximal section transport plus the
  canonical determinant-one boundary shear we obtain a certified factor-two
  ramified raw-defect spend from the original state.

Thus the section boundary is not a terminal case and introduces no new
termination mechanism. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseRees_lowLayer_or_ramifiedSpend
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect) :
    Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          s.rawDefect s.family) ∨
      ∃ hbound :
          HasCanonicalPositiveTransverseReesCoefficientBound
            s.rawDefect s.family,
        Nonempty
          (CertifiedRamifiedRawDefectSpend
            (s.canonicalPositiveTransverseBoundaryReentryState hbound) s) := by
  classical
  by_cases hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family
  · right
    exact ⟨hbound,
      ⟨s.canonicalPositiveTransverseBoundaryReentry_certifiedRamifiedSpend
        hpositive hbound⟩⟩
  · left
    exact canonicalPositiveTransverseReesLowLayer_of_not_bound
      hpositive hbound

end

end HC4.Valuation
