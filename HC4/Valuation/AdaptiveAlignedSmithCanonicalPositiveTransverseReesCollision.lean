import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectReentry
import HC4.MongeAmpere
import Mathlib.Tactic

/-!
# A19.18: collision transport through the determinant-closing Rees transform

A19.17 constructs a canonical positive-clock transverse Rees family with raw
Hessian defect zero whenever the coefficientwise exposure is integral.  To be
useful for the JC2-facing endgame we must retain the actual marked collision,
not merely the determinant clock.

For raw clock `Delta <= 2` this transport is automatic.  The canonical marked
right section specializes to `e0`, so every transverse coordinate vanishes at
the parameter origin.  After parameter ramification by `2`, one factor of the
parameter covers every transverse source weight `Delta <= 2`.  The standard
adaptive-exposure covariance theorem therefore transports the exact family
collision through the same determinant-closing Rees transform.

The longitudinal source weight is zero.  Hence the transformed left special
point still has longitudinal coordinate `0`, while the transformed right
special point still has longitudinal coordinate `1`; the collision remains
distinct even if a transverse section boundary appears.

Specializing the raw-zero exposed family gives an honest polynomial
Monge--Ampere solution with that distinct exact gradient collision.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- At clock at most two, the fixed ramification `R = 2` covers every source
weight of the determinant-closing transverse Rees transform. -/
theorem canonicalPositiveTransverseReesWeight_covered_of_le_two
    {Delta : ℕ}
    (hDelta : Delta ≤ 2) :
    ∀ i : Fin 4, canonicalPositiveTransverseReesWeight Delta i ≤ 2 := by
  intro i
  fin_cases i <;>
    simp [canonicalPositiveTransverseReesWeight] <;> omega

/-- The zero marked section satisfies the source-integrality side condition
for the determinant-closing Rees weight. -/
theorem zeroSection_canonicalPositiveTransverseRees_special
    (Delta : ℕ) :
    ∀ i : Fin 4,
      canonicalPositiveTransverseReesWeight Delta i = 0 ∨
        Polynomial.constantCoeff ((zeroPolynomialSection (K := K)) i) = 0 := by
  intro i
  exact Or.inr (by simp [zeroPolynomialSection])

/-- The canonical right marked section satisfies the same vanishing condition:
coordinate zero has source weight zero, while every transverse coordinate has
zero constant coefficient because the special point is `e0`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.movingSection_canonicalPositiveTransverseRees_special
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    ∀ i : Fin 4,
      canonicalPositiveTransverseReesWeight s.rawDefect i = 0 ∨
        Polynomial.constantCoeff (s.movingSection i) = 0 := by
  intro i
  by_cases hi : i = (0 : Fin 4)
  · left
    subst i
    simp [canonicalPositiveTransverseReesWeight]
  · right
    have h := congrFun s.sectionSpecial i
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using h

/-- The determinant-closing Rees exposure retains the exact family collision
at every positive clock at most two. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseRees_exactCollision_of_le_two
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hclock : s.rawDefect ≤ 2)
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    let W := canonicalPositiveTransverseReesWeight s.rawDefect
    let ha := parameterRamificationSection_hasIntegralAdaptiveSmithSection
      (K := K) 2 W
      (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
      (zeroPolynomialSection (K := K))
      (zeroSection_canonicalPositiveTransverseRees_special s.rawDefect)
    let hb := parameterRamificationSection_hasIntegralAdaptiveSmithSection
      (K := K) 2 W
      (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
      s.movingSection
      s.movingSection_canonicalPositiveTransverseRees_special
    HasPolynomialFamilyExactGradientCollision
      (canonicalPositiveTransverseReesFamily s.rawDefect s.family hbound)
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) 2
          (zeroPolynomialSection (K := K))) ha)
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) 2 s.movingSection) hb) := by
  dsimp
  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        s.family (zeroPolynomialSection (K := K)) s.movingSection := by
    simpa [zeroPolynomialSection] using s.exactCollision
  simpa [canonicalPositiveTransverseReesFamily] using
    (polynomialFamilyExactGradientCollision_ramifiedAdaptiveSmithExposure
      2 (canonicalPositiveTransverseReesWeight s.rawDefect)
      (2 * s.rawDefect) (by norm_num)
      s.family hbound.integralExposure
      (zeroPolynomialSection (K := K)) s.movingSection
      (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
      (zeroSection_canonicalPositiveTransverseRees_special s.rawDefect)
      s.movingSection_canonicalPositiveTransverseRees_special hcoll)

/-- Coordinate zero of the pulled-back left special point remains zero. -/
theorem canonicalPositiveTransverseRees_leftSpecial_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hclock : s.rawDefect ≤ 2) :
    let W := canonicalPositiveTransverseReesWeight s.rawDefect
    let ha := parameterRamificationSection_hasIntegralAdaptiveSmithSection
      (K := K) 2 W
      (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
      (zeroPolynomialSection (K := K))
      (zeroSection_canonicalPositiveTransverseRees_special s.rawDefect)
    polynomialSectionSpecialPoint
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) 2
          (zeroPolynomialSection (K := K))) ha) (0 : Fin 4) = 0 := by
  dsimp
  let W := canonicalPositiveTransverseReesWeight s.rawDefect
  let a := parameterRamificationSection
    (K := K) 2 (zeroPolynomialSection (K := K))
  let ha := parameterRamificationSection_hasIntegralAdaptiveSmithSection
    (K := K) 2 W
    (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
    (zeroPolynomialSection (K := K))
    (zeroSection_canonicalPositiveTransverseRees_special s.rawDefect)
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq W a ha) (0 : Fin 4)
  have hW0 : W (0 : Fin 4) = 0 := by
    simp [W, canonicalPositiveTransverseReesWeight]
  have hsection :
      integralAdaptiveSmithSection W a ha (0 : Fin 4) = a (0 : Fin 4) := by
    simpa [adaptiveSmithInflateSection, hW0] using hreinflate
  unfold polynomialSectionSpecialPoint
  rw [hsection]
  simp [a, parameterRamificationSection, zeroPolynomialSection]

/-- Coordinate zero of the pulled-back right special point remains one. -/
theorem canonicalPositiveTransverseRees_rightSpecial_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hclock : s.rawDefect ≤ 2) :
    let W := canonicalPositiveTransverseReesWeight s.rawDefect
    let hb := parameterRamificationSection_hasIntegralAdaptiveSmithSection
      (K := K) 2 W
      (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
      s.movingSection
      s.movingSection_canonicalPositiveTransverseRees_special
    polynomialSectionSpecialPoint
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) 2 s.movingSection) hb)
      (0 : Fin 4) = 1 := by
  dsimp
  let W := canonicalPositiveTransverseReesWeight s.rawDefect
  let b := parameterRamificationSection (K := K) 2 s.movingSection
  let hb := parameterRamificationSection_hasIntegralAdaptiveSmithSection
    (K := K) 2 W
    (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
    s.movingSection
    s.movingSection_canonicalPositiveTransverseRees_special
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq W b hb) (0 : Fin 4)
  have hW0 : W (0 : Fin 4) = 0 := by
    simp [W, canonicalPositiveTransverseReesWeight]
  have hsection :
      integralAdaptiveSmithSection W b hb (0 : Fin 4) = b (0 : Fin 4) := by
    simpa [adaptiveSmithInflateSection, hW0] using hreinflate
  unfold polynomialSectionSpecialPoint
  rw [hsection]
  unfold b parameterRamificationSection
  rw [constantCoeff_parameterRamificationHom (K := K) 2 (by norm_num)]
  have h := congrFun s.sectionSpecial (0 : Fin 4)
  simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using h

/-- **A19.18 — low positive clocks produce an honest Monge--Ampere
counterexample fibre unless A19.17 has already exposed a low coefficient
layer.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseRees_mongeAmpereCollision_of_le_two
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect)
    (hclock : s.rawDefect ≤ 2)
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    ∃ p q : Fin 4 → K,
      p ≠ q ∧
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (polynomialFamilySpecialFiber
          (canonicalPositiveTransverseReesFamily
            s.rawDefect s.family hbound)) ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber
          (canonicalPositiveTransverseReesFamily
            s.rawDefect s.family hbound)) p q := by
  let W := canonicalPositiveTransverseReesWeight s.rawDefect
  let ha := parameterRamificationSection_hasIntegralAdaptiveSmithSection
    (K := K) 2 W
    (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
    (zeroPolynomialSection (K := K))
    (zeroSection_canonicalPositiveTransverseRees_special s.rawDefect)
  let hb := parameterRamificationSection_hasIntegralAdaptiveSmithSection
    (K := K) 2 W
    (canonicalPositiveTransverseReesWeight_covered_of_le_two hclock)
    s.movingSection
    s.movingSection_canonicalPositiveTransverseRees_special
  let a' := integralAdaptiveSmithSection W
    (parameterRamificationSection (K := K) 2
      (zeroPolynomialSection (K := K))) ha
  let b' := integralAdaptiveSmithSection W
    (parameterRamificationSection (K := K) 2 s.movingSection) hb
  let p := polynomialSectionSpecialPoint a'
  let q := polynomialSectionSpecialPoint b'
  refine ⟨p, q, ?_, ?_, ?_⟩
  · intro hpq
    have h0 := congrFun hpq (0 : Fin 4)
    have ha0 : p (0 : Fin 4) = 0 := by
      simpa [p, a', W, ha] using
        canonicalPositiveTransverseRees_leftSpecial_zero s hclock
    have hb0 : q (0 : Fin 4) = 1 := by
      simpa [q, b', W, hb] using
        canonicalPositiveTransverseRees_rightSpecial_zero s hclock
    rw [ha0, hb0] at h0
    exact zero_ne_one h0
  · unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
    rw [hessianDeterminant_polynomialFamilySpecialFiber]
    have hdef := canonicalPositiveTransverseReesFamily_hessianDefect_zero
      hpositive s.hessianDefect hbound
    unfold HasPolynomialFamilyHessianDefect at hdef
    rw [hdef]
    simp
  · have hfamily :=
      s.canonicalPositiveTransverseRees_exactCollision_of_le_two hclock hbound
    exact polynomialFamilyExactGradientCollision_specialFiber
      (canonicalPositiveTransverseReesFamily s.rawDefect s.family hbound)
      a' b' (by simpa [a', b', W, ha, hb] using hfamily)

end

end HC4.Valuation
