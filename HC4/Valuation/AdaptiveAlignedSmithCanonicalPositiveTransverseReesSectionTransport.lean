import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionFrontier
import Mathlib.Tactic

/-!
# A19.20: transport the marked collision to the positive Rees section frontier

A19.19 chooses the largest uniform transverse source weight at which the
ramified moving section is still polynomial.  This file performs no new
exposure geometry: it simply uses the already-proved adaptive diagonal
collision covariance at that maximal weight.

The key source-facing conclusion is exact.  If the maximal section weight is
strictly below the determinant-closing weight `Delta`, then one of the three
transverse coordinates reaches its exact parameter order there.  Its integral
quotient therefore has nonzero constant coefficient.  In other words, an
early stop is literally a section boundary, not a new terminal obstruction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Integral pullback of the ramified zero section at the maximal transverse
section frontier. -/
noncomputable def canonicalPositiveTransverseSectionFrontierLeftSection
    (Delta : ℕ) (b : Fin 4 → Polynomial K) : Fin 4 → Polynomial K := by
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  let W := canonicalPositiveTransverseReesWeight r
  let hdiv := canonicalPositiveTransverseSectionFrontier_zero_hasIntegralSection
    (K := K) Delta b
  exact integralAdaptiveSmithSection W
    (parameterRamificationSection
      (K := K) 2 (zeroPolynomialSection (K := K))) hdiv

/-- Integral pullback of the ramified moving section at the same frontier. -/
noncomputable def canonicalPositiveTransverseSectionFrontierRightSection
    (Delta : ℕ) (b : Fin 4 → Polynomial K) : Fin 4 → Polynomial K := by
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  let W := canonicalPositiveTransverseReesWeight r
  let hdiv := canonicalPositiveTransverseSectionFrontier_hasIntegralSection
    (K := K) Delta b
  exact integralAdaptiveSmithSection W
    (parameterRamificationSection (K := K) 2 b) hdiv

/-- The pulled-back left section is still literally zero. -/
theorem canonicalPositiveTransverseSectionFrontierLeftSection_eq_zero
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    canonicalPositiveTransverseSectionFrontierLeftSection
        (K := K) Delta b =
      zeroPolynomialSection (K := K) := by
  funext i
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  let W := canonicalPositiveTransverseReesWeight r
  let aram := parameterRamificationSection
    (K := K) 2 (zeroPolynomialSection (K := K))
  let hdiv := canonicalPositiveTransverseSectionFrontier_zero_hasIntegralSection
    (K := K) Delta b
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq W aram hdiv) i
  have hramzero : aram i = 0 := by
    simp [aram, parameterRamificationSection, zeroPolynomialSection]
  have heq :
      Polynomial.X ^ W i *
          integralAdaptiveSmithSection W aram hdiv i =
        Polynomial.X ^ W i * 0 := by
    simpa [adaptiveSmithInflateSection, hramzero] using hreinflate
  have hcancel := polynomial_X_pow_mul_cancel (K := K) (W i) heq
  simpa [canonicalPositiveTransverseSectionFrontierLeftSection,
    r, W, aram, hdiv, zeroPolynomialSection] using hcancel

/-- The longitudinal coordinate of the transported right special point remains
exactly `1`, independently of how large the transverse frontier weight is. -/
theorem canonicalPositiveTransverseSectionFrontierRightSpecial_zero
    (Delta : ℕ)
    (b : Fin 4 → Polynomial K)
    (hspecial :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) Delta b) (0 : Fin 4) = 1 := by
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  let W := canonicalPositiveTransverseReesWeight r
  let bram := parameterRamificationSection (K := K) 2 b
  let hdiv := canonicalPositiveTransverseSectionFrontier_hasIntegralSection
    (K := K) Delta b
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq W bram hdiv) (0 : Fin 4)
  have hW0 : W (0 : Fin 4) = 0 := by
    simp [W, canonicalPositiveTransverseReesWeight]
  have hsection :
      integralAdaptiveSmithSection W bram hdiv (0 : Fin 4) =
        bram (0 : Fin 4) := by
    simpa [adaptiveSmithInflateSection, hW0] using hreinflate
  change Polynomial.constantCoeff
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) Delta b (0 : Fin 4)) = 1
  rw [show canonicalPositiveTransverseSectionFrontierRightSection
      (K := K) Delta b (0 : Fin 4) =
        integralAdaptiveSmithSection W bram hdiv (0 : Fin 4) by
      rfl]
  rw [hsection]
  unfold bram parameterRamificationSection
  rw [constantCoeff_parameterRamificationHom (K := K) 2 (by norm_num)]
  have h0 := congrFun hspecial (0 : Fin 4)
  simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using h0

/-- The exact zero-left moving gradient collision survives the maximal
section-frontier exposure. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontier_exactCollision
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        s.rawDefect s.family) :
    HasPolynomialFamilyExactGradientCollision
      (canonicalPositiveTransverseSectionFrontierFamily
        s.rawDefect s.family hbound s.movingSection)
      (canonicalPositiveTransverseSectionFrontierLeftSection
        (K := K) s.rawDefect s.movingSection)
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) s.rawDefect s.movingSection) := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  have hr : r ≤ s.rawDefect :=
    canonicalPositiveTransverseSectionFrontierWeight_le
      s.rawDefect s.movingSection
  let hbnd := hbound.mono hr
  let W := canonicalPositiveTransverseReesWeight r
  let aram := parameterRamificationSection
    (K := K) 2 (zeroPolynomialSection (K := K))
  let bram := parameterRamificationSection (K := K) 2 s.movingSection
  let ha := canonicalPositiveTransverseSectionFrontier_zero_hasIntegralSection
    (K := K) s.rawDefect s.movingSection
  let hb := canonicalPositiveTransverseSectionFrontier_hasIntegralSection
    (K := K) s.rawDefect s.movingSection
  have hram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      2 s.family (zeroPolynomialSection (K := K)) s.movingSection
      s.exactCollision
  have hout :=
    polynomialFamilyExactGradientCollision_adaptiveSmithExposure
      2 W (2 * r) (by norm_num)
      s.family hbnd.integralExposure aram bram ha hb hram
  simpa [canonicalPositiveTransverseSectionFrontierFamily,
    canonicalPositiveTransverseReesFamily,
    canonicalPositiveTransverseSectionFrontierLeftSection,
    canonicalPositiveTransverseSectionFrontierRightSection,
    r, W, aram, bram, ha, hb, hbnd, hr] using hout

/-- A lightweight source-facing certificate for a transverse section boundary
created by the positive Rees transport.  The existing determinant-one
three-shear machinery consumes precisely this noncanonical special point. -/
structure CanonicalPositiveTransverseSectionFrontierBoundary
    (Delta : ℕ) (b : Fin 4 → Polynomial K) : Type where
  coordinate : Fin 4
  coordinate_ne_zero : coordinate ≠ (0 : Fin 4)
  special_ne_zero :
    polynomialSectionSpecialPoint
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) Delta b) coordinate ≠ 0

/-- Elementary arithmetic for the minimum of three natural numbers. -/
theorem min_three_eq_one_or_two_or_three
    (a b c : ℕ) :
    min a (min b c) = a ∨
      min a (min b c) = b ∨
      min a (min b c) = c := by
  by_cases ha : a ≤ min b c
  · exact Or.inl (min_eq_left ha)
  · have hrest : min b c ≤ a := by omega
    have hout : min a (min b c) = min b c := min_eq_right hrest
    by_cases hb : b ≤ c
    · right; left
      rw [hout, min_eq_left hb]
    · right; right
      have hc : c ≤ b := by omega
      rw [hout, min_eq_right hc]

/-- The maximal frontier weight is attained by at least one of the three
transverse coordinate caps. -/
theorem canonicalPositiveTransverseSectionFrontierWeight_eq_cap
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    canonicalPositiveTransverseSectionFrontierWeight Delta b =
        canonicalPositiveTransverseSectionOrderCap Delta
          (parameterRamificationSection (K := K) 2 b (1 : Fin 4)) ∨
      canonicalPositiveTransverseSectionFrontierWeight Delta b =
        canonicalPositiveTransverseSectionOrderCap Delta
          (parameterRamificationSection (K := K) 2 b (2 : Fin 4)) ∨
      canonicalPositiveTransverseSectionFrontierWeight Delta b =
        canonicalPositiveTransverseSectionOrderCap Delta
          (parameterRamificationSection (K := K) 2 b (3 : Fin 4)) := by
  simpa [canonicalPositiveTransverseSectionFrontierWeight] using
    min_three_eq_one_or_two_or_three
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (1 : Fin 4)))
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (2 : Fin 4)))
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (3 : Fin 4)))

/-- If one coordinate cap is the maximal common frontier and that frontier is
strictly early, the transported coordinate has nonzero special value. -/
theorem canonicalPositiveTransverseSectionFrontierRightSpecial_ne_zero_of_cap_eq_of_lt
    (Delta : ℕ) (b : Fin 4 → Polynomial K)
    (i : Fin 4) (hi : i ≠ (0 : Fin 4))
    (hcap :
      canonicalPositiveTransverseSectionFrontierWeight Delta b =
        canonicalPositiveTransverseSectionOrderCap Delta
          (parameterRamificationSection (K := K) 2 b i))
    (hlt : canonicalPositiveTransverseSectionFrontierWeight Delta b < Delta) :
    polynomialSectionSpecialPoint
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) Delta b) i ≠ 0 := by
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  let W := canonicalPositiveTransverseReesWeight r
  let bram := parameterRamificationSection (K := K) 2 b
  let hdiv := canonicalPositiveTransverseSectionFrontier_hasIntegralSection
    (K := K) Delta b
  have hcaplt :
      canonicalPositiveTransverseSectionOrderCap Delta (bram i) < Delta := by
    rw [← hcap]
    exact hlt
  rcases canonicalPositiveTransverseSectionOrderCap_exact_of_lt
      (K := K) Delta (bram i) hcaplt with
    ⟨hp, hfactor, hconst⟩
  have hWi : W i = r := by
    simp [W, canonicalPositiveTransverseReesWeight, hi]
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq W bram hdiv) i
  change
    Polynomial.X ^ W i *
        integralAdaptiveSmithSection W bram hdiv i = bram i at hreinflate
  rw [hWi] at hreinflate
  have hcap' :
      canonicalPositiveTransverseSectionOrderCap Delta (bram i) = r := by
    simpa [r, bram] using hcap.symm
  have hfactor' :
      bram i = Polynomial.X ^ r *
        polynomialParameterPrimitivePart (bram i) hp := by
    calc
      bram i =
          Polynomial.X ^ canonicalPositiveTransverseSectionOrderCap Delta (bram i) *
            polynomialParameterPrimitivePart (bram i) hp := hfactor
      _ = Polynomial.X ^ r *
            polynomialParameterPrimitivePart (bram i) hp := by
          rw [hcap']
  rw [hfactor'] at hreinflate
  have hcancel := polynomial_X_pow_mul_cancel (K := K) r hreinflate
  change Polynomial.constantCoeff
      (canonicalPositiveTransverseSectionFrontierRightSection
        (K := K) Delta b i) ≠ 0
  rw [show canonicalPositiveTransverseSectionFrontierRightSection
      (K := K) Delta b i = integralAdaptiveSmithSection W bram hdiv i by
      rfl]
  rw [hcancel]
  exact hconst

/-- **Early maximal section transport is exactly a transverse boundary.** -/
theorem canonicalPositiveTransverseSectionFrontier_boundary_of_lt
    (Delta : ℕ) (b : Fin 4 → Polynomial K)
    (hlt : canonicalPositiveTransverseSectionFrontierWeight Delta b < Delta) :
    Nonempty
      (CanonicalPositiveTransverseSectionFrontierBoundary
        (K := K) Delta b) := by
  rcases canonicalPositiveTransverseSectionFrontierWeight_eq_cap
      (K := K) Delta b with h1 | h2 | h3
  · exact ⟨{
      coordinate := (1 : Fin 4)
      coordinate_ne_zero := by decide
      special_ne_zero :=
        canonicalPositiveTransverseSectionFrontierRightSpecial_ne_zero_of_cap_eq_of_lt
          (K := K) Delta b (1 : Fin 4) (by decide) h1 hlt
    }⟩
  · exact ⟨{
      coordinate := (2 : Fin 4)
      coordinate_ne_zero := by decide
      special_ne_zero :=
        canonicalPositiveTransverseSectionFrontierRightSpecial_ne_zero_of_cap_eq_of_lt
          (K := K) Delta b (2 : Fin 4) (by decide) h2 hlt
    }⟩
  · exact ⟨{
      coordinate := (3 : Fin 4)
      coordinate_ne_zero := by decide
      special_ne_zero :=
        canonicalPositiveTransverseSectionFrontierRightSpecial_ne_zero_of_cap_eq_of_lt
          (K := K) Delta b (3 : Fin 4) (by decide) h3 hlt
    }⟩

/-- At any frontier, the transported marked point is either still canonical or
is an actual transverse section boundary. -/
theorem ScaleAwareAdaptiveGeometricRestartState.canonicalPositiveTransverseSectionFrontier_canonical_or_boundary
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    polynomialSectionSpecialPoint
        (canonicalPositiveTransverseSectionFrontierRightSection
          (K := K) s.rawDefect s.movingSection) =
      coordinateAxisPoint (K := K) (0 : Fin 4) ∨
    Nonempty
      (CanonicalPositiveTransverseSectionFrontierBoundary
        (K := K) s.rawDefect s.movingSection) := by
  classical
  by_cases hspecial :
      polynomialSectionSpecialPoint
          (canonicalPositiveTransverseSectionFrontierRightSection
            (K := K) s.rawDefect s.movingSection) =
        coordinateAxisPoint (K := K) (0 : Fin 4)
  · exact Or.inl hspecial
  · right
    have hex :
        ∃ i : Fin 4, i ≠ (0 : Fin 4) ∧
          polynomialSectionSpecialPoint
            (canonicalPositiveTransverseSectionFrontierRightSection
              (K := K) s.rawDefect s.movingSection) i ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hspecial
      funext i
      by_cases hi : i = (0 : Fin 4)
      · subst i
        simpa [coordinateAxisPoint] using
          canonicalPositiveTransverseSectionFrontierRightSpecial_zero
            (K := K) s.rawDefect s.movingSection s.sectionSpecial
      · have hz := hnone i hi
        simpa [coordinateAxisPoint, hi] using hz
    rcases hex with ⟨i, hi, hne⟩
    exact ⟨{
      coordinate := i
      coordinate_ne_zero := hi
      special_ne_zero := hne
    }⟩

end

end HC4.Valuation