import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionParity
import HC4.Valuation.AdaptiveAlignedSmithExposureGeometry
import Mathlib.Tactic

/-!
# A19.30: remove the factor-two cover from an early positive Rees frontier

A19.29 proves that every strict early section-frontier weight `r` is even.
Write `r = 2s`.  The coefficient inequality at weight `r`

    2r <= 2q + r * deg_transverse

then divides exactly by two to

    r <= q + s * deg_transverse.

This is precisely the coefficientwise integrality condition for the *original*
parameter, with ramification index one, transverse source weight `(0,s,s,s)`,
and common divided level `r`.

The same parity statement removes the factor-two cover from the moving
section.  Consequently an early A19 frontier is already an honest integral
source exposure at the represented scale.  Its Hessian clock is literally
`Delta - r`.

No recursive progress is asserted here: the next adapter still has to consume
the resulting source geometry against the retained terminal provenance.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Once `r = 2s`, the A19 coefficient bound at weight `r` is exactly enough
for an unramified adaptive Smith exposure with transverse weight `s` and
common level `r`. -/
theorem canonicalPositiveTransverseRees_half_integralExposure
    {Delta r s : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound Delta P)
    (hrDelta : r ≤ Delta)
    (hrs : r = 2 * s) :
    HasIntegralAdaptiveSmithExposure
      1 (canonicalPositiveTransverseReesWeight s) r P := by
  have hrbound := hbound.mono hrDelta
  intro d hd
  let q := smithFamilyCoefficientOrder P d
  let n := canonicalTransverseDegree d
  have hineq := hrbound d hd
  rw [canonicalPositiveTransverseReesWeight_finsupp] at hineq
  have hhalf :
      r ≤ q + Finsupp.weight
        (canonicalPositiveTransverseReesWeight s) d := by
    rw [canonicalPositiveTransverseReesWeight_finsupp]
    dsimp [q, n] at hineq ⊢
    rw [hrs] at hineq ⊢
    omega
  have hqdiv : Polynomial.X ^ q ∣ MvPolynomial.coeff d P :=
    smithFamilyCoefficientOrder_dvd P hd
  have hramdiv :
      Polynomial.X ^ (1 * q) ∣
        parameterRamificationHom (K := K) 1 (MvPolynomial.coeff d P) :=
    parameterRamification_pow_dvd 1 q _ hqdiv
  rcases hramdiv with ⟨a, ha⟩
  refine ⟨Polynomial.X ^
      (q + Finsupp.weight (canonicalPositiveTransverseReesWeight s) d - r) * a,
    ?_⟩
  unfold adaptiveSmithExposureCoefficientFactor
  rw [ha]
  have hexp :
      r +
          (q + Finsupp.weight (canonicalPositiveTransverseReesWeight s) d - r) =
        Finsupp.weight (canonicalPositiveTransverseReesWeight s) d + 1 * q := by
    omega
  calc
    Polynomial.X ^ Finsupp.weight (canonicalPositiveTransverseReesWeight s) d *
          (Polynomial.X ^ (1 * q) * a) =
        Polynomial.X ^
            (Finsupp.weight (canonicalPositiveTransverseReesWeight s) d + 1 * q) * a := by
          rw [← mul_assoc, ← pow_add]
    _ = Polynomial.X ^ r *
          (Polynomial.X ^
            (q + Finsupp.weight (canonicalPositiveTransverseReesWeight s) d - r) * a) := by
          rw [← mul_assoc, ← pow_add, hexp]

/-- If the factor-two frontier has weight `2s`, then the *original* moving
section is already divisible by `X^s` in every transverse coordinate. -/
theorem canonicalPositiveTransverseRees_half_hasIntegralSection
    (Delta s : ℕ)
    (b : Fin 4 → Polynomial K)
    (hrs : canonicalPositiveTransverseSectionFrontierWeight Delta b = 2 * s) :
    HasIntegralAdaptiveSmithSection
      (canonicalPositiveTransverseReesWeight s) b := by
  classical
  have hcoord :
      ∀ i : Fin 4, i ≠ (0 : Fin 4) →
        canonicalPositiveTransverseSectionFrontierWeight Delta b ≤
          canonicalPositiveTransverseSectionOrderCap Delta
            (parameterRamificationSection (K := K) 2 b i) →
        Polynomial.X ^ s ∣ b i := by
    intro i hi hfrontLe
    by_cases hbi : b i = 0
    · simp [hbi]
    · let p := parameterRamificationSection (K := K) 2 b i
      have hp : p ≠ 0 := by
        dsimp [p, parameterRamificationSection]
        exact parameterRamificationHom_ne_zero_of_pos 2 (by norm_num) hbi
      have hcapDvd :=
        canonicalPositiveTransverseSectionOrderCap_dvd (K := K) Delta p
      have hfrontPow :
          Polynomial.X ^ canonicalPositiveTransverseSectionFrontierWeight Delta b ∣
            Polynomial.X ^ canonicalPositiveTransverseSectionOrderCap Delta p :=
        polynomial_X_pow_dvd_X_pow_of_le (K := K) _ _ hfrontLe
      have hfrontDvd :
          Polynomial.X ^ canonicalPositiveTransverseSectionFrontierWeight Delta b ∣ p :=
        dvd_trans hfrontPow hcapDvd
      have horderLe :
          canonicalPositiveTransverseSectionFrontierWeight Delta b ≤
            polynomialParameterOrder p hp :=
        polynomial_X_pow_dvd_le_parameterOrder p hp _ hfrontDvd
      have horderRam :
          polynomialParameterOrder p hp =
            2 * polynomialParameterOrder (b i) hbi := by
        simpa [p, parameterRamificationSection] using
          polynomialParameterOrder_parameterRamificationHom_eq
            (K := K) 2 (by norm_num) (b i) hbi
      have hsLe : s ≤ polynomialParameterOrder (b i) hbi := by
        rw [hrs, horderRam] at horderLe
        omega
      have hprimitive := polynomialParameterPrimitivePart_spec (b i) hbi
      have hqDvd :
          Polynomial.X ^ polynomialParameterOrder (b i) hbi ∣ b i :=
        ⟨polynomialParameterPrimitivePart (b i) hbi, hprimitive⟩
      exact dvd_trans
        (polynomial_X_pow_dvd_X_pow_of_le
          (K := K) s (polynomialParameterOrder (b i) hbi) hsLe)
        hqDvd
  intro i
  fin_cases i
  · simp [canonicalPositiveTransverseReesWeight]
  · simpa [canonicalPositiveTransverseReesWeight] using
      hcoord (1 : Fin 4) (by decide)
        (canonicalPositiveTransverseSectionFrontierWeight_le_one
          (K := K) Delta b)
  · simpa [canonicalPositiveTransverseReesWeight] using
      hcoord (2 : Fin 4) (by decide)
        (canonicalPositiveTransverseSectionFrontierWeight_le_two
          (K := K) Delta b)
  · simpa [canonicalPositiveTransverseReesWeight] using
      hcoord (3 : Fin 4) (by decide)
        (canonicalPositiveTransverseSectionFrontierWeight_le_three
          (K := K) Delta b)

/-- The zero section is integrally transportable through the same unramified
half-frontier weight. -/
theorem canonicalPositiveTransverseRees_half_zero_hasIntegralSection
    (s : ℕ) :
    HasIntegralAdaptiveSmithSection
      (canonicalPositiveTransverseReesWeight s)
      (zeroPolynomialSection (K := K)) := by
  intro i
  simp [zeroPolynomialSection]

/-- **Unramified early-frontier Hessian clock.**

At an early even A19 frontier `r = 2s`, the represented family admits an
honest ramification-one exposure at the same parameter scale whose exact
Hessian defect is `Delta - r`. -/
theorem canonicalPositiveTransverseRees_unramifiedFrontier_hessianDefect
    {Delta r s : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound Delta P)
    (hrDelta : r ≤ Delta)
    (hrs : r = 2 * s) :
    let hint := canonicalPositiveTransverseRees_half_integralExposure
      (K := K) hbound hrDelta hrs
    HasPolynomialFamilyHessianDefect (K := K)
      (adaptiveSmithExposureFamily
        1 (canonicalPositiveTransverseReesWeight s) r P hint)
      (Delta - r) := by
  dsimp
  let hint := canonicalPositiveTransverseRees_half_integralExposure
    (K := K) hbound hrDelta hrs
  have hnonneg :
      4 * r ≤
        1 * Delta +
          2 * ∑ i : Fin 4, canonicalPositiveTransverseReesWeight s i := by
    rw [canonicalPositiveTransverseReesWeight_sum]
    omega
  have hout :=
    adaptiveSmithFirstContactExposureFamily_hasHessianDefect
      1 (canonicalPositiveTransverseReesWeight s) r Delta
      (by norm_num) hnonneg P hint hdef
  have hclock :
      1 * Delta +
          2 * ∑ i : Fin 4, canonicalPositiveTransverseReesWeight s i -
            4 * r = Delta - r := by
    rw [canonicalPositiveTransverseReesWeight_sum]
    omega
  rw [← hclock]
  exact hout

/-- Every strict early A19 frontier therefore admits a concrete half-weight
` s ` at the represented scale, with coefficient and moving-section
integrality and exact raw clock `Delta - r`. -/
theorem exists_canonicalPositiveTransverseRees_unramifiedFrontier
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound Delta P)
    (b : Fin 4 → Polynomial K)
    (hlt : canonicalPositiveTransverseSectionFrontierWeight Delta b < Delta) :
    ∃ s : ℕ,
      canonicalPositiveTransverseSectionFrontierWeight Delta b = 2 * s ∧
      ∃ hint : HasIntegralAdaptiveSmithExposure
          1 (canonicalPositiveTransverseReesWeight s)
          (canonicalPositiveTransverseSectionFrontierWeight Delta b) P,
        HasIntegralAdaptiveSmithSection
            (canonicalPositiveTransverseReesWeight s) b ∧
          HasPolynomialFamilyHessianDefect (K := K)
            (adaptiveSmithExposureFamily
              1 (canonicalPositiveTransverseReesWeight s)
              (canonicalPositiveTransverseSectionFrontierWeight Delta b) P hint)
            (Delta - canonicalPositiveTransverseSectionFrontierWeight Delta b) := by
  rcases canonicalPositiveTransverseSectionFrontierWeight_even_of_lt
      (K := K) Delta b hlt with ⟨s, hs⟩
  have hrs : canonicalPositiveTransverseSectionFrontierWeight Delta b = 2 * s := by
    omega
  let hint := canonicalPositiveTransverseRees_half_integralExposure
    (K := K) hbound (Nat.le_of_lt hlt) hrs
  have hsection := canonicalPositiveTransverseRees_half_hasIntegralSection
    (K := K) Delta s b hrs
  have hdef' := canonicalPositiveTransverseRees_unramifiedFrontier_hessianDefect
    (K := K) P hdef hbound (Nat.le_of_lt hlt) hrs
  refine ⟨s, hrs, hint, hsection, ?_⟩
  simpa [hint] using hdef'

end

end HC4.Valuation