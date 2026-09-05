import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesCollision
import HC4.Valuation.AdaptiveSectionBoundaryReentry
import Mathlib.Tactic

/-!
# A19.19: section frontier for the positive transverse Rees transform

A19.17 proves coefficientwise integrality of the determinant-closing
transverse Rees family unless a concrete low Smith layer appears.  The marked
moving section is a separate source-facing issue: at large positive clock the
fixed ramification by two need not cover the full transverse weight.

The correct finite adapter is to move along the same uniform transverse Rees
ray only as far as the marked section is integrally transportable.  The family
coefficient bound is downward closed along this ray.  For a section coordinate
we cap its exact ramified parameter order by the target clock; this cap is the
largest uniform source weight that coordinate can absorb.  The minimum of the
three transverse caps is therefore the first section-contact weight.

No new geometric or termination mechanism is introduced here.  The exposed
family is still the existing adaptive Smith exposure, and any transverse
special-point boundary is consumed later by the already-green canonical
three-shear re-entry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Clearing the canonical positive transverse Rees family at weight `Delta`
clears it at every smaller uniform transverse weight `r`. -/
theorem HasCanonicalPositiveTransverseReesCoefficientBound.mono
    {r Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (h : HasCanonicalPositiveTransverseReesCoefficientBound Delta P)
    (hr : r ≤ Delta) :
    HasCanonicalPositiveTransverseReesCoefficientBound r P := by
  intro d hd
  have hDelta := h d hd
  rw [canonicalPositiveTransverseReesWeight_finsupp] at hDelta ⊢
  let q := smithFamilyCoefficientOrder P d
  let n := canonicalTransverseDegree d
  have hDelta' : 2 * Delta ≤ 2 * q + Delta * n := by
    simpa [q, n] using hDelta
  have htarget : 2 * r ≤ 2 * q + r * n := by
    by_cases hn0 : n = 0
    · rw [hn0] at hDelta' ⊢
      simp at hDelta' ⊢
      omega
    by_cases hn1 : n = 1
    · rw [hn1] at hDelta' ⊢
      simp at hDelta' ⊢
      omega
    · have hn2 : 2 ≤ n := by omega
      have hmul : 2 * r ≤ r * n := by
        have hm := Nat.mul_le_mul_left r hn2
        simpa [Nat.mul_comm] using hm
      omega
  simpa [q, n] using htarget

/-- For one ramified section coordinate, cap its exact parameter order by the
full determinant-closing transverse weight.  A zero coordinate has infinite
usable order for this finite problem, represented by the cap itself. -/
noncomputable def canonicalPositiveTransverseSectionOrderCap
    (Delta : ℕ) (p : Polynomial K) : ℕ := by
  classical
  exact if hp : p = 0 then Delta
    else min Delta (polynomialParameterOrder p hp)

/-- A section-order cap never exceeds the requested determinant-closing
weight. -/
theorem canonicalPositiveTransverseSectionOrderCap_le
    (Delta : ℕ) (p : Polynomial K) :
    canonicalPositiveTransverseSectionOrderCap Delta p ≤ Delta := by
  classical
  by_cases hp : p = 0
  · simp [canonicalPositiveTransverseSectionOrderCap, hp]
  · simp [canonicalPositiveTransverseSectionOrderCap, hp]

/-- The ramified section coordinate is divisible by the source weight given by
its capped exact order. -/
theorem canonicalPositiveTransverseSectionOrderCap_dvd
    (Delta : ℕ) (p : Polynomial K) :
    Polynomial.X ^ canonicalPositiveTransverseSectionOrderCap Delta p ∣ p := by
  classical
  by_cases hp : p = 0
  · subst p
    simp [canonicalPositiveTransverseSectionOrderCap]
  · let q := polynomialParameterOrder p hp
    let u := polynomialParameterPrimitivePart p hp
    have hfactor : p = Polynomial.X ^ q * u := by
      simpa [q, u] using polynomialParameterPrimitivePart_spec p hp
    have hsmall :
        Polynomial.X ^ min Delta q ∣ Polynomial.X ^ q :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) (min Delta q) q (min_le_right _ _)
    have hcap :
        canonicalPositiveTransverseSectionOrderCap Delta p = min Delta q := by
      simp [canonicalPositiveTransverseSectionOrderCap, hp, q]
    rw [hcap]
    exact dvd_trans hsmall ⟨u, hfactor⟩

/-- If the capped order is strictly below the target weight, then it is an
actual finite exact order: after removing precisely that power of `X`, the
remaining primitive quotient has nonzero constant coefficient. -/
theorem canonicalPositiveTransverseSectionOrderCap_exact_of_lt
    (Delta : ℕ) (p : Polynomial K)
    (hlt : canonicalPositiveTransverseSectionOrderCap Delta p < Delta) :
    ∃ hp : p ≠ 0,
      p = Polynomial.X ^ canonicalPositiveTransverseSectionOrderCap Delta p *
          polynomialParameterPrimitivePart p hp ∧
      Polynomial.constantCoeff (polynomialParameterPrimitivePart p hp) ≠ 0 := by
  classical
  by_cases hp : p = 0
  · simp [canonicalPositiveTransverseSectionOrderCap, hp] at hlt
  · let q := polynomialParameterOrder p hp
    have hmin : min Delta q < Delta := by
      simpa [canonicalPositiveTransverseSectionOrderCap, hp, q] using hlt
    have hq : q < Delta := by
      by_contra hnot
      have hDq : Delta ≤ q := by omega
      rw [min_eq_left hDq] at hmin
      exact (Nat.lt_irrefl Delta) hmin
    have hcap0 :
        canonicalPositiveTransverseSectionOrderCap Delta p = min Delta q := by
      simp [canonicalPositiveTransverseSectionOrderCap, hp, q]
    have hminEq : min Delta q = q :=
      min_eq_right (Nat.le_of_lt hq)
    have hcap : canonicalPositiveTransverseSectionOrderCap Delta p = q :=
      hcap0.trans hminEq
    refine ⟨hp, ?_, ?_⟩
    · rw [hcap]
      exact polynomialParameterPrimitivePart_spec p hp
    · exact polynomialParameterPrimitivePart_constantCoeff_ne_zero p hp

/-- The largest uniform transverse weight, capped by `Delta`, which all three
ramified transverse coordinates of the moving section can absorb. -/
noncomputable def canonicalPositiveTransverseSectionFrontierWeight
    (Delta : ℕ) (b : Fin 4 → Polynomial K) : ℕ :=
  min
    (canonicalPositiveTransverseSectionOrderCap Delta
      (parameterRamificationSection (K := K) 2 b (1 : Fin 4)))
    (min
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (2 : Fin 4)))
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (3 : Fin 4))))

/-- The section frontier never passes the determinant-closing weight. -/
theorem canonicalPositiveTransverseSectionFrontierWeight_le
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    canonicalPositiveTransverseSectionFrontierWeight Delta b ≤ Delta := by
  exact le_trans (min_le_left _ _)
    (canonicalPositiveTransverseSectionOrderCap_le Delta _)

/-- Frontier weight is below the first transverse coordinate cap. -/
theorem canonicalPositiveTransverseSectionFrontierWeight_le_one
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    canonicalPositiveTransverseSectionFrontierWeight Delta b ≤
      canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (1 : Fin 4)) := by
  exact min_le_left _ _

/-- Frontier weight is below the second transverse coordinate cap. -/
theorem canonicalPositiveTransverseSectionFrontierWeight_le_two
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    canonicalPositiveTransverseSectionFrontierWeight Delta b ≤
      canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (2 : Fin 4)) := by
  exact le_trans (min_le_right _ _) (min_le_left _ _)

/-- Frontier weight is below the third transverse coordinate cap. -/
theorem canonicalPositiveTransverseSectionFrontierWeight_le_three
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    canonicalPositiveTransverseSectionFrontierWeight Delta b ≤
      canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (3 : Fin 4)) := by
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- At the maximal common section weight the ramified moving section is
literally integrally pullable through the uniform transverse source diagonal.
No ramification-cover inequality is assumed. -/
theorem canonicalPositiveTransverseSectionFrontier_hasIntegralSection
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
    HasIntegralAdaptiveSmithSection
      (canonicalPositiveTransverseReesWeight r)
      (parameterRamificationSection (K := K) 2 b) := by
  classical
  dsimp
  intro i
  fin_cases i
  · simp [canonicalPositiveTransverseReesWeight]
  · have hle := canonicalPositiveTransverseSectionFrontierWeight_le_one
      (K := K) Delta b
    have hpow := polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (canonicalPositiveTransverseSectionFrontierWeight Delta b)
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (1 : Fin 4))) hle
    simpa [canonicalPositiveTransverseReesWeight] using
      dvd_trans hpow
        (canonicalPositiveTransverseSectionOrderCap_dvd
          (K := K) Delta
          (parameterRamificationSection (K := K) 2 b (1 : Fin 4)))
  · have hle := canonicalPositiveTransverseSectionFrontierWeight_le_two
      (K := K) Delta b
    have hpow := polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (canonicalPositiveTransverseSectionFrontierWeight Delta b)
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (2 : Fin 4))) hle
    simpa [canonicalPositiveTransverseReesWeight] using
      dvd_trans hpow
        (canonicalPositiveTransverseSectionOrderCap_dvd
          (K := K) Delta
          (parameterRamificationSection (K := K) 2 b (2 : Fin 4)))
  · have hle := canonicalPositiveTransverseSectionFrontierWeight_le_three
      (K := K) Delta b
    have hpow := polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (canonicalPositiveTransverseSectionFrontierWeight Delta b)
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b (3 : Fin 4))) hle
    simpa [canonicalPositiveTransverseReesWeight] using
      dvd_trans hpow
        (canonicalPositiveTransverseSectionOrderCap_dvd
          (K := K) Delta
          (parameterRamificationSection (K := K) 2 b (3 : Fin 4)))

/-- The ramified zero section is integrally pullable through every frontier
weight. -/
theorem canonicalPositiveTransverseSectionFrontier_zero_hasIntegralSection
    (Delta : ℕ) (b : Fin 4 → Polynomial K) :
    let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
    HasIntegralAdaptiveSmithSection
      (canonicalPositiveTransverseReesWeight r)
      (parameterRamificationSection
        (K := K) 2 (zeroPolynomialSection (K := K))) := by
  dsimp
  intro i
  simp [parameterRamificationSection, zeroPolynomialSection]

/-- Actual family at the maximal moving-section transport frontier.  This is
exactly the existing adaptive Smith exposure; only the chosen weight is new. -/
noncomputable def canonicalPositiveTransverseSectionFrontierFamily
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound Delta P)
    (b : Fin 4 → Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) := by
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  let hr : r ≤ Delta :=
    canonicalPositiveTransverseSectionFrontierWeight_le Delta b
  exact canonicalPositiveTransverseReesFamily r P (hbound.mono hr)

/-- The maximal section-frontier family has the exact partially spent Hessian
clock `2 * (Delta - r)`.  In particular `r = Delta` is literal raw defect
zero, while `r < Delta` is a genuine positive ramified spend. -/
theorem canonicalPositiveTransverseSectionFrontierFamily_hessianDefect
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound Delta P)
    (b : Fin 4 → Polynomial K) :
    let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
    HasPolynomialFamilyHessianDefect (K := K)
      (canonicalPositiveTransverseSectionFrontierFamily Delta P hbound b)
      (2 * (Delta - r)) := by
  dsimp
  let r := canonicalPositiveTransverseSectionFrontierWeight Delta b
  have hr : r ≤ Delta :=
    canonicalPositiveTransverseSectionFrontierWeight_le Delta b
  let hbnd := hbound.mono hr
  have hnonneg :
      4 * (2 * r) ≤
        2 * Delta +
          2 * ∑ i : Fin 4, canonicalPositiveTransverseReesWeight r i := by
    rw [canonicalPositiveTransverseReesWeight_sum]
    omega
  have hout :=
    adaptiveSmithFirstContactExposureFamily_hasHessianDefect
      2 (canonicalPositiveTransverseReesWeight r) (2 * r) Delta
      (by norm_num) hnonneg P hbnd.integralExposure hdef
  change HasPolynomialFamilyHessianDefect (K := K)
    (adaptiveSmithExposureFamily
      2 (canonicalPositiveTransverseReesWeight r) (2 * r)
      P hbnd.integralExposure) (2 * (Delta - r))
  have hclock :
      2 * Delta +
          2 * ∑ i : Fin 4, canonicalPositiveTransverseReesWeight r i -
            4 * (2 * r) =
        2 * (Delta - r) := by
    rw [canonicalPositiveTransverseReesWeight_sum]
    omega
  rw [← hclock]
  exact hout

end

end HC4.Valuation
