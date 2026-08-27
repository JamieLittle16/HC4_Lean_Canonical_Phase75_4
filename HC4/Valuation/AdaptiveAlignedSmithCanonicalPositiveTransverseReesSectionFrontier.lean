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

This file begins that adapter with the two arithmetic facts needed by the
frontier construction: downward closure of family integrality, and exact
factorisation at a capped section order.  No new geometric or termination
claim is introduced.
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
    (Delta : ℕ) (p : Polynomial K) : ℕ :=
  if hp : p = 0 then Delta
  else min Delta (polynomialParameterOrder p hp)

/-- A section-order cap never exceeds the requested determinant-closing
weight. -/
theorem canonicalPositiveTransverseSectionOrderCap_le
    (Delta : ℕ) (p : Polynomial K) :
    canonicalPositiveTransverseSectionOrderCap Delta p ≤ Delta := by
  classical
  unfold canonicalPositiveTransverseSectionOrderCap
  split
  · simp
  · exact min_le_left _ _

/-- The ramified section coordinate is divisible by the source weight given by
its capped exact order. -/
theorem canonicalPositiveTransverseSectionOrderCap_dvd
    (Delta : ℕ) (p : Polynomial K) :
    Polynomial.X ^ canonicalPositiveTransverseSectionOrderCap Delta p ∣ p := by
  classical
  unfold canonicalPositiveTransverseSectionOrderCap
  split
  · rename_i hp
    subst p
    simp
  · rename_i hp
    let q := polynomialParameterOrder p hp
    let u := polynomialParameterPrimitivePart p hp
    have hfactor : p = Polynomial.X ^ q * u := by
      simpa [q, u] using polynomialParameterPrimitivePart_spec p hp
    have hsmall :
        Polynomial.X ^ min Delta q ∣ Polynomial.X ^ q :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) (min Delta q) q (min_le_right _ _)
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
    have hcap : canonicalPositiveTransverseSectionOrderCap Delta p = q := by
      simp [canonicalPositiveTransverseSectionOrderCap, hp, q,
        min_eq_right (Nat.le_of_lt hq)]
    refine ⟨hp, ?_, ?_⟩
    · rw [hcap]
      exact polynomialParameterPrimitivePart_spec p hp
    · exact polynomialParameterPrimitivePart_constantCoeff_ne_zero p hp

end

end HC4.Valuation
