import HC4.Newton.SmithGradeArithmetic
import Mathlib.Tactic

/-!
# Balance of the two surviving Smith extreme grades

After the elementary Smith-grade classification, the two possible
negative-coordinate extremes have the form

    p_k = (-1, k),
    q_l = (l, -1),

with `k,l >= 1`.

This file isolates the elementary convex/separation geometry of those two
points.

If the origin lies on their convex segment with nonnegative rational
weights, then

    k*l = 1,

hence `k=l=1`.

Conversely, when `k*l > 1` there is an explicit integral separating
functional

    theta = (2k, k*l + 1)

which is strictly positive on both extreme grades.  Thus the two-extreme
configuration cannot balance the origin.

This is the finite algebraic core of the pole-minimal convex-balance
argument.  The next module must connect a separating Smith functional to a
legal infinitesimal valuation tilt and hence to pole-minimality.
-/

namespace HC4.Newton

noncomputable section

/-- The negative-first surviving Smith extreme `(-1,k)`. -/
def smithNegativeFirstExtreme
    (k : ℕ) : ℤ × ℤ :=
  (-1, (k : ℤ))

/-- The negative-second surviving Smith extreme `(l,-1)`. -/
def smithNegativeSecondExtreme
    (l : ℕ) : ℤ × ℤ :=
  ((l : ℤ), -1)

/-- Integer dot product on a Smith grade. -/
def smithGradeDot
    (theta gamma : ℤ × ℤ) : ℤ :=
  theta.1 * gamma.1 + theta.2 * gamma.2

/-- Rational convex balance of the two surviving extreme grades. -/
def SmithTwoExtremeBalance
    (k l : ℕ) : Prop :=
  ∃ alpha beta : ℚ,
    0 ≤ alpha ∧
    0 ≤ beta ∧
    alpha + beta = 1 ∧
    alpha * (-1 : ℚ) + beta * (l : ℚ) = 0 ∧
    alpha * (k : ℚ) + beta * (-1 : ℚ) = 0

/-- In a two-extreme balance the first coefficient cannot vanish. -/
theorem smithTwoExtremeBalance_alpha_ne_zero
    {k l : ℕ}
    (hbal : SmithTwoExtremeBalance k l) :
    ∃ alpha beta : ℚ,
      0 ≤ alpha ∧
      0 ≤ beta ∧
      alpha + beta = 1 ∧
      alpha ≠ 0 ∧
      alpha * (-1 : ℚ) + beta * (l : ℚ) = 0 ∧
      alpha * (k : ℚ) + beta * (-1 : ℚ) = 0 := by
  rcases hbal with
    ⟨alpha, beta, halpha, hbeta, hsum, hfirst, hsecond⟩
  have hane : alpha ≠ 0 := by
    intro ha
    have hb0 : beta = 0 := by
      rw [ha] at hsecond
      norm_num at hsecond
      exact hsecond
    rw [ha, hb0] at hsum
    norm_num at hsum
  exact
    ⟨alpha, beta, halpha, hbeta, hsum, hane, hfirst, hsecond⟩

/-- Exact algebraic balance equation for the two extreme parameters. -/
theorem smithTwoExtremeBalance_cast_product_eq_one
    {k l : ℕ}
    (hbal : SmithTwoExtremeBalance k l) :
    (k : ℚ) * (l : ℚ) = 1 := by
  rcases smithTwoExtremeBalance_alpha_ne_zero hbal with
    ⟨alpha, beta, halpha, hbeta, hsum, hane, hfirst, hsecond⟩
  have hbetaEq : beta = alpha * (k : ℚ) := by
    linarith
  have halphaEq : alpha = beta * (l : ℚ) := by
    linarith
  have hprod :
      alpha * ((k : ℚ) * (l : ℚ) - 1) = 0 := by
    rw [hbetaEq] at halphaEq
    nlinarith
  have hfactor :
      (k : ℚ) * (l : ℚ) - 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hane
  linarith

/-- A balanced pair of positive integral extremes necessarily has
`k*l = 1` already in `Nat`. -/
theorem smithTwoExtremeBalance_nat_product_eq_one
    {k l : ℕ}
    (hbal : SmithTwoExtremeBalance k l) :
    k * l = 1 := by
  have hq :
      (k : ℚ) * (l : ℚ) = 1 :=
    smithTwoExtremeBalance_cast_product_eq_one hbal
  have hq' :
      (((k * l : ℕ) : ℚ)) = 1 := by
    simpa only [Nat.cast_mul] using hq
  exact_mod_cast hq'

/-- **Two-extreme balance collapse.**
Positive surviving extremes that balance the origin are exactly
`(-1,1)` and `(1,-1)`. -/
theorem smithTwoExtremeBalance_forces_target_grades
    {k l : ℕ}
    (hk : 1 ≤ k)
    (hl : 1 ≤ l)
    (hbal : SmithTwoExtremeBalance k l) :
    smithNegativeFirstExtreme k = (-1, 1) ∧
      smithNegativeSecondExtreme l = (1, -1) := by
  have hprodEq :
      k * l = 1 :=
    smithTwoExtremeBalance_nat_product_eq_one hbal
  have hprodLe : k * l ≤ 1 := by
    omega
  rcases smithBalancedExtreme_productBound
      k l hk hl hprodLe with ⟨hk1, hl1⟩
  subst k
  subst l
  norm_num [smithNegativeFirstExtreme, smithNegativeSecondExtreme]

/-- Explicit integral separator for the two extreme grades when their
product exceeds one. -/
def smithExtremeSeparator
    (k l : ℕ) : ℤ × ℤ :=
  (2 * (k : ℤ), ((k * l : ℕ) : ℤ) + 1)

/-- The explicit separator is positive on `(-1,k)` whenever `k*l > 1`. -/
theorem smithExtremeSeparator_pos_negativeFirst
    {k l : ℕ}
    (hk : 1 ≤ k)
    (hprod : 1 < k * l) :
    0 <
      smithGradeDot
        (smithExtremeSeparator k l)
        (smithNegativeFirstExtreme k) := by
  unfold smithGradeDot
  simp [smithExtremeSeparator, smithNegativeFirstExtreme]
  have hkz : (1 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast hk
  have hpz : (1 : ℤ) < ((k * l : ℕ) : ℤ) := by
    exact_mod_cast hprod
  nlinarith

/-- The same separator is positive on `(l,-1)` whenever `k*l > 1`. -/
theorem smithExtremeSeparator_pos_negativeSecond
    {k l : ℕ}
    (hprod : 1 < k * l) :
    0 <
      smithGradeDot
        (smithExtremeSeparator k l)
        (smithNegativeSecondExtreme l) := by
  unfold smithGradeDot
  simp [smithExtremeSeparator, smithNegativeSecondExtreme]
  have hpz : (1 : ℤ) < ((k * l : ℕ) : ℤ) := by
    exact_mod_cast hprod
  nlinarith

/-- Any nonzero first-quadrant grade is also strictly positive under the
explicit separator, provided the extreme parameters are positive. -/
theorem smithExtremeSeparator_pos_nonnegative
    {k l : ℕ}
    (hk : 1 ≤ k)
    (a b : ℕ)
    (hnz : a ≠ 0 ∨ b ≠ 0) :
    0 <
      smithGradeDot
        (smithExtremeSeparator k l)
        ((a : ℤ), (b : ℤ)) := by
  unfold smithGradeDot
  simp [smithExtremeSeparator]
  have hkz : (1 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast hk
  have hlz : (0 : ℤ) ≤ (l : ℤ) := by
    exact_mod_cast (Nat.zero_le l)
  have hcoef1 : (0 : ℤ) < 2 * (k : ℤ) := by
    omega
  have hcoef2 :
      (0 : ℤ) < (k : ℤ) * (l : ℤ) + 1 := by
    have hkl : (0 : ℤ) ≤ (k : ℤ) * (l : ℤ) :=
      mul_nonneg (by omega) hlz
    omega
  rcases hnz with ha | hb
  · have haz : (0 : ℤ) < (a : ℤ) := by
      exact_mod_cast (Nat.pos_of_ne_zero ha)
    have hbz : (0 : ℤ) ≤ (b : ℤ) := by
      exact_mod_cast (Nat.zero_le b)
    have hterm1 :
        0 < (2 * (k : ℤ)) * (a : ℤ) :=
      mul_pos hcoef1 haz
    have hterm2 :
        0 ≤ ((k : ℤ) * (l : ℤ) + 1) * (b : ℤ) :=
      mul_nonneg (le_of_lt hcoef2) hbz
    exact add_pos_of_pos_of_nonneg hterm1 hterm2
  · have hbz : (0 : ℤ) < (b : ℤ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hb)
    have haz : (0 : ℤ) ≤ (a : ℤ) := by
      exact_mod_cast (Nat.zero_le a)
    have hterm1 :
        0 ≤ (2 * (k : ℤ)) * (a : ℤ) :=
      mul_nonneg (le_of_lt hcoef1) haz
    have hterm2 :
        0 < ((k : ℤ) * (l : ℤ) + 1) * (b : ℤ) :=
      mul_pos hcoef2 hbz
    exact add_pos_of_nonneg_of_pos hterm1 hterm2

end

end HC4.Newton
