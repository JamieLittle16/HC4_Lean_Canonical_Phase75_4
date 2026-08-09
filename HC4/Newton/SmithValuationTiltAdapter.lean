import HC4.Newton.FiniteValuationTilt
import Mathlib.Tactic

/-!
# Smith conformal tilt as a valuation change

For a Smith-chart monomial

    x^a y^b z^c w^d

the two relative Levi grades are

    Gamma = (b+d-1, c+d-1).

The corresponding two-parameter conformal tilt fixes the primitive
`x`-direction and changes the raw monomial weight by

    theta_1*b + theta_2*c + (theta_1+theta_2)*d.

The normalising Levi term itself changes by `theta_1+theta_2`.  Therefore
the change in the normalised coefficient valuation is exactly

    theta dot Gamma.

This file proves that identity directly.

There is also a useful global bound requiring no finite-support maximum.
Every Smith-grade coordinate is at least `-1`.  Hence for a separator with
nonnegative coordinates,

    theta dot Gamma >= -(theta_1+theta_2).

For the explicit Phase 93.6 separator this gives the natural-number bound

    B = 2k + k*l + 1.

Combining this bound with Phase 93.7 yields a finite-support theorem saying
that if the separator is positive on every old minimal-face monomial, then
the explicit small rational conformal tilt raises every supported
normalised valuation strictly above the old minimum.
-/

namespace HC4.Newton

noncomputable section

/-- Raw monomial-weight change under the two independent Smith conformal
tilts.  The `w` exponent sees the sum of the two tilt parameters. -/
def smithRawConformalTiltChange
    (theta : ℤ × ℤ)
    (b c d : ℕ) : ℤ :=
  theta.1 * (b : ℤ) +
    theta.2 * (c : ℤ) +
    (theta.1 + theta.2) * (d : ℤ)

/-- Change of the normalising Levi reference weight. -/
def smithLeviNormalisationTiltChange
    (theta : ℤ × ℤ) : ℤ :=
  theta.1 + theta.2

/-- Change of the normalised coefficient valuation. -/
def smithNormalisedConformalTiltChange
    (theta : ℤ × ℤ)
    (b c d : ℕ) : ℤ :=
  smithRawConformalTiltChange theta b c d -
    smithLeviNormalisationTiltChange theta

/-- **Smith valuation adapter.**
The normalised conformal valuation change is exactly the dot product of
the tilt direction with the relative Levi grade. -/
theorem smithNormalisedConformalTiltChange_eq_gradeDot
    (theta : ℤ × ℤ)
    (b c d : ℕ) :
    smithNormalisedConformalTiltChange theta b c d =
      smithGradeDot theta (smithGrade b c d) := by
  unfold smithNormalisedConformalTiltChange
  unfold smithRawConformalTiltChange
  unfold smithLeviNormalisationTiltChange
  unfold smithGradeDot
  unfold smithGrade
  unfold smithGradeFirst
  unfold smithGradeSecond
  push_cast
  ring

/-- Every first Smith-grade coordinate is at least `-1`. -/
theorem smithGradeFirst_ge_neg_one
    (b d : ℕ) :
    (-1 : ℤ) ≤ smithGradeFirst b d := by
  unfold smithGradeFirst
  omega

/-- Every second Smith-grade coordinate is at least `-1`. -/
theorem smithGradeSecond_ge_neg_one
    (c d : ℕ) :
    (-1 : ℤ) ≤ smithGradeSecond c d := by
  unfold smithGradeSecond
  omega

/-- A nonnegative Smith tilt has a universal lower bound on its valuation
change, independent of the finite support. -/
theorem smithGradeDot_lower_bound_of_nonnegative
    (theta : ℤ × ℤ)
    (htheta1 : 0 ≤ theta.1)
    (htheta2 : 0 ≤ theta.2)
    (b c d : ℕ) :
    -(theta.1 + theta.2) ≤
      smithGradeDot theta (smithGrade b c d) := by
  have hg1 :
      (-1 : ℤ) ≤ smithGradeFirst b d :=
    smithGradeFirst_ge_neg_one b d
  have hg2 :
      (-1 : ℤ) ≤ smithGradeSecond c d :=
    smithGradeSecond_ge_neg_one c d
  have h1 :
      theta.1 * (-1 : ℤ) ≤
        theta.1 * smithGradeFirst b d :=
    mul_le_mul_of_nonneg_left hg1 htheta1
  have h2 :
      theta.2 * (-1 : ℤ) ≤
        theta.2 * smithGradeSecond c d :=
    mul_le_mul_of_nonneg_left hg2 htheta2
  unfold smithGradeDot
  unfold smithGrade
  dsimp
  linarith

/-- Natural-number lower-bound constant for the explicit Phase 93.6
separator. -/
def smithExtremeSeparatorBound
    (k l : ℕ) : ℕ :=
  2 * k + k * l + 1

/-- The first coordinate of the explicit separator is nonnegative. -/
theorem smithExtremeSeparator_first_nonnegative
    (k l : ℕ) :
    (0 : ℤ) ≤ (smithExtremeSeparator k l).1 := by
  simp [smithExtremeSeparator]

/-- The second coordinate of the explicit separator is nonnegative. -/
theorem smithExtremeSeparator_second_nonnegative
    (k l : ℕ) :
    (0 : ℤ) ≤ (smithExtremeSeparator k l).2 := by
  change (0 : ℤ) ≤ (((k * l : ℕ) : ℤ)) + 1
  have hkl : (0 : ℤ) ≤ (((k * l : ℕ) : ℤ)) := by
    exact_mod_cast (Nat.zero_le (k * l))
  omega

/-- The sum of the two explicit separator coordinates is exactly the
natural bound chosen above. -/
theorem smithExtremeSeparator_coordinateSum
    (k l : ℕ) :
    (smithExtremeSeparator k l).1 +
        (smithExtremeSeparator k l).2 =
      (smithExtremeSeparatorBound k l : ℕ) := by
  simp [smithExtremeSeparator, smithExtremeSeparatorBound]
  ring

/-- Universal lower bound for the explicit Smith separator on every
Smith-chart monomial. -/
theorem smithExtremeSeparator_gradeDot_lower_bound
    (k l b c d : ℕ) :
    -((smithExtremeSeparatorBound k l : ℕ) : ℤ) ≤
      smithGradeDot
        (smithExtremeSeparator k l)
        (smithGrade b c d) := by
  have h :=
    smithGradeDot_lower_bound_of_nonnegative
      (smithExtremeSeparator k l)
      (smithExtremeSeparator_first_nonnegative k l)
      (smithExtremeSeparator_second_nonnegative k l)
      b c d
  rw [smithExtremeSeparator_coordinateSum k l] at h
  exact h

/-- A finite support element carrying only the Smith-relevant exponents.
The longitudinal exponent does not enter the relative Levi grade. -/
structure SmithSupportExponent where
  b : ℕ
  c : ℕ
  d : ℕ
deriving DecidableEq

/-- Relative Levi grade of a finite-support exponent record. -/
def SmithSupportExponent.grade
    (e : SmithSupportExponent) : ℤ × ℤ :=
  smithGrade e.b e.c e.d

/-- Valuation derivative of an exponent under the explicit separator. -/
def smithSeparatorDelta
    (k l : ℕ)
    (e : SmithSupportExponent) : ℤ :=
  smithGradeDot
    (smithExtremeSeparator k l)
    e.grade

/-- The explicit separator derivative has the Phase 93.7 lower bound on
every support exponent. -/
theorem smithSeparatorDelta_lower_bound
    (k l : ℕ)
    (e : SmithSupportExponent) :
    -((smithExtremeSeparatorBound k l : ℕ) : ℤ) ≤
      smithSeparatorDelta k l e := by
  exact
    smithExtremeSeparator_gradeDot_lower_bound
      k l e.b e.c e.d

/-- **Finite-support Smith valuation tilt.**
If the old integral normalised valuations have minimum `m`, and every
monomial on that old minimum face is strictly positive for the explicit
Smith separator, then the Phase 93.7 rational tilt raises every supported
normalised valuation strictly above `m`.

No separate support-dependent bound is required. -/
theorem smithFiniteSupportTilt_strictly_raises_minimum
    (S : Finset SmithSupportExponent)
    (k l : ℕ)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hfacePositive :
      ∀ e ∈ S,
        base e = m ->
          (1 : ℤ) ≤ smithSeparatorDelta k l e) :
    ∀ e ∈ S,
      (m : ℚ) <
        finiteTiltedValue
          (finiteTiltEpsilon
            (smithExtremeSeparatorBound k l : ℚ))
          (base e : ℚ)
          (smithSeparatorDelta k l e : ℚ) := by
  apply
    finiteSupportTilt_strictly_raises_minimum
      S
      (smithExtremeSeparatorBound k l)
      m
      base
      (smithSeparatorDelta k l)
  · exact hmin
  · intro e he
    exact smithSeparatorDelta_lower_bound k l e
  · exact hfacePositive

end

end HC4.Newton
