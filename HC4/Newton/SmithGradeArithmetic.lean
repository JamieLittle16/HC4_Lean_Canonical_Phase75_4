import HC4.Newton.SmithCollisionQuadraticRankOne
import Mathlib.Tactic

/-!
# Elementary arithmetic of the Smith relative Levi grades

For a Smith-chart monomial

    x^a y^b z^c w^d

the two relative Levi grades are

    Gamma = (b + d - 1, c + d - 1).

The longitudinal exponent `a` is irrelevant to these two coordinates.

This file formalises the elementary lattice facts used after the
directional first-wall exclusion:

* a negative first grade forces `b = d = 0`;
* a negative second grade forces `c = d = 0`;
* after excluding the low first-wall grades, a negative first coordinate
  has the form `(-1,k)` with `k >= 1`, and symmetrically;
* zero grade has exactly two exponent patterns:
      (b,c,d) = (1,1,0)   or   (0,0,1);
  after excluding the `w`-linear wall only `yz` remains;
* the three quadratic transverse monomials `z^2`, `yz`, `y^2` have grades
      (-1,1), (0,0), (1,-1).

The convex-balance/separation theorem is deliberately left to the next
module.  This file provides the stable finite arithmetic API it will use.
-/

namespace HC4.Newton

noncomputable section

/-- First relative Levi grade of `x^a y^b z^c w^d`. -/
def smithGradeFirst
    (b d : ℕ) : ℤ :=
  ((b + d : ℕ) : ℤ) - 1

/-- Second relative Levi grade of `x^a y^b z^c w^d`. -/
def smithGradeSecond
    (c d : ℕ) : ℤ :=
  ((c + d : ℕ) : ℤ) - 1

/-- Pair-valued Smith relative Levi grade. -/
def smithGrade
    (b c d : ℕ) : ℤ × ℤ :=
  (smithGradeFirst b d, smithGradeSecond c d)

/-- Negative first grade forces absence of both `y` and `w`. -/
theorem smithGradeFirst_neg_shape
    (b d : ℕ)
    (hneg : smithGradeFirst b d < 0) :
    b = 0 ∧ d = 0 ∧ smithGradeFirst b d = -1 := by
  unfold smithGradeFirst at *
  omega

/-- Negative second grade forces absence of both `z` and `w`. -/
theorem smithGradeSecond_neg_shape
    (c d : ℕ)
    (hneg : smithGradeSecond c d < 0) :
    c = 0 ∧ d = 0 ∧ smithGradeSecond c d = -1 := by
  unfold smithGradeSecond at *
  omega

/-- If the first grade is negative but neither `(-1,-1)` nor `(-1,0)`
survives, then the second grade is at least one. -/
theorem smithGrade_negativeFirst_surviving
    (b c d : ℕ)
    (hneg : smithGradeFirst b d < 0)
    (hnotMinusOne : smithGradeSecond c d ≠ -1)
    (hnotZero : smithGradeSecond c d ≠ 0) :
    smithGradeFirst b d = -1 ∧
      1 ≤ smithGradeSecond c d := by
  rcases smithGradeFirst_neg_shape b d hneg with
    ⟨hb, hd, hfirst⟩
  subst d
  constructor
  · exact hfirst
  · unfold smithGradeSecond at hnotMinusOne hnotZero ⊢
    omega

/-- Symmetric surviving negative-second statement. -/
theorem smithGrade_negativeSecond_surviving
    (b c d : ℕ)
    (hneg : smithGradeSecond c d < 0)
    (hnotMinusOne : smithGradeFirst b d ≠ -1)
    (hnotZero : smithGradeFirst b d ≠ 0) :
    smithGradeSecond c d = -1 ∧
      1 ≤ smithGradeFirst b d := by
  rcases smithGradeSecond_neg_shape c d hneg with
    ⟨hc, hd, hsecond⟩
  subst d
  constructor
  · exact hsecond
  · unfold smithGradeFirst at hnotMinusOne hnotZero ⊢
    omega

/-- A zero Smith grade has exactly the `yz` exponent pattern or the
`w`-linear exponent pattern. -/
theorem smithGrade_zero_cases
    (b c d : ℕ)
    (hfirst : smithGradeFirst b d = 0)
    (hsecond : smithGradeSecond c d = 0) :
    (b = 1 ∧ c = 1 ∧ d = 0) ∨
      (b = 0 ∧ c = 0 ∧ d = 1) := by
  unfold smithGradeFirst at hfirst
  unfold smithGradeSecond at hsecond
  omega

/-- Excluding the `w`-linear zero-grade wall leaves only `yz`. -/
theorem smithGrade_zero_is_yz_of_not_wLinear
    (b c d : ℕ)
    (hfirst : smithGradeFirst b d = 0)
    (hsecond : smithGradeSecond c d = 0)
    (hnotW : ¬ (b = 0 ∧ c = 0 ∧ d = 1)) :
    b = 1 ∧ c = 1 ∧ d = 0 := by
  rcases smithGrade_zero_cases b c d hfirst hsecond with
    hyz | hw
  · exact hyz
  · exact False.elim (hnotW hw)

/-- `z^2` has Smith grade `(-1,1)`. -/
@[simp] theorem smithGrade_z_sq :
    smithGrade 0 2 0 = (-1, 1) := by
  norm_num [smithGrade, smithGradeFirst, smithGradeSecond]

/-- `yz` has Smith grade `(0,0)`. -/
@[simp] theorem smithGrade_yz :
    smithGrade 1 1 0 = (0, 0) := by
  norm_num [smithGrade, smithGradeFirst, smithGradeSecond]

/-- `y^2` has Smith grade `(1,-1)`. -/
@[simp] theorem smithGrade_y_sq :
    smithGrade 2 0 0 = (1, -1) := by
  norm_num [smithGrade, smithGradeFirst, smithGradeSecond]

/-- If a surviving negative-first grade is exactly `(-1,1)`, then its
transverse exponent pattern is `z^2`. -/
theorem smithGrade_eq_minusOne_one_exponents
    (b c d : ℕ)
    (hfirst : smithGradeFirst b d = -1)
    (hsecond : smithGradeSecond c d = 1) :
    b = 0 ∧ c = 2 ∧ d = 0 := by
  unfold smithGradeFirst at hfirst
  unfold smithGradeSecond at hsecond
  omega

/-- Grade `(1,-1)` is exactly the `y^2` exponent pattern. -/
theorem smithGrade_eq_one_minusOne_exponents
    (b c d : ℕ)
    (hfirst : smithGradeFirst b d = 1)
    (hsecond : smithGradeSecond c d = -1) :
    b = 2 ∧ c = 0 ∧ d = 0 := by
  unfold smithGradeFirst at hfirst
  unfold smithGradeSecond at hsecond
  omega

/-- Grade `(0,0)`, after excluding the `w`-linear wall, is exactly `yz`. -/
theorem smithGrade_eq_zero_zero_exponents_of_not_wLinear
    (b c d : ℕ)
    (hgrade : smithGrade b c d = (0, 0))
    (hnotW : ¬ (b = 0 ∧ c = 0 ∧ d = 1)) :
    b = 1 ∧ c = 1 ∧ d = 0 := by
  have hfirst : smithGradeFirst b d = 0 := by
    exact congrArg Prod.fst hgrade
  have hsecond : smithGradeSecond c d = 0 := by
    exact congrArg Prod.snd hgrade
  exact
    smithGrade_zero_is_yz_of_not_wLinear
      b c d hfirst hsecond hnotW

/-- Once the balancing argument has produced the numerical bound
`k*l <= 1`, positive integral extreme parameters must both equal one. -/
theorem smithBalancedExtreme_productBound
    (k l : ℕ)
    (hk : 1 ≤ k)
    (hl : 1 ≤ l)
    (hprod : k * l ≤ 1) :
    k = 1 ∧ l = 1 := by
  have hk_le : k ≤ 1 := by
    calc
      k = k * 1 := by simp
      _ ≤ k * l := Nat.mul_le_mul_left k hl
      _ ≤ 1 := hprod
  have hk_eq : k = 1 := Nat.le_antisymm hk_le hk
  have hl_le : l ≤ 1 := by
    calc
      l = 1 * l := by simp
      _ ≤ k * l := Nat.mul_le_mul_right l hk
      _ ≤ 1 := hprod
  have hl_eq : l = 1 := Nat.le_antisymm hl_le hl
  exact ⟨hk_eq, hl_eq⟩

/-- Elementary endpoint of the balanced-grade calculation: if the
negative-coordinate extremes are `(-1,k)` and `(l,-1)` with positive
integral parameters and balance has forced `k*l <= 1`, then the only
possible extremes are `(-1,1)` and `(1,-1)`. -/
theorem smithBalancedExtreme_grades
    (k l : ℕ)
    (hk : 1 ≤ k)
    (hl : 1 ≤ l)
    (hprod : k * l ≤ 1) :
    ((-1 : ℤ), (k : ℤ)) = (-1, 1) ∧
      ((l : ℤ), (-1 : ℤ)) = (1, -1) := by
  rcases smithBalancedExtreme_productBound
      k l hk hl hprod with ⟨hk1, hl1⟩
  subst k
  subst l
  norm_num

end

end HC4.Newton
