import HC4.Newton.TerminalNonnegativeWeights
import Mathlib.Tactic

/-!
# The standard one-zero terminal weight pattern

The remaining nonnegative terminal boundary after the strictly-positive
branch is closed is the case of exactly one zero weight.

After a coordinate permutation, write the weights as

    (0, d, a, d-a),   0 < a < d.

The zero coordinate is paired with the unique degree-`d` coordinate by the
determinant matching; the two remaining coordinates have positive
complementary weights.

This module records the standard model and its elementary positivity facts.
The coordinate-permutation adapter from an arbitrary one-zero face is kept
separate.
-/

namespace HC4.Newton

noncomputable section

/-- Standard one-zero terminal weight `(0,d,a,d-a)`. -/
def standardOneZeroTerminalWeight
    (d a : ℤ) : Fin 4 -> ℤ
  | 0 => 0
  | 1 => d
  | 2 => a
  | 3 => d - a

@[simp] theorem standardOneZeroTerminalWeight_zero
    (d a : ℤ) :
    standardOneZeroTerminalWeight d a 0 = 0 := rfl

@[simp] theorem standardOneZeroTerminalWeight_one
    (d a : ℤ) :
    standardOneZeroTerminalWeight d a 1 = d := rfl

@[simp] theorem standardOneZeroTerminalWeight_two
    (d a : ℤ) :
    standardOneZeroTerminalWeight d a 2 = a := rfl

@[simp] theorem standardOneZeroTerminalWeight_three
    (d a : ℤ) :
    standardOneZeroTerminalWeight d a 3 = d - a := rfl

/-- The three nonzero coordinates of the standard one-zero pattern are
strictly positive. -/
theorem standardOneZero_positive_coordinates
    {d a : ℤ}
    (ha : 0 < a)
    (had : a < d) :
    0 < standardOneZeroTerminalWeight d a 1 ∧
      0 < standardOneZeroTerminalWeight d a 2 ∧
      0 < standardOneZeroTerminalWeight d a 3 := by
  simp [standardOneZeroTerminalWeight, ha]
  omega

/-- The standard one-zero pattern is nonnegative. -/
theorem standardOneZero_nonnegative
    {d a : ℤ}
    (ha : 0 < a)
    (had : a < d) :
    IsNonnegativeIntegralWeight
      (standardOneZeroTerminalWeight d a) := by
  intro i
  fin_cases i <;>
    simp [standardOneZeroTerminalWeight] <;>
    omega

/-- Coordinate zero is the unique zero weight in the standard pattern. -/
theorem standardOneZero_zero_iff
    {d a : ℤ}
    (ha : 0 < a)
    (had : a < d)
    (i : Fin 4) :
    standardOneZeroTerminalWeight d a i = 0 ↔
      i = 0 := by
  fin_cases i <;>
    simp [standardOneZeroTerminalWeight] <;>
    omega

end

end HC4.Newton
