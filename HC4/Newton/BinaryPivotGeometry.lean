import HC4.Newton.BinarySchurPivot
import Mathlib.Tactic

/-!
# Geometry of a binary rank-one pivot

The rank-two Schur analysis from Phase 90 ends with a nonzero symmetric
binary block

    [ a  b ]
    [ b  c ]

whose determinant core vanishes. Phase 90.1 already proves that such a
block has either a left pivot (`a ≠ 0`, `a*c=b^2`) or is the pure
right-axis block (`a=b=0`, `c ≠ 0`).

This file turns that certificate into the explicit one-direction geometry
needed by the homogeneous Hessian layer.

For a left pivot:

* `(-b,a)` is a nonzero kernel vector;
* if

      Q(x,y) = a x^2 + 2 b x y + c y^2,

  then

      a Q(x,y) = (a x + b y)^2.

For a right-axis pivot, `Q(x,y)=c y^2`.

Thus every nonzero determinant-zero symmetric binary packet is explicitly
a single-direction square packet, without using a general matrix-rank API.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

namespace BinarySchurBlock

/-- Quadratic form associated to the symmetric binary block. -/
def quadratic
    (q : BinarySchurBlock K)
    (x y : K) : K :=
  q.a * x * x + 2 * q.b * x * y + q.c * y * y

/-- First row applied to the canonical left-pivot kernel vector `(-b,a)`. -/
theorem leftKernel_first
    (q : BinarySchurBlock K) :
    q.a * (-q.b) + q.b * q.a = 0 := by
  ring

/-- Under the determinant-zero relation, the second row also annihilates
the canonical vector `(-b,a)`. -/
theorem leftKernel_second
    (q : BinarySchurBlock K)
    (hdet : q.a * q.c = q.b * q.b) :
    q.b * (-q.b) + q.c * q.a = 0 := by
  calc
    q.b * (-q.b) + q.c * q.a =
        -(q.b * q.b) + q.a * q.c := by
      ring
    _ = 0 := by
      rw [hdet]
      ring

/-- The canonical left-pivot kernel vector is nonzero because its second
component is the nonzero pivot `a`. -/
theorem leftKernel_nonzero
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot) :
    (-q.b) ≠ 0 ∨ q.a ≠ 0 := by
  exact Or.inr hleft.1

/-- **Cleared square identity for a left pivot.**
No division is required: multiplying the quadratic form by the nonzero
pivot coefficient turns it into a literal square. -/
theorem quadratic_clearedSquare_of_leftPivot
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot)
    (x y : K) :
    q.a * q.quadratic x y =
      (q.a * x + q.b * y) ^ 2 := by
  rcases hleft with ⟨ha, hdet⟩
  unfold quadratic
  calc
    q.a *
        (q.a * x * x + 2 * q.b * x * y + q.c * y * y) =
      q.a * q.a * x * x
        + 2 * q.a * q.b * x * y
        + (q.a * q.c) * y * y := by
          ring
    _ =
      q.a * q.a * x * x
        + 2 * q.a * q.b * x * y
        + (q.b * q.b) * y * y := by
          rw [hdet]
    _ = (q.a * x + q.b * y) ^ 2 := by
          ring

/-- The right-axis pivot is already a pure square direction. -/
theorem quadratic_eq_rightAxis
    (q : BinarySchurBlock K)
    (hright : q.RightAxisPivot)
    (x y : K) :
    q.quadratic x y = q.c * y * y := by
  rcases hright with ⟨ha, hb, hc⟩
  simp [quadratic, ha, hb]

/-- Explicit geometric dichotomy for every nonzero determinant-zero binary
block. -/
theorem squareGeometry_of_detCore_eq_zero
    (q : BinarySchurBlock K)
    (hdet : q.detCore = 0)
    (hnz : q.Nonzero) :
    (q.LeftPivot ∧
      (∀ x y : K,
        q.a * q.quadratic x y =
          (q.a * x + q.b * y) ^ 2)) ∨
    (q.RightAxisPivot ∧
      (∀ x y : K,
        q.quadratic x y = q.c * y * y)) := by
  rcases q.pivot_of_detCore_eq_zero hdet hnz with hleft | hright
  · left
    refine ⟨hleft, ?_⟩
    intro x y
    exact q.quadratic_clearedSquare_of_leftPivot hleft x y
  · right
    refine ⟨hright, ?_⟩
    intro x y
    exact q.quadratic_eq_rightAxis hright x y

/-- Version using the determinant relation `a*c=b^2` directly. -/
theorem squareGeometry_of_rankOneRelation
    (q : BinarySchurBlock K)
    (hdet : q.a * q.c = q.b * q.b)
    (hnz : q.Nonzero) :
    (q.LeftPivot ∧
      (∀ x y : K,
        q.a * q.quadratic x y =
          (q.a * x + q.b * y) ^ 2)) ∨
    (q.RightAxisPivot ∧
      (∀ x y : K,
        q.quadratic x y = q.c * y * y)) := by
  apply q.squareGeometry_of_detCore_eq_zero
  · exact q.detCore_eq_zero_iff.mpr hdet
  · exact hnz

end BinarySchurBlock

end

end HC4.Newton
