import Mathlib.Tactic

/-!
# Binary Schur pivot algebra

This file isolates the elementary two-dimensional algebra used at the first
rank-increasing Schur coefficient of a four-dimensional Hessian family.

For a symmetric block

    [ a  b ]
    [ b  c ]

the rank-one condition is the vanishing determinant relation `a*c = b*b`.
If the block is nonzero, this relation forces a usable diagonal pivot:
either `a ≠ 0`, or the block is already the pure second-axis block
`a = b = 0`, `c ≠ 0`.

The point of recording this separately is that the later first-rank-entry
argument can use a small algebraic certificate instead of invoking general
matrix-rank or Smith-normal-form machinery.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The three coefficients of a symmetric `2 × 2` block. -/
structure BinarySchurBlock (K : Type*) where
  a : K
  b : K
  c : K

/-- The determinant core of a symmetric binary block. -/
def BinarySchurBlock.detCore (q : BinarySchurBlock K) : K :=
  q.a * q.c - q.b * q.b

/-- The block is coefficientwise nonzero. -/
def BinarySchurBlock.Nonzero (q : BinarySchurBlock K) : Prop :=
  q.a ≠ 0 ∨ q.b ≠ 0 ∨ q.c ≠ 0

/-- A left pivot certificate: the first diagonal coefficient is nonzero and
the determinant relation is rank-one. -/
def BinarySchurBlock.LeftPivot (q : BinarySchurBlock K) : Prop :=
  q.a ≠ 0 ∧ q.a * q.c = q.b * q.b

/-- The degenerate coordinate form obtained when the left diagonal entry
vanishes under the rank-one determinant relation. -/
def BinarySchurBlock.RightAxisPivot (q : BinarySchurBlock K) : Prop :=
  q.a = 0 ∧ q.b = 0 ∧ q.c ≠ 0

/-- Vanishing determinant core is the familiar relation `a*c = b^2`. -/
theorem BinarySchurBlock.detCore_eq_zero_iff
    (q : BinarySchurBlock K) :
    q.detCore = 0 ↔ q.a * q.c = q.b * q.b := by
  unfold BinarySchurBlock.detCore
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mpr h

/-- If the left diagonal coefficient vanishes in a determinant-zero
symmetric block, then the off-diagonal coefficient vanishes as well. -/
theorem BinarySchurBlock.offDiagonal_eq_zero_of_left_eq_zero
    (q : BinarySchurBlock K)
    (hdet : q.a * q.c = q.b * q.b)
    (ha : q.a = 0) :
    q.b = 0 := by
  have hb2 : q.b * q.b = 0 := by
    simpa [ha] using hdet.symm
  rcases mul_eq_zero.mp hb2 with hb | hb
  · exact hb
  · exact hb

/-- A nonzero determinant-zero symmetric binary block always has a usable
diagonal pivot.  If the left entry is unavailable, the block is already a
pure nonzero right-axis block. -/
theorem BinarySchurBlock.leftPivot_or_rightAxisPivot
    (q : BinarySchurBlock K)
    (hdet : q.a * q.c = q.b * q.b)
    (hnz : q.Nonzero) :
    q.LeftPivot ∨ q.RightAxisPivot := by
  by_cases ha : q.a = 0
  · right
    have hb : q.b = 0 :=
      q.offDiagonal_eq_zero_of_left_eq_zero hdet ha
    have hc : q.c ≠ 0 := by
      intro hc
      rcases hnz with hna | hnb | hnc
      · exact hna ha
      · exact hnb hb
      · exact hnc hc
    exact ⟨ha, hb, hc⟩
  · left
    exact ⟨ha, hdet⟩

/-- In particular, a nonzero determinant-zero symmetric binary block cannot
have both diagonal entries equal to zero. -/
theorem BinarySchurBlock.nonzeroDiagonal
    (q : BinarySchurBlock K)
    (hdet : q.a * q.c = q.b * q.b)
    (hnz : q.Nonzero) :
    q.a ≠ 0 ∨ q.c ≠ 0 := by
  rcases q.leftPivot_or_rightAxisPivot hdet hnz with hleft | hright
  · exact Or.inl hleft.1
  · exact Or.inr hright.2.2

/-- Version stated directly from a zero determinant core. -/
theorem BinarySchurBlock.pivot_of_detCore_eq_zero
    (q : BinarySchurBlock K)
    (hdet : q.detCore = 0)
    (hnz : q.Nonzero) :
    q.LeftPivot ∨ q.RightAxisPivot := by
  apply q.leftPivot_or_rightAxisPivot
  · exact (q.detCore_eq_zero_iff).mp hdet
  · exact hnz

end

end HC4.Newton
