import HC4.Newton.BinarySchurPivot
import Mathlib.Tactic

/-!
# First binary Schur entry

Phase 90.1 isolated the rank-one pivot algebra for a nonzero symmetric
`2 × 2` block with vanishing determinant.

At a first rank-increasing Schur order, the coefficient that appears is
only defined up to a nonzero scalar coming from the chosen parameter/
normalisation.  This file records that the pivot conclusion is invariant
under that scalar.

For a block `q` and scalar `t`,

    detCore (t • q) = t^2 * detCore q.

Hence a nonzero scale cannot create determinant-zero artificially.  If the
scaled first coefficient has zero determinant and the underlying block is
nonzero, the Phase 90.1 pivot theorem applies to the unscaled block.

This is the algebraic certificate used by the next phase, where the
determinant-order calculation will produce the zero determinant hypothesis
for the actual first Schur coefficient.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

namespace BinarySchurBlock

/-- Coefficientwise scalar multiplication of a binary Schur block. -/
def scale (t : K) (q : BinarySchurBlock K) : BinarySchurBlock K where
  a := t * q.a
  b := t * q.b
  c := t * q.c

@[simp] theorem scale_a (t : K) (q : BinarySchurBlock K) :
    (q.scale t).a = t * q.a := rfl

@[simp] theorem scale_b (t : K) (q : BinarySchurBlock K) :
    (q.scale t).b = t * q.b := rfl

@[simp] theorem scale_c (t : K) (q : BinarySchurBlock K) :
    (q.scale t).c = t * q.c := rfl

/-- Determinant core is homogeneous of degree two under scalar scaling. -/
theorem detCore_scale (t : K) (q : BinarySchurBlock K) :
    (q.scale t).detCore = t ^ 2 * q.detCore := by
  unfold scale BinarySchurBlock.detCore
  ring

/-- A nonzero scalar preserves coefficientwise nonvanishing. -/
theorem nonzero_scale_iff
    (t : K) (q : BinarySchurBlock K)
    (ht : t ≠ 0) :
    (q.scale t).Nonzero ↔ q.Nonzero := by
  constructor
  · intro hscaled
    rcases hscaled with ha | hb | hc
    · left
      intro hqa
      exact ha (by simp [scale, hqa])
    · right
      left
      intro hqb
      exact hb (by simp [scale, hqb])
    · right
      right
      intro hqc
      exact hc (by simp [scale, hqc])
  · intro hq
    rcases hq with ha | hb | hc
    · left
      exact mul_ne_zero ht ha
    · right
      left
      exact mul_ne_zero ht hb
    · right
      right
      exact mul_ne_zero ht hc

/-- Zero determinant of a nontrivially scaled first coefficient forces zero
determinant of the underlying block. -/
theorem detCore_eq_zero_of_scale_detCore_eq_zero
    (t : K) (q : BinarySchurBlock K)
    (ht : t ≠ 0)
    (hscaled : (q.scale t).detCore = 0) :
    q.detCore = 0 := by
  rw [detCore_scale] at hscaled
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  exact (mul_eq_zero.mp hscaled).resolve_left ht2

/-- **First-entry pivot certificate.**
A nonzero binary block whose nonzero scalar multiple has zero determinant
already carries the Phase 90.1 rank-one pivot certificate. -/
theorem pivot_of_scaled_detCore_eq_zero
    (t : K) (q : BinarySchurBlock K)
    (ht : t ≠ 0)
    (hnz : q.Nonzero)
    (hscaled : (q.scale t).detCore = 0) :
    q.LeftPivot ∨ q.RightAxisPivot := by
  apply q.pivot_of_detCore_eq_zero
  · exact q.detCore_eq_zero_of_scale_detCore_eq_zero t ht hscaled
  · exact hnz

/-- Same conclusion when nonvanishing is known for the scaled coefficient
rather than for the normalised block. -/
theorem pivot_of_scaled_nonzero_detCore_eq_zero
    (t : K) (q : BinarySchurBlock K)
    (ht : t ≠ 0)
    (hnzScaled : (q.scale t).Nonzero)
    (hscaled : (q.scale t).detCore = 0) :
    q.LeftPivot ∨ q.RightAxisPivot := by
  apply q.pivot_of_scaled_detCore_eq_zero t ht
  · exact (q.nonzero_scale_iff t ht).mp hnzScaled
  · exact hscaled

end BinarySchurBlock

/-- Data carried by a first nonzero binary Schur coefficient after choosing
a normalisation scalar. -/
structure FirstBinarySchurEntry (K : Type*) [Field K] where
  scale : K
  block : BinarySchurBlock K
  scale_ne_zero : scale ≠ 0
  block_nonzero : block.Nonzero

namespace FirstBinarySchurEntry

/-- The actual coefficient represented by a normalised first entry. -/
def coefficient (e : FirstBinarySchurEntry K) : BinarySchurBlock K :=
  e.block.scale e.scale

/-- Determinant core of the represented first coefficient. -/
theorem coefficient_detCore
    (e : FirstBinarySchurEntry K) :
    e.coefficient.detCore = e.scale ^ 2 * e.block.detCore := by
  exact BinarySchurBlock.detCore_scale e.scale e.block

/-- A determinant-zero first coefficient has the binary rank-one pivot
certificate needed by the rank-two branch. -/
theorem pivot_of_coefficient_detCore_eq_zero
    (e : FirstBinarySchurEntry K)
    (hdet : e.coefficient.detCore = 0) :
    e.block.LeftPivot ∨ e.block.RightAxisPivot := by
  exact e.block.pivot_of_scaled_detCore_eq_zero
    e.scale e.scale_ne_zero e.block_nonzero hdet

end FirstBinarySchurEntry

end

end HC4.Newton
