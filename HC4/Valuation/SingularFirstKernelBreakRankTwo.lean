import HC4.Valuation.FirstKernelBreakRankTwo
import Mathlib.Tactic

/-!
# Singular first kernel break gives rank-two geometry

`FirstKernelBreakRankTwo` treats a family whose determinant closes at a later
positive parameter order.  The A19.55 codimension-two carrier has an even
cleaner deformation: the exact initial-form chain stays Hessian-singular, so
the determinant of the honest interpolating family is identically zero.

This file records the corresponding first-break algebra without introducing a
fake defect clock.  If coordinate `3` is a constant Hessian kernel through all
orders below a positive first break `j`, the complementary `0,1,2` Hessian
block is nondegenerate at order zero, and the full determinant is identically
zero, then the first kernel diagonal coefficient vanishes.  Hence an actual
kernel break is mixed and gives a concrete nonzero principal `2 x 2` minor at
that coefficient layer.

No Smith clock, blocker clock, repair tag, or valuation state occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

/-- Exact polynomial-series data for the first break of a constant kernel in
an identically Hessian-singular family. -/
structure SingularFirstKernelBreakFourBlockData
    (R : Type*) [CommRing R] where
  block : GeneralFourBlock (Polynomial R)
  order : ℕ
  order_pos : 0 < order
  q_lower_zero : ∀ n : ℕ, n < order → block.q.coeff n = 0
  s_lower_zero : ∀ n : ℕ, n < order → block.s.coeff n = 0
  y_lower_zero : ∀ n : ℕ, n < order → block.y.coeff n = 0
  z_lower_zero : ∀ n : ℕ, n < order → block.z.coeff n = 0
  activeThree_coeff_zero_ne_zero :
    (firstKernelBreakActiveThreeDet block).coeff 0 ≠ 0
  determinantCore_eq_zero : block.determinantCore = 0
  kernel_break :
    block.q.coeff order ≠ 0 ∨
      block.s.coeff order ≠ 0 ∨
      block.y.coeff order ≠ 0 ∨
      block.z.coeff order ≠ 0

namespace SingularFirstKernelBreakFourBlockData

variable (E : SingularFirstKernelBreakFourBlockData R)

/-- At the first kernel break, all quadratic kernel-entry terms still vanish;
only the active `3 x 3` determinant times the kernel diagonal can contribute. -/
theorem determinantCore_coeff_order :
    E.block.determinantCore.coeff E.order =
      (firstKernelBreakActiveThreeDet E.block).coeff 0 *
        E.block.z.coeff E.order := by
  rw [determinantCore_eq_activeThreeDet_mul_z_add_kernelPairs]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
  rw [coeff_mul_eq_constant_mul_of_right_vanishes_below
      (firstKernelBreakActiveThreeDet E.block) E.block.z E.z_lower_zero]

  have hyy1 :
      ((E.block.a * E.block.d) * (E.block.y * E.block.y)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (E.block.a * E.block.d) E.block.y E.block.y
      E.order_pos E.y_lower_zero E.y_lower_zero
  have hsy1 :
      ((2 * E.block.a * E.block.r) * (E.block.s * E.block.y)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (2 * E.block.a * E.block.r) E.block.s E.block.y
      E.order_pos E.s_lower_zero E.y_lower_zero
  have hss1 :
      ((E.block.a * E.block.x) * (E.block.s * E.block.s)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (E.block.a * E.block.x) E.block.s E.block.s
      E.order_pos E.s_lower_zero E.s_lower_zero
  have hyy2 :
      ((E.block.b * E.block.b) * (E.block.y * E.block.y)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (E.block.b * E.block.b) E.block.y E.block.y
      E.order_pos E.y_lower_zero E.y_lower_zero
  have hsy2 :
      ((2 * E.block.b * E.block.p) * (E.block.s * E.block.y)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (2 * E.block.b * E.block.p) E.block.s E.block.y
      E.order_pos E.s_lower_zero E.y_lower_zero
  have hqy1 :
      ((2 * E.block.b * E.block.r) * (E.block.q * E.block.y)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (2 * E.block.b * E.block.r) E.block.q E.block.y
      E.order_pos E.q_lower_zero E.y_lower_zero
  have hqs1 :
      ((2 * E.block.b * E.block.x) * (E.block.q * E.block.s)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (2 * E.block.b * E.block.x) E.block.q E.block.s
      E.order_pos E.q_lower_zero E.s_lower_zero
  have hqy2 :
      ((2 * E.block.d * E.block.p) * (E.block.q * E.block.y)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (2 * E.block.d * E.block.p) E.block.q E.block.y
      E.order_pos E.q_lower_zero E.y_lower_zero
  have hqq1 :
      ((E.block.d * E.block.x) * (E.block.q * E.block.q)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (E.block.d * E.block.x) E.block.q E.block.q
      E.order_pos E.q_lower_zero E.q_lower_zero
  have hss2 :
      ((E.block.p * E.block.p) * (E.block.s * E.block.s)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (E.block.p * E.block.p) E.block.s E.block.s
      E.order_pos E.s_lower_zero E.s_lower_zero
  have hqs2 :
      ((2 * E.block.p * E.block.r) * (E.block.q * E.block.s)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (2 * E.block.p * E.block.r) E.block.q E.block.s
      E.order_pos E.q_lower_zero E.s_lower_zero
  have hqq2 :
      ((E.block.r * E.block.r) * (E.block.q * E.block.q)).coeff E.order = 0 := by
    exact coeff_active_mul_kernelPair_eq_zero
      (E.block.r * E.block.r) E.block.q E.block.q
      E.order_pos E.q_lower_zero E.q_lower_zero

  rw [hyy1, hsy1, hss1, hyy2, hsy2, hqy1, hqs1, hqy2,
    hqq1, hss2, hqs2, hqq2]
  ring

/-- In an identically singular family the first kernel-diagonal coefficient
must vanish, provided the complementary active `3 x 3` block is nondegenerate
at the special fibre. -/
theorem kernelDiagonal_coeff_order_eq_zero
    [NoZeroDivisors R] :
    E.block.z.coeff E.order = 0 := by
  have hdetzero : E.block.determinantCore.coeff E.order = 0 := by
    rw [E.determinantCore_eq_zero]
    simp
  have hmul :
      (firstKernelBreakActiveThreeDet E.block).coeff 0 *
          E.block.z.coeff E.order = 0 := by
    rw [← E.determinantCore_coeff_order]
    exact hdetzero
  rcases mul_eq_zero.mp hmul with hactive | hz
  · exact (E.activeThree_coeff_zero_ne_zero hactive).elim
  · exact hz

/-- Therefore an actual first break is mixed: at least one mixed kernel entry
is nonzero at the first break order. -/
theorem mixed_coeff_ne_zero
    [NoZeroDivisors R] :
    E.block.q.coeff E.order ≠ 0 ∨
      E.block.s.coeff E.order ≠ 0 ∨
      E.block.y.coeff E.order ≠ 0 := by
  have hz := E.kernelDiagonal_coeff_order_eq_zero
  rcases E.kernel_break with hq | hs | hy | hdiag
  · exact Or.inl hq
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr hy)
  · exact (hdiag hz).elim

/-- **Singular first-kernel-break rank-two geometry.**  The coefficient matrix
at the first actual opening has an explicit nonzero principal `2 x 2` minor. -/
theorem exists_nonzero_principalMinor_at_order
    [NoZeroDivisors R] :
    (E.block.a.coeff E.order * E.block.z.coeff E.order -
        E.block.q.coeff E.order * E.block.q.coeff E.order ≠ 0) ∨
    (E.block.d.coeff E.order * E.block.z.coeff E.order -
        E.block.s.coeff E.order * E.block.s.coeff E.order ≠ 0) ∨
    (E.block.x.coeff E.order * E.block.z.coeff E.order -
        E.block.y.coeff E.order * E.block.y.coeff E.order ≠ 0) := by
  have hz := E.kernelDiagonal_coeff_order_eq_zero
  rcases E.mixed_coeff_ne_zero with hq | hs | hy
  · left
    rw [hz]
    simpa using neg_ne_zero.mpr (mul_ne_zero hq hq)
  · right
    left
    rw [hz]
    simpa using neg_ne_zero.mpr (mul_ne_zero hs hs)
  · right
    right
    rw [hz]
    simpa using neg_ne_zero.mpr (mul_ne_zero hy hy)

end SingularFirstKernelBreakFourBlockData

end

end HC4.Valuation
