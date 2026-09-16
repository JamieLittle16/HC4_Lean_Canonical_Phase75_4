import HC4.Valuation.SingularFirstKernelBreakRankTwo
import Mathlib.Tactic

/-!
# Canonical selector for the first singular kernel-row break

Given a polynomial four-block whose kernel row has zero constant coefficient
but is not identically zero, the first nonzero row coefficient is selected by
`Nat.find`.  This supplies exactly the lower-vanishing and positive-order data
required by `SingularFirstKernelBreakFourBlockData`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

/-- Some entry in the fourth row/column of the symmetric four-block is nonzero
at parameter order `n`. -/
def fourBlockKernelRowBreakAt
    (B : GeneralFourBlock (Polynomial R)) (n : ℕ) : Prop :=
  B.q.coeff n ≠ 0 ∨
    B.s.coeff n ≠ 0 ∨
    B.y.coeff n ≠ 0 ∨
    B.z.coeff n ≠ 0

/-- A nonzero kernel-row series has a coefficient order at which it breaks. -/
theorem exists_fourBlockKernelRowBreakAt
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0) :
    ∃ n : ℕ, fourBlockKernelRowBreakAt B n := by
  rcases hrow with hq | hs | hy | hz
  · rcases Polynomial.support_nonempty.mpr hq with ⟨n, hn⟩
    exact ⟨n, Or.inl (Polynomial.mem_support_iff.mp hn)⟩
  · rcases Polynomial.support_nonempty.mpr hs with ⟨n, hn⟩
    exact ⟨n, Or.inr (Or.inl (Polynomial.mem_support_iff.mp hn))⟩
  · rcases Polynomial.support_nonempty.mpr hy with ⟨n, hn⟩
    exact ⟨n, Or.inr (Or.inr (Or.inl (Polynomial.mem_support_iff.mp hn)))⟩
  · rcases Polynomial.support_nonempty.mpr hz with ⟨n, hn⟩
    exact ⟨n, Or.inr (Or.inr (Or.inr (Polynomial.mem_support_iff.mp hn)))⟩

/-- Least parameter order at which some kernel-row entry is nonzero. -/
noncomputable def firstFourBlockKernelRowBreakOrder
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0) : ℕ :=
  Nat.find (exists_fourBlockKernelRowBreakAt B hrow)

/-- The least selected order really breaks the row. -/
theorem firstFourBlockKernelRowBreakOrder_spec
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0) :
    fourBlockKernelRowBreakAt B
      (firstFourBlockKernelRowBreakOrder B hrow) := by
  exact Nat.find_spec (exists_fourBlockKernelRowBreakAt B hrow)

/-- Every strictly lower coefficient of every kernel-row entry vanishes. -/
theorem firstFourBlockKernelRowBreakOrder_lower_zero
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0)
    {n : ℕ}
    (hn : n < firstFourBlockKernelRowBreakOrder B hrow) :
    B.q.coeff n = 0 ∧
      B.s.coeff n = 0 ∧
      B.y.coeff n = 0 ∧
      B.z.coeff n = 0 := by
  have hnot : ¬ fourBlockKernelRowBreakAt B n :=
    Nat.find_min (exists_fourBlockKernelRowBreakAt B hrow) hn
  push_neg at hnot
  exact hnot

/-- If the constant kernel row is zero, the first break order is positive. -/
theorem firstFourBlockKernelRowBreakOrder_pos
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0)
    (hq0 : B.q.coeff 0 = 0)
    (hs0 : B.s.coeff 0 = 0)
    (hy0 : B.y.coeff 0 = 0)
    (hz0 : B.z.coeff 0 = 0) :
    0 < firstFourBlockKernelRowBreakOrder B hrow := by
  by_contra hnot
  have hzero : firstFourBlockKernelRowBreakOrder B hrow = 0 := Nat.eq_zero_of_not_pos hnot
  have hbreak := firstFourBlockKernelRowBreakOrder_spec B hrow
  rw [hzero] at hbreak
  simp [fourBlockKernelRowBreakAt, hq0, hs0, hy0, hz0] at hbreak

/-- Package the least row break into the exact singular first-break structure. -/
noncomputable def singularFirstKernelBreakData_of_kernelRow
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0)
    (hq0 : B.q.coeff 0 = 0)
    (hs0 : B.s.coeff 0 = 0)
    (hy0 : B.y.coeff 0 = 0)
    (hz0 : B.z.coeff 0 = 0)
    (hactive : (firstKernelBreakActiveThreeDet B).coeff 0 ≠ 0)
    (hdet : B.determinantCore = 0) :
    SingularFirstKernelBreakFourBlockData R := by
  let j := firstFourBlockKernelRowBreakOrder B hrow
  have hjpos : 0 < j := by
    dsimp [j]
    exact firstFourBlockKernelRowBreakOrder_pos B hrow hq0 hs0 hy0 hz0
  have hlower :
      ∀ n : ℕ, n < j →
        B.q.coeff n = 0 ∧ B.s.coeff n = 0 ∧
          B.y.coeff n = 0 ∧ B.z.coeff n = 0 := by
    intro n hn
    exact firstFourBlockKernelRowBreakOrder_lower_zero B hrow hn
  exact {
    block := B
    order := j
    order_pos := hjpos
    q_lower_zero := fun n hn => (hlower n hn).1
    s_lower_zero := fun n hn => (hlower n hn).2.1
    y_lower_zero := fun n hn => (hlower n hn).2.2.1
    z_lower_zero := fun n hn => (hlower n hn).2.2.2
    activeThree_coeff_zero_ne_zero := hactive
    determinantCore_eq_zero := hdet
    kernel_break := by
      dsimp [j]
      exact firstFourBlockKernelRowBreakOrder_spec B hrow
  }

end

end HC4.Valuation
