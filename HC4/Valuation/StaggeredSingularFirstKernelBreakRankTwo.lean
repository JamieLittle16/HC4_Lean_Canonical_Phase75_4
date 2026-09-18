
import HC4.Valuation.SingularFirstKernelBreakRankTwo
import Mathlib.Tactic

/-!
# Staggered singular first-kernel break

The central finite-staircase family does not begin with a rank-three special
fibre. Its complementary three-by-three Hessian minor first becomes nonzero
at a positive parameter order q, while the remaining kernel row first opens
at a later order j > q.

If the active three-by-three determinant vanishes below q and is nonzero at q,
the fourth row vanishes below j, q < j, and the full determinant is identically
zero, then the fourth diagonal coefficient at j vanishes. At order q+j the
only possible linear contribution is activeThree_q * z_j, while all quadratic
kernel-row terms begin at order at least 2j.

Hence the first fourth-row opening is mixed and carries a concrete nonzero
principal two-by-two coefficient-layer minor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

theorem coeff_mul_eq_leading_mul_of_lower_zero
    (A C : Polynomial R)
    {q j : ℕ}
    (hA : ∀ n : ℕ, n < q → A.coeff n = 0)
    (hC : ∀ n : ℕ, n < j → C.coeff n = 0) :
    (A * C).coeff (q + j) =
      A.coeff q * C.coeff j := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (q, j)
  · intro x hx hne
    have hsum : x.1 + x.2 = q + j :=
      Finset.mem_antidiagonal.mp hx
    by_cases hxq : x.1 < q
    · rw [hA x.1 hxq]
      simp
    · by_cases hxj : x.2 < j
      · rw [hC x.2 hxj]
        simp
      · have hx1 : q ≤ x.1 := Nat.le_of_not_gt hxq
        have hx2 : j ≤ x.2 := Nat.le_of_not_gt hxj
        have heq1 : x.1 = q := by omega
        have heq2 : x.2 = j := by omega
        exact (hne (Prod.ext heq1 heq2)).elim
  · intro hnot
    have hmem : (q, j) ∈ Finset.antidiagonal (q + j) := by
      rw [Finset.mem_antidiagonal]
    exact (hnot hmem).elim

theorem coeff_kernelPair_eq_zero_before_double
    (B C : Polynomial R)
    {j n : ℕ}
    (hn : n < 2 * j)
    (hB : ∀ r : ℕ, r < j → B.coeff r = 0)
    (hC : ∀ r : ℕ, r < j → C.coeff r = 0) :
    (B * C).coeff n = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = n :=
    Finset.mem_antidiagonal.mp hx
  have hsmall : x.1 < j ∨ x.2 < j := by
    by_contra hnot
    push_neg at hnot
    omega
  rcases hsmall with hleft | hright
  · rw [hB x.1 hleft]
    simp
  · rw [hC x.2 hright]
    simp

structure StaggeredSingularFirstKernelBreakFourBlockData
    (R : Type*) [CommRing R] where
  block : GeneralFourBlock (Polynomial R)
  activeOrder : ℕ
  kernelOrder : ℕ
  activeOrder_pos : 0 < activeOrder
  active_lt_kernel : activeOrder < kernelOrder
  active_lower_zero :
    ∀ n : ℕ, n < activeOrder →
      (firstKernelBreakActiveThreeDet block).coeff n = 0
  active_coeff_ne_zero :
    (firstKernelBreakActiveThreeDet block).coeff activeOrder ≠ 0
  q_lower_zero :
    ∀ n : ℕ, n < kernelOrder → block.q.coeff n = 0
  s_lower_zero :
    ∀ n : ℕ, n < kernelOrder → block.s.coeff n = 0
  y_lower_zero :
    ∀ n : ℕ, n < kernelOrder → block.y.coeff n = 0
  z_lower_zero :
    ∀ n : ℕ, n < kernelOrder → block.z.coeff n = 0
  determinantCore_eq_zero : block.determinantCore = 0
  kernel_break :
    block.q.coeff kernelOrder ≠ 0 ∨
      block.s.coeff kernelOrder ≠ 0 ∨
      block.y.coeff kernelOrder ≠ 0 ∨
      block.z.coeff kernelOrder ≠ 0

namespace StaggeredSingularFirstKernelBreakFourBlockData

variable (E : StaggeredSingularFirstKernelBreakFourBlockData R)

private theorem active_mul_z_coeff :
    (firstKernelBreakActiveThreeDet E.block * E.block.z).coeff
        (E.activeOrder + E.kernelOrder) =
      (firstKernelBreakActiveThreeDet E.block).coeff E.activeOrder *
        E.block.z.coeff E.kernelOrder := by
  exact coeff_mul_eq_leading_mul_of_lower_zero
    (firstKernelBreakActiveThreeDet E.block) E.block.z
    E.active_lower_zero E.z_lower_zero

private theorem active_mul_kernelPair_coeff_zero
    (A B C : Polynomial R)
    (hB : ∀ n : ℕ, n < E.kernelOrder → B.coeff n = 0)
    (hC : ∀ n : ℕ, n < E.kernelOrder → C.coeff n = 0) :
    (A * (B * C)).coeff
        (E.activeOrder + E.kernelOrder) = 0 := by
  apply coeff_mul_eq_zero_of_right_vanishes_through
  intro n hn
  apply coeff_kernelPair_eq_zero_before_double B C
  · omega
  · exact hB
  · exact hC

theorem kernelDiagonal_coeff_kernelOrder_eq_zero
    [NoZeroDivisors R] :
    E.block.z.coeff E.kernelOrder = 0 := by
  have hdetCoeff :
      E.block.determinantCore.coeff
          (E.activeOrder + E.kernelOrder) = 0 := by
    rw [E.determinantCore_eq_zero]
    simp
  rw [determinantCore_eq_activeThreeDet_mul_z_add_kernelPairs] at hdetCoeff
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub] at hdetCoeff
  rw [E.active_mul_z_coeff] at hdetCoeff

  have hyy1 :
      ((E.block.a * E.block.d) * (E.block.y * E.block.y)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (E.block.a * E.block.d) E.block.y E.block.y
      E.y_lower_zero E.y_lower_zero
  have hsy1 :
      ((2 * E.block.a * E.block.r) * (E.block.s * E.block.y)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (2 * E.block.a * E.block.r) E.block.s E.block.y
      E.s_lower_zero E.y_lower_zero
  have hss1 :
      ((E.block.a * E.block.x) * (E.block.s * E.block.s)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (E.block.a * E.block.x) E.block.s E.block.s
      E.s_lower_zero E.s_lower_zero
  have hyy2 :
      ((E.block.b * E.block.b) * (E.block.y * E.block.y)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (E.block.b * E.block.b) E.block.y E.block.y
      E.y_lower_zero E.y_lower_zero
  have hsy2 :
      ((2 * E.block.b * E.block.p) * (E.block.s * E.block.y)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (2 * E.block.b * E.block.p) E.block.s E.block.y
      E.s_lower_zero E.y_lower_zero
  have hqy1 :
      ((2 * E.block.b * E.block.r) * (E.block.q * E.block.y)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (2 * E.block.b * E.block.r) E.block.q E.block.y
      E.q_lower_zero E.y_lower_zero
  have hqs1 :
      ((2 * E.block.b * E.block.x) * (E.block.q * E.block.s)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (2 * E.block.b * E.block.x) E.block.q E.block.s
      E.q_lower_zero E.s_lower_zero
  have hqy2 :
      ((2 * E.block.d * E.block.p) * (E.block.q * E.block.y)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (2 * E.block.d * E.block.p) E.block.q E.block.y
      E.q_lower_zero E.y_lower_zero
  have hqq1 :
      ((E.block.d * E.block.x) * (E.block.q * E.block.q)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (E.block.d * E.block.x) E.block.q E.block.q
      E.q_lower_zero E.q_lower_zero
  have hss2 :
      ((E.block.p * E.block.p) * (E.block.s * E.block.s)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (E.block.p * E.block.p) E.block.s E.block.s
      E.s_lower_zero E.s_lower_zero
  have hqs2 :
      ((2 * E.block.p * E.block.r) * (E.block.q * E.block.s)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (2 * E.block.p * E.block.r) E.block.q E.block.s
      E.q_lower_zero E.s_lower_zero
  have hqq2 :
      ((E.block.r * E.block.r) * (E.block.q * E.block.q)).coeff
          (E.activeOrder + E.kernelOrder) = 0 :=
    E.active_mul_kernelPair_coeff_zero
      (E.block.r * E.block.r) E.block.q E.block.q
      E.q_lower_zero E.q_lower_zero

  rw [hyy1, hsy1, hss1, hyy2, hsy2, hqy1, hqs1, hqy2,
    hqq1, hss2, hqs2, hqq2] at hdetCoeff
  ring_nf at hdetCoeff
  exact
    (mul_eq_zero.mp hdetCoeff).resolve_left E.active_coeff_ne_zero

theorem mixed_coeff_ne_zero
    [NoZeroDivisors R] :
    E.block.q.coeff E.kernelOrder ≠ 0 ∨
      E.block.s.coeff E.kernelOrder ≠ 0 ∨
      E.block.y.coeff E.kernelOrder ≠ 0 := by
  have hz := E.kernelDiagonal_coeff_kernelOrder_eq_zero
  rcases E.kernel_break with hq | hs | hy | hdiag
  · exact Or.inl hq
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr hy)
  · exact (hdiag hz).elim

theorem exists_nonzero_principalMinor_at_kernelOrder
    [NoZeroDivisors R] :
    (E.block.a.coeff E.kernelOrder * E.block.z.coeff E.kernelOrder -
        E.block.q.coeff E.kernelOrder * E.block.q.coeff E.kernelOrder ≠ 0) ∨
    (E.block.d.coeff E.kernelOrder * E.block.z.coeff E.kernelOrder -
        E.block.s.coeff E.kernelOrder * E.block.s.coeff E.kernelOrder ≠ 0) ∨
    (E.block.x.coeff E.kernelOrder * E.block.z.coeff E.kernelOrder -
        E.block.y.coeff E.kernelOrder * E.block.y.coeff E.kernelOrder ≠ 0) := by
  have hz := E.kernelDiagonal_coeff_kernelOrder_eq_zero
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

end StaggeredSingularFirstKernelBreakFourBlockData

end

end HC4.Valuation
