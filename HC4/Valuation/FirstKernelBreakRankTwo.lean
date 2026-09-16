import HC4.Newton.FirstSchurLayerLinearization
import HC4.Valuation.SmithFrontierFourBlockExtraction
import Mathlib.Tactic

/-!
# First preclosing kernel break gives rank-two geometry

This file isolates the finite polynomial-series calculation needed by the
A19 same-carrier codimension-two branch.

Work with a symmetric `4 x 4` Hessian series in the canonical
`GeneralFourBlock` coordinates

    [ a  b  p  q ]
    [ b  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ].

Assume the fourth coordinate is a constant Hessian-kernel direction through
all parameter orders below a positive order `j`.  Thus the four entries
`q,s,y,z` have zero coefficients below `j`.  No restriction is imposed on
the positive coefficients of the complementary `3 x 3` block.

At order `j` the determinant linearises exactly as

    [tau^j] det(H) = det(H_012(0)) * z_j.

All terms involving a mixed fourth-coordinate entry contain at least two of
`q,s,y`, hence start at order at least `2j`.  Therefore, if the full
determinant closes at a strictly later order and the constant complementary
`3 x 3` determinant is nonzero, then `z_j = 0`.  If `j` is an actual kernel
break, one of `q_j,s_j,y_j` is nonzero and the corresponding principal
`2 x 2` coefficient-layer minor is the nonzero negative square

    -q_j^2, -s_j^2, or -y_j^2.

The conclusion retains the concrete nonzero minor.  It does not attach a
repair transition and does not identify this parameter clock with any Smith
or blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

/-- Determinant of the complementary `0,1,2` block of a general four-block. -/
def firstKernelBreakActiveThreeDet
    (H : GeneralFourBlock (Polynomial R)) : Polynomial R :=
  H.a * H.d * H.x -
    H.a * H.r * H.r -
    H.b * H.b * H.x +
    2 * H.b * H.p * H.r -
    H.d * H.p * H.p

/-- The explicit four-block determinant, grouped into the term linear in the
kernel diagonal entry `z` plus terms containing at least two mixed
fourth-coordinate entries. -/
theorem determinantCore_eq_activeThreeDet_mul_z_add_kernelPairs
    (H : GeneralFourBlock (Polynomial R)) :
    H.determinantCore =
      firstKernelBreakActiveThreeDet H * H.z
      - (H.a * H.d) * (H.y * H.y)
      + (2 * H.a * H.r) * (H.s * H.y)
      - (H.a * H.x) * (H.s * H.s)
      + (H.b * H.b) * (H.y * H.y)
      - (2 * H.b * H.p) * (H.s * H.y)
      - (2 * H.b * H.r) * (H.q * H.y)
      + (2 * H.b * H.x) * (H.q * H.s)
      + (2 * H.d * H.p) * (H.q * H.y)
      - (H.d * H.x) * (H.q * H.q)
      + (H.p * H.p) * (H.s * H.s)
      - (2 * H.p * H.r) * (H.q * H.s)
      + (H.r * H.r) * (H.q * H.q) := by
  unfold GeneralFourBlock.determinantCore firstKernelBreakActiveThreeDet
  ring

/-- If two parameter series both vanish below a positive order `j`, their
product vanishes through order `j`. -/
theorem coeff_kernelPair_eq_zero_through
    (B C : Polynomial R)
    {j : ℕ}
    (hj : 0 < j)
    (hB : ∀ n : ℕ, n < j → B.coeff n = 0)
    (hC : ∀ n : ℕ, n < j → C.coeff n = 0) :
    ∀ n : ℕ, n ≤ j → (B * C).coeff n = 0 := by
  intro n hn
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  have hsum : u.1 + u.2 = n := Finset.mem_antidiagonal.mp hu
  have hsmall : u.1 < j ∨ u.2 < j := by
    omega
  rcases hsmall with hleft | hright
  · rw [hB u.1 hleft]
    simp
  · rw [hC u.2 hright]
    simp

/-- Multiplying a pair of first-breaking kernel entries by arbitrary active
series cannot create a coefficient at the first break order. -/
theorem coeff_active_mul_kernelPair_eq_zero
    (A B C : Polynomial R)
    {j : ℕ}
    (hj : 0 < j)
    (hB : ∀ n : ℕ, n < j → B.coeff n = 0)
    (hC : ∀ n : ℕ, n < j → C.coeff n = 0) :
    (A * (B * C)).coeff j = 0 := by
  apply coeff_mul_eq_zero_of_right_vanishes_through
  intro n hn
  exact coeff_kernelPair_eq_zero_through B C hj hB hC n hn

/-- Exact data of a first break of the fourth constant kernel direction in a
polynomial four-block whose determinant closes later. -/
structure FirstKernelBreakFourBlockData
    (R : Type*) [CommRing R] where
  block : GeneralFourBlock (Polynomial R)
  order : ℕ
  defect : ℕ
  order_pos : 0 < order
  order_lt_defect : order < defect
  q_lower_zero : ∀ n : ℕ, n < order → block.q.coeff n = 0
  s_lower_zero : ∀ n : ℕ, n < order → block.s.coeff n = 0
  y_lower_zero : ∀ n : ℕ, n < order → block.y.coeff n = 0
  z_lower_zero : ∀ n : ℕ, n < order → block.z.coeff n = 0
  activeThree_coeff_zero_ne_zero :
    (firstKernelBreakActiveThreeDet block).coeff 0 ≠ 0
  determinantCore_eq : block.determinantCore = Polynomial.X ^ defect
  kernel_break :
    block.q.coeff order ≠ 0 ∨
      block.s.coeff order ≠ 0 ∨
      block.y.coeff order ≠ 0 ∨
      block.z.coeff order ≠ 0

namespace FirstKernelBreakFourBlockData

variable (E : FirstKernelBreakFourBlockData R)

/-- The first-break determinant coefficient only sees the constant
complementary `3 x 3` determinant and the first kernel-diagonal coefficient. -/
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

/-- Strictly before determinant closure, the first kernel-diagonal coefficient
must still vanish. -/
theorem kernelDiagonal_coeff_order_eq_zero
    [NoZeroDivisors R] :
    E.block.z.coeff E.order = 0 := by
  have hdetzero : E.block.determinantCore.coeff E.order = 0 := by
    rw [E.determinantCore_eq]
    simp [Polynomial.coeff_X_pow, Nat.ne_of_lt E.order_lt_defect]
  have hmul :
      (firstKernelBreakActiveThreeDet E.block).coeff 0 *
          E.block.z.coeff E.order = 0 := by
    rw [← E.determinantCore_coeff_order]
    exact hdetzero
  rcases mul_eq_zero.mp hmul with hactive | hz
  · exact (E.activeThree_coeff_zero_ne_zero hactive).elim
  · exact hz

/-- The first actual break is therefore mixed: one of the three mixed
fourth-coordinate entries is nonzero. -/
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

/-- The coefficient matrix at the first kernel break has an explicit nonzero
principal `2 x 2` minor.  The three alternatives correspond to coordinates
`0,1,2` against the kernel coordinate `3`. -/
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

end FirstKernelBreakFourBlockData

end

end HC4.Valuation
