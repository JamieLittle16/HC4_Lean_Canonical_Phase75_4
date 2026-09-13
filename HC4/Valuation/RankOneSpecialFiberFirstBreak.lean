import HC4.Valuation.SingularFirstKernelBreakSelector
import Mathlib.Tactic

/-!
# First kernel-row break from a rank-one special fibre

The existing first-break theorem assumes the complementary `3 x 3` block is
nondegenerate at the special fibre.  The A19.55 degenerate coordinate-max leaf
has the opposite geometry: its special fibre is a pure coordinate power, so
its Hessian has one nonzero active diagonal entry and rank one.

For that situation no determinant expansion is needed.

Let `j > 0` be the first parameter order at which the kernel row
`q,s,y,z` opens.

* If `z_j != 0`, any nonzero active diagonal constant coefficient pairs with
  it to give a nonzero coefficient of one of the family principal minors
  `a z - q^2`, `d z - s^2`, `x z - y^2`.  The square term cannot contribute at
  order `j` because the corresponding kernel entry vanishes below `j`.
* If `z_j = 0`, the row break is mixed.  The corresponding principal minor of
  the coefficient matrix at order `j` is the nonzero negative square
  `-q_j^2`, `-s_j^2`, or `-y_j^2`.

Thus a rank-one special fibre plus a genuine kernel-row opening always carries
concrete rank-two geometry, either across two parameter layers or already in
the first breaking layer.  No determinant defect, Smith clock, or repair tag
is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- Concrete rank-two geometry at the first kernel-row break from a special
fibre with some nonzero active diagonal entry. -/
inductive RankOneSpecialFiberFirstBreakOutcome
    (B : GeneralFourBlock (Polynomial R))
    (j : ℕ) : Prop
  | familyMinor
      (h :
        (B.a * B.z - B.q * B.q).coeff j ≠ 0 ∨
        (B.d * B.z - B.s * B.s).coeff j ≠ 0 ∨
        (B.x * B.z - B.y * B.y).coeff j ≠ 0)
  | layerMinor
      (h :
        B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j ≠ 0 ∨
        B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j ≠ 0 ∨
        B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j ≠ 0)

/-- **Rank-one-special-fibre first-break theorem.** -/
theorem rankOneSpecialFiber_firstKernelRowBreak_rankTwo
    (B : GeneralFourBlock (Polynomial R))
    (hrow : B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0)
    (hq0 : B.q.coeff 0 = 0)
    (hs0 : B.s.coeff 0 = 0)
    (hy0 : B.y.coeff 0 = 0)
    (hz0 : B.z.coeff 0 = 0)
    (hactiveDiag :
      B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0) :
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  let j := firstFourBlockKernelRowBreakOrder B hrow
  have hjpos : 0 < j := by
    dsimp [j]
    exact firstFourBlockKernelRowBreakOrder_pos B hrow hq0 hs0 hy0 hz0
  have hlower :
      ∀ n : ℕ, n < j →
        B.q.coeff n = 0 ∧ B.s.coeff n = 0 ∧
          B.y.coeff n = 0 ∧ B.z.coeff n = 0 := by
    intro n hn
    dsimp [j] at hn ⊢
    exact firstFourBlockKernelRowBreakOrder_lower_zero B hrow hn
  have hqLower : ∀ n : ℕ, n < j → B.q.coeff n = 0 :=
    fun n hn => (hlower n hn).1
  have hsLower : ∀ n : ℕ, n < j → B.s.coeff n = 0 :=
    fun n hn => (hlower n hn).2.1
  have hyLower : ∀ n : ℕ, n < j → B.y.coeff n = 0 :=
    fun n hn => (hlower n hn).2.2.1
  have hzLower : ∀ n : ℕ, n < j → B.z.coeff n = 0 :=
    fun n hn => (hlower n hn).2.2.2
  have hbreak : fourBlockKernelRowBreakAt B j := by
    dsimp [j]
    exact firstFourBlockKernelRowBreakOrder_spec B hrow

  by_cases hzj : B.z.coeff j = 0
  · have hmixed :
        B.q.coeff j ≠ 0 ∨ B.s.coeff j ≠ 0 ∨ B.y.coeff j ≠ 0 := by
      rcases hbreak with hq | hs | hy | hz
      · exact Or.inl hq
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr hy)
      · exact (hz hzj).elim
    apply RankOneSpecialFiberFirstBreakOutcome.layerMinor
    rcases hmixed with hq | hs | hy
    · exact Or.inl (by
        rw [hzj]
        simpa using neg_ne_zero.mpr (mul_ne_zero hq hq))
    · exact Or.inr (Or.inl (by
        rw [hzj]
        simpa using neg_ne_zero.mpr (mul_ne_zero hs hs)))
    · exact Or.inr (Or.inr (by
        rw [hzj]
        simpa using neg_ne_zero.mpr (mul_ne_zero hy hy)))
  · have hqSq : (B.q * B.q).coeff j = 0 :=
      coeff_kernelPair_eq_zero_through B.q B.q hjpos hqLower hqLower j le_rfl
    have hsSq : (B.s * B.s).coeff j = 0 :=
      coeff_kernelPair_eq_zero_through B.s B.s hjpos hsLower hsLower j le_rfl
    have hySq : (B.y * B.y).coeff j = 0 :=
      coeff_kernelPair_eq_zero_through B.y B.y hjpos hyLower hyLower j le_rfl
    have haz : (B.a * B.z).coeff j = B.a.coeff 0 * B.z.coeff j :=
      coeff_mul_eq_constant_mul_of_right_vanishes_below B.a B.z hzLower
    have hdz : (B.d * B.z).coeff j = B.d.coeff 0 * B.z.coeff j :=
      coeff_mul_eq_constant_mul_of_right_vanishes_below B.d B.z hzLower
    have hxz : (B.x * B.z).coeff j = B.x.coeff 0 * B.z.coeff j :=
      coeff_mul_eq_constant_mul_of_right_vanishes_below B.x B.z hzLower
    apply RankOneSpecialFiberFirstBreakOutcome.familyMinor
    rcases hactiveDiag with ha | hd | hx
    · left
      rw [Polynomial.coeff_sub, haz, hqSq]
      simpa using mul_ne_zero ha hzj
    · right
      left
      rw [Polynomial.coeff_sub, hdz, hsSq]
      simpa using mul_ne_zero hd hzj
    · right
      right
      rw [Polynomial.coeff_sub, hxz, hySq]
      simpa using mul_ne_zero hx hzj

end

end HC4.Valuation
