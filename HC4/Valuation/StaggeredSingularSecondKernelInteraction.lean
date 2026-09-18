import HC4.Valuation.StaggeredSingularFirstKernelBreakRankTwo
import Mathlib.Tactic

/-!
# Second interaction after a staggered singular kernel break

Suppose a symmetric four-block has identically zero determinant, its active
three-by-three determinant first becomes nonzero at order `q`, and the
remaining kernel row first opens later at order `j > q`.

The first staggered-break theorem shows that the kernel diagonal still
vanishes at order `j`.  In fact it vanishes for longer: every coefficient
strictly below

    2*j - q

is zero.  Before parameter order `2*j`, all terms quadratic in the mixed
kernel row are still absent, so the determinant coefficient at `q+s`
isolates the leading active determinant coefficient times `z_s`.

At order `2*j` the first quadratic mixed-row interaction appears.  In the
rank-two special-fibre configuration used by A19, the active constant block
has zero middle row/column.  If the middle mixed entry `s_j` is nonzero,
the quadratic contribution is exactly

    -(a₀*x₀ - p₀²) * s_j².

Consequently the zero determinant forces a genuinely nonzero kernel-diagonal
coefficient at the exact order `2*j-q`.

This is state-free polynomial-series algebra.  No Smith clock, repair label,
or source truncation occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

/-- Multiplying a quadratic kernel-row term by an arbitrary active series
cannot create a coefficient before twice the kernel-row opening order. -/
theorem coeff_active_mul_kernelPair_eq_zero_before_double
    (A B C : Polynomial R)
    {j n : ℕ}
    (hn : n < 2 * j)
    (hB : ∀ r : ℕ, r < j → B.coeff r = 0)
    (hC : ∀ r : ℕ, r < j → C.coeff r = 0) :
    (A * (B * C)).coeff n = 0 := by
  apply coeff_mul_eq_zero_of_right_vanishes_through
  intro r hr
  apply coeff_kernelPair_eq_zero_before_double B C
    (j := j) (n := r)
  · exact lt_of_le_of_lt hr hn
  · exact hB
  · exact hC

/-- Before the first quadratic kernel-row interaction, the full determinant
coefficient is just the coefficient of the active-three determinant times the
kernel diagonal. -/
theorem determinantCore_coeff_eq_activeThree_mul_z_before_double
    (H : GeneralFourBlock (Polynomial R))
    {j n : ℕ}
    (hn : n < 2 * j)
    (hq : ∀ r : ℕ, r < j → H.q.coeff r = 0)
    (hs : ∀ r : ℕ, r < j → H.s.coeff r = 0)
    (hy : ∀ r : ℕ, r < j → H.y.coeff r = 0) :
    H.determinantCore.coeff n =
      (firstKernelBreakActiveThreeDet H * H.z).coeff n := by
  rw [determinantCore_eq_activeThreeDet_mul_z_add_kernelPairs]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub]

  have hyy1 :
      ((H.a * H.d) * (H.y * H.y)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (H.a * H.d) H.y H.y hn hy hy
  have hsy1 :
      ((2 * H.a * H.r) * (H.s * H.y)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (2 * H.a * H.r) H.s H.y hn hs hy
  have hss1 :
      ((H.a * H.x) * (H.s * H.s)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (H.a * H.x) H.s H.s hn hs hs
  have hyy2 :
      ((H.b * H.b) * (H.y * H.y)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (H.b * H.b) H.y H.y hn hy hy
  have hsy2 :
      ((2 * H.b * H.p) * (H.s * H.y)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (2 * H.b * H.p) H.s H.y hn hs hy
  have hqy1 :
      ((2 * H.b * H.r) * (H.q * H.y)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (2 * H.b * H.r) H.q H.y hn hq hy
  have hqs1 :
      ((2 * H.b * H.x) * (H.q * H.s)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (2 * H.b * H.x) H.q H.s hn hq hs
  have hqy2 :
      ((2 * H.d * H.p) * (H.q * H.y)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (2 * H.d * H.p) H.q H.y hn hq hy
  have hqq1 :
      ((H.d * H.x) * (H.q * H.q)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (H.d * H.x) H.q H.q hn hq hq
  have hss2 :
      ((H.p * H.p) * (H.s * H.s)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (H.p * H.p) H.s H.s hn hs hs
  have hqs2 :
      ((2 * H.p * H.r) * (H.q * H.s)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (2 * H.p * H.r) H.q H.s hn hq hs
  have hqq2 :
      ((H.r * H.r) * (H.q * H.q)).coeff n = 0 :=
    coeff_active_mul_kernelPair_eq_zero_before_double
      (H.r * H.r) H.q H.q hn hq hq

  rw [hyy1, hsy1, hss1, hyy2, hsy2, hqy1, hqs1, hqy2,
    hqq1, hss2, hqs2, hqq2]
  ring

/-- At the exact double-kernel order, an arbitrary active prefactor only
contributes through its constant coefficient. -/
theorem coeff_active_mul_kernelPair_at_double
    (A B C : Polynomial R)
    {j : ℕ}
    (hB : ∀ r : ℕ, r < j → B.coeff r = 0)
    (hC : ∀ r : ℕ, r < j → C.coeff r = 0) :
    (A * (B * C)).coeff (2 * j) =
      A.coeff 0 * (B.coeff j * C.coeff j) := by
  have hpair :
      ∀ n : ℕ, n < 2 * j → (B * C).coeff n = 0 := by
    intro n hn
    exact coeff_kernelPair_eq_zero_before_double B C hn hB hC
  rw [coeff_mul_eq_constant_mul_of_right_vanishes_below A (B * C) hpair]
  have hlead :=
    coeff_mul_eq_leading_mul_of_lower_zero B C
      (q := j) (j := j) hB hC
  have hsum : j + j = 2 * j := by omega
  rw [hsum] at hlead
  rw [hlead]

/-- Exact determinant coefficient at the first quadratic kernel-row
interaction when the constant active three-block has zero middle row/column. -/
theorem determinantCore_coeff_doubleKernel_of_middleKernelBase
    (H : GeneralFourBlock (Polynomial R))
    {j : ℕ}
    (hq : ∀ r : ℕ, r < j → H.q.coeff r = 0)
    (hs : ∀ r : ℕ, r < j → H.s.coeff r = 0)
    (hy : ∀ r : ℕ, r < j → H.y.coeff r = 0)
    (hb0 : H.b.coeff 0 = 0)
    (hd0 : H.d.coeff 0 = 0)
    (hr0 : H.r.coeff 0 = 0) :
    H.determinantCore.coeff (2 * j) =
      (firstKernelBreakActiveThreeDet H * H.z).coeff (2 * j) -
        (H.a.coeff 0 * H.x.coeff 0 - H.p.coeff 0 * H.p.coeff 0) *
          (H.s.coeff j * H.s.coeff j) := by
  rw [determinantCore_eq_activeThreeDet_mul_z_add_kernelPairs]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub]

  have hyy1 := coeff_active_mul_kernelPair_at_double
    (H.a * H.d) H.y H.y hy hy
  have hsy1 := coeff_active_mul_kernelPair_at_double
    (2 * H.a * H.r) H.s H.y hs hy
  have hss1 := coeff_active_mul_kernelPair_at_double
    (H.a * H.x) H.s H.s hs hs
  have hyy2 := coeff_active_mul_kernelPair_at_double
    (H.b * H.b) H.y H.y hy hy
  have hsy2 := coeff_active_mul_kernelPair_at_double
    (2 * H.b * H.p) H.s H.y hs hy
  have hqy1 := coeff_active_mul_kernelPair_at_double
    (2 * H.b * H.r) H.q H.y hq hy
  have hqs1 := coeff_active_mul_kernelPair_at_double
    (2 * H.b * H.x) H.q H.s hq hs
  have hqy2 := coeff_active_mul_kernelPair_at_double
    (2 * H.d * H.p) H.q H.y hq hy
  have hqq1 := coeff_active_mul_kernelPair_at_double
    (H.d * H.x) H.q H.q hq hq
  have hss2 := coeff_active_mul_kernelPair_at_double
    (H.p * H.p) H.s H.s hs hs
  have hqs2 := coeff_active_mul_kernelPair_at_double
    (2 * H.p * H.r) H.q H.s hq hs
  have hqq2 := coeff_active_mul_kernelPair_at_double
    (H.r * H.r) H.q H.q hq hq

  rw [hyy1, hsy1, hss1, hyy2, hsy2, hqy1, hqs1, hqy2,
    hqq1, hss2, hqs2, hqq2]
  simp [Polynomial.coeff_zero_eq_eval_zero, hb0, hd0, hr0]
  ring

namespace StaggeredSingularFirstKernelBreakFourBlockData

variable (E : StaggeredSingularFirstKernelBreakFourBlockData R)

/-- The missing diagonal cannot open before the first quadratic interaction
between the later kernel row and itself. -/
theorem kernelDiagonal_coeff_eq_zero_before_secondInteraction
    [NoZeroDivisors R] :
    ∀ s : ℕ, s < 2 * E.kernelOrder - E.activeOrder →
      E.block.z.coeff s = 0 := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
      intro hsBound
      by_cases hsKernel : s < E.kernelOrder
      · exact E.z_lower_zero s hsKernel
      · have hzLower :
            ∀ n : ℕ, n < s → E.block.z.coeff n = 0 := by
          intro n hn
          by_cases hnKernel : n < E.kernelOrder
          · exact E.z_lower_zero n hnKernel
          · exact ih n hn (lt_trans hn hsBound)
        have hdegree :
            E.activeOrder + s < 2 * E.kernelOrder := by
          omega
        have hdet :
            E.block.determinantCore.coeff (E.activeOrder + s) = 0 := by
          rw [E.determinantCore_eq_zero]
          simp
        rw [determinantCore_coeff_eq_activeThree_mul_z_before_double
          E.block hdegree E.q_lower_zero E.s_lower_zero E.y_lower_zero] at hdet
        have hlead :=
          coeff_mul_eq_leading_mul_of_lower_zero
            (firstKernelBreakActiveThreeDet E.block) E.block.z
            E.active_lower_zero hzLower
        rw [hlead] at hdet
        exact
          (mul_eq_zero.mp hdet).resolve_left E.active_coeff_ne_zero

/-- If the constant active block has a genuine outer principal minor and the
first mixed opening is the middle entry `s_j`, then the next missing-diagonal
coefficient is forced nonzero at the exact order `2*j-q`. -/
theorem kernelDiagonal_coeff_secondInteraction_ne_zero
    [NoZeroDivisors R]
    (hb0 : E.block.b.coeff 0 = 0)
    (hd0 : E.block.d.coeff 0 = 0)
    (hr0 : E.block.r.coeff 0 = 0)
    (houter :
      E.block.a.coeff 0 * E.block.x.coeff 0 -
        E.block.p.coeff 0 * E.block.p.coeff 0 ≠ 0)
    (hsj : E.block.s.coeff E.kernelOrder ≠ 0) :
    E.block.z.coeff
        (2 * E.kernelOrder - E.activeOrder) ≠ 0 := by
  let k := 2 * E.kernelOrder - E.activeOrder
  have hactiveLt : E.activeOrder < E.kernelOrder := E.active_lt_kernel
  have hqle : E.activeOrder ≤ 2 * E.kernelOrder := by omega
  have hsum : E.activeOrder + k = 2 * E.kernelOrder := by
    dsimp [k]
    omega
  have hzLower :
      ∀ n : ℕ, n < k → E.block.z.coeff n = 0 := by
    intro n hn
    exact E.kernelDiagonal_coeff_eq_zero_before_secondInteraction n (by
      simpa [k] using hn)
  have hactiveZ :
      (firstKernelBreakActiveThreeDet E.block * E.block.z).coeff
          (2 * E.kernelOrder) =
        (firstKernelBreakActiveThreeDet E.block).coeff E.activeOrder *
          E.block.z.coeff k := by
    have hlead :=
      coeff_mul_eq_leading_mul_of_lower_zero
        (firstKernelBreakActiveThreeDet E.block) E.block.z
        E.active_lower_zero hzLower
    simpa [hsum] using hlead
  have hdet :
      E.block.determinantCore.coeff (2 * E.kernelOrder) = 0 := by
    rw [E.determinantCore_eq_zero]
    simp
  rw [determinantCore_coeff_doubleKernel_of_middleKernelBase
      E.block E.q_lower_zero E.s_lower_zero E.y_lower_zero
      hb0 hd0 hr0, hactiveZ] at hdet
  intro hz
  rw [hz, mul_zero, zero_sub] at hdet
  have hright :
      (E.block.a.coeff 0 * E.block.x.coeff 0 -
          E.block.p.coeff 0 * E.block.p.coeff 0) *
        (E.block.s.coeff E.kernelOrder *
          E.block.s.coeff E.kernelOrder) ≠ 0 :=
    mul_ne_zero houter (mul_ne_zero hsj hsj)
  exact hright (neg_eq_zero.mp hdet)

end StaggeredSingularFirstKernelBreakFourBlockData

end

end HC4.Valuation
