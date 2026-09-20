import HC4.Newton.PreterminalFirstDeparture
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# First rank-one Schur-layer linearisation

This file isolates the exact finite convolution calculation needed at the
first transverse departure from a rank-one Schur line.

Let

    S(X) = [[A(X), B(X)], [B(X), C(X)]]

be a symmetric binary Schur family over an arbitrary commutative ring.  Fix
an order `j > 0`.  Assume

* `A(0) = a₀`;
* every coefficient of `B` below `j` vanishes;
* every coefficient of `C` below `j` vanishes.

No condition is imposed on the positive coefficients of `A` below `j`.
Nevertheless the `j`th coefficient of

    det S = A*C - B^2

is exactly

    a₀ * C_j.

Indeed every convolution term in `A*C` except `A₀*C_j` contains a lower
coefficient of `C`, while every term in `B^2` contains at least one lower
coefficient of `B` because `j > 0`.

This is the precise algebra behind the handwritten first-departure formula
`b * P_{j,VV}`.  The geometric part of the HC4 argument now only has to
construct the three Schur series and prove the stated lower-layer
vanishing; the determinant cancellation itself is unconditional.
-/

namespace HC4.Newton

noncomputable section

/-! ## Pure polynomial convolution lemmas -/

variable {R : Type*} [CommRing R]

/-- If the right factor has no coefficients below `j`, then the `j`th
coefficient of a product only sees the constant coefficient of the left
factor. -/
theorem coeff_mul_eq_constant_mul_of_right_vanishes_below
    (A C : Polynomial R)
    {j : ℕ}
    (hC : ∀ n : ℕ, n < j → C.coeff n = 0) :
    (A * C).coeff j = A.coeff 0 * C.coeff j := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (0, j)
  · intro x hx hne
    have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
    have hx2lt : x.2 < j := by
      by_contra hnot
      have hx2ge : j ≤ x.2 := Nat.le_of_not_gt hnot
      have hx1zero : x.1 = 0 := by omega
      have hx2eq : x.2 = j := by omega
      apply hne
      exact Prod.ext hx1zero hx2eq
    rw [hC x.2 hx2lt]
    simp
  · intro hnot
    have hmem : (0, j) ∈ Finset.antidiagonal j := by
      rw [Finset.mem_antidiagonal]
      simp
    exact (hnot hmem).elim

/-- If the right factor vanishes through order `j`, then the `j`th
coefficient of the product vanishes.  This is the denominator-cleared Schur
form needed later: multiplying the full determinant by an arbitrary active
factor cannot create a coefficient before the determinant-closing order. -/
theorem coeff_mul_eq_zero_of_right_vanishes_through
    (A C : Polynomial R)
    {j : ℕ}
    (hC : ∀ n : ℕ, n ≤ j → C.coeff n = 0) :
    (A * C).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
  have hx2le : x.2 ≤ j := by omega
  rw [hC x.2 hx2le]
  simp

/-- If a polynomial has no coefficients below a positive order `j`, then
its square has zero `j`th coefficient. -/
theorem coeff_sq_eq_zero_of_vanishes_below
    (B : Polynomial R)
    {j : ℕ}
    (hj : 0 < j)
    (hB : ∀ n : ℕ, n < j → B.coeff n = 0) :
    (B * B).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
  have hsmall : x.1 < j ∨ x.2 < j := by
    omega
  rcases hsmall with hx1 | hx2
  · rw [hB x.1 hx1]
    simp
  · rw [hB x.2 hx2]
    simp

/-! ## Packaged first rank-one Schur departure -/

/-- The exact algebraic data of a first transverse departure from a
rank-one symmetric Schur line.

The active diagonal entry may have arbitrary earlier positive layers.  Only
the off-diagonal and kernel-direction entries are required to vanish below
the departure order. -/
structure FirstRankOneSchurDeparture (R : Type*) [CommRing R] where
  order : ℕ
  leading : R
  active : Polynomial R
  offDiag : Polynomial R
  kernel : Polynomial R
  order_pos : 0 < order
  active_coeff_zero : active.coeff 0 = leading
  offDiag_lower_zero :
    ∀ n : ℕ, n < order → offDiag.coeff n = 0
  kernel_lower_zero :
    ∀ n : ℕ, n < order → kernel.coeff n = 0

namespace FirstRankOneSchurDeparture

/-- Determinant of the binary Schur family. -/
def determinant
    (E : FirstRankOneSchurDeparture R) : Polynomial R :=
  E.active * E.kernel - E.offDiag * E.offDiag

/-- **First-departure Schur linearisation.**

At the first transverse order the determinant is linear in the new
kernel-direction entry, with coefficient equal to the old active rank-one
entry. -/
theorem coeff_order_determinant
    (E : FirstRankOneSchurDeparture R) :
    E.determinant.coeff E.order =
      E.leading * E.kernel.coeff E.order := by
  unfold determinant
  rw [Polynomial.coeff_sub]
  rw [coeff_mul_eq_constant_mul_of_right_vanishes_below
      E.active E.kernel E.kernel_lower_zero]
  rw [coeff_sq_eq_zero_of_vanishes_below
      E.offDiag E.order_pos E.offDiag_lower_zero]
  rw [E.active_coeff_zero]
  simp

end FirstRankOneSchurDeparture

/-! ## Automatic first transverse order -/

/-- A polynomial binary Schur series whose constant term is already on a
fixed rank-one line.  Positive coefficients of the active entry are left
completely unrestricted; only the off-diagonal and kernel entries vanish at
order zero. -/
structure RankOneSchurSeries (R : Type*) [CommRing R] where
  leading : R
  active : Polynomial R
  offDiag : Polynomial R
  kernel : Polynomial R
  active_coeff_zero : active.coeff 0 = leading
  offDiag_coeff_zero : offDiag.coeff 0 = 0
  kernel_coeff_zero : kernel.coeff 0 = 0

namespace RankOneSchurSeries

/-- Determinant of the binary Schur series. -/
def determinant (S : RankOneSchurSeries R) : Polynomial R :=
  S.active * S.kernel - S.offDiag * S.offDiag

/-- Positive parameter orders at which the Schur line actually moves in a
transverse direction.  Pure changes of the active entry are deliberately
ignored. -/
noncomputable def positiveTransverseOrders
    (S : RankOneSchurSeries R) : Finset ℕ :=
  (S.offDiag.support ∪ S.kernel.support).filter (fun n => 0 < n)

/-- There is a genuine later transverse Schur layer. -/
def HasPositiveTransverseLayer
    (S : RankOneSchurSeries R) : Prop :=
  S.positiveTransverseOrders.Nonempty

/-- Least positive order at which either the off-diagonal or kernel Schur
entry is nonzero. -/
noncomputable def firstPositiveTransverseOrder
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer) : ℕ :=
  S.positiveTransverseOrders.min' h

theorem firstPositiveTransverseOrder_mem
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer) :
    S.firstPositiveTransverseOrder h ∈ S.positiveTransverseOrders := by
  unfold firstPositiveTransverseOrder
  exact Finset.min'_mem _ h

theorem firstPositiveTransverseOrder_pos
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer) :
    0 < S.firstPositiveTransverseOrder h := by
  have hm := S.firstPositiveTransverseOrder_mem h
  exact (Finset.mem_filter.mp hm).2

/-- Every off-diagonal coefficient before the selected first transverse
order vanishes. -/
theorem offDiag_coeff_eq_zero_of_lt_first
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer)
    {n : ℕ}
    (hn : n < S.firstPositiveTransverseOrder h) :
    S.offDiag.coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.offDiag_coeff_zero
  · by_contra hcoeff
    have hmem : n ∈ S.positiveTransverseOrders := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_union.mpr
        left
        exact Polynomial.mem_support_iff.mpr hcoeff
      · omega
    have hle : S.firstPositiveTransverseOrder h ≤ n := by
      unfold firstPositiveTransverseOrder
      exact Finset.min'_le S.positiveTransverseOrders n hmem
    omega

/-- Every kernel coefficient before the selected first transverse order
vanishes. -/
theorem kernel_coeff_eq_zero_of_lt_first
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer)
    {n : ℕ}
    (hn : n < S.firstPositiveTransverseOrder h) :
    S.kernel.coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.kernel_coeff_zero
  · by_contra hcoeff
    have hmem : n ∈ S.positiveTransverseOrders := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_union.mpr
        right
        exact Polynomial.mem_support_iff.mpr hcoeff
      · omega
    have hle : S.firstPositiveTransverseOrder h ≤ n := by
      unfold firstPositiveTransverseOrder
      exact Finset.min'_le S.positiveTransverseOrders n hmem
    omega

/-- The selected order is genuinely transverse: at least one of the two
transverse Schur entries is nonzero there. -/
theorem transverse_nonzero_at_first
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer) :
    S.offDiag.coeff (S.firstPositiveTransverseOrder h) ≠ 0 ∨
      S.kernel.coeff (S.firstPositiveTransverseOrder h) ≠ 0 := by
  have hm := S.firstPositiveTransverseOrder_mem h
  have hu := (Finset.mem_filter.mp hm).1
  rcases Finset.mem_union.mp hu with hB | hC
  · exact Or.inl (Polynomial.mem_support_iff.mp hB)
  · exact Or.inr (Polynomial.mem_support_iff.mp hC)

/-- If there is no positive transverse layer, the off-diagonal Schur
series vanishes identically. -/
theorem offDiag_eq_zero_of_not_hasPositiveTransverseLayer
    (S : RankOneSchurSeries R)
    (h : ¬ S.HasPositiveTransverseLayer) :
    S.offDiag = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn0 : n = 0
  · subst n
    exact S.offDiag_coeff_zero
  · by_contra hcoeff
    apply h
    refine ⟨n, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_union.mpr
      left
      exact Polynomial.mem_support_iff.mpr hcoeff
    · omega

/-- If there is no positive transverse layer, the kernel-direction Schur
series vanishes identically. -/
theorem kernel_eq_zero_of_not_hasPositiveTransverseLayer
    (S : RankOneSchurSeries R)
    (h : ¬ S.HasPositiveTransverseLayer) :
    S.kernel = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn0 : n = 0
  · subst n
    exact S.kernel_coeff_zero
  · by_contra hcoeff
    apply h
    refine ⟨n, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_union.mpr
      right
      exact Polynomial.mem_support_iff.mpr hcoeff
    · omega

/-- With no transverse movement at all, the binary Schur determinant is
identically zero. -/
theorem determinant_eq_zero_of_not_hasPositiveTransverseLayer
    (S : RankOneSchurSeries R)
    (h : ¬ S.HasPositiveTransverseLayer) :
    S.determinant = 0 := by
  unfold RankOneSchurSeries.determinant
  rw [S.offDiag_eq_zero_of_not_hasPositiveTransverseLayer h,
    S.kernel_eq_zero_of_not_hasPositiveTransverseLayer h]
  simp

/-- Every determinant coefficient strictly before the selected first
transverse order vanishes. -/
theorem determinant_coeff_eq_zero_of_lt_first
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer)
    {n : ℕ}
    (hn : n < S.firstPositiveTransverseOrder h) :
    S.determinant.coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [RankOneSchurSeries.determinant,
      S.offDiag_coeff_zero, S.kernel_coeff_zero]
  · unfold RankOneSchurSeries.determinant
    rw [Polynomial.coeff_sub]
    have hkernel :
        ∀ k : ℕ, k ≤ n → S.kernel.coeff k = 0 := by
      intro k hk
      exact S.kernel_coeff_eq_zero_of_lt_first h (by omega)
    rw [coeff_mul_eq_zero_of_right_vanishes_through
      S.active S.kernel hkernel]
    have hoff :
        ∀ k : ℕ, k < n → S.offDiag.coeff k = 0 := by
      intro k hk
      exact S.offDiag_coeff_eq_zero_of_lt_first h (by omega)
    rw [coeff_sq_eq_zero_of_vanishes_below
      S.offDiag (Nat.pos_of_ne_zero hn0) hoff]
    simp

/-- If both factors vanish below order `j`, their product has no
coefficient strictly before order `2*j`. -/
theorem coeff_mul_eq_zero_before_twice_of_lower_zero
    (B C : Polynomial R)
    {j n : ℕ}
    (hn : n < 2 * j)
    (hB : ∀ r : ℕ, r < j → B.coeff r = 0)
    (hC : ∀ r : ℕ, r < j → C.coeff r = 0) :
    (B * C).coeff n = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
  have hsmall : x.1 < j ∨ x.2 < j := by
    by_contra hnot
    push_neg at hnot
    omega
  rcases hsmall with hleft | hright
  · rw [hB x.1 hleft]
    simp
  · rw [hC x.2 hright]
    simp

/-- If both factors vanish below `j`, the coefficient at the exact first
possible product order `2*j` is the product of their `j`th coefficients. -/
theorem coeff_mul_twice_eq_leading_mul_of_lower_zero
    (B C : Polynomial R)
    {j : ℕ}
    (hB : ∀ r : ℕ, r < j → B.coeff r = 0)
    (hC : ∀ r : ℕ, r < j → C.coeff r = 0) :
    (B * C).coeff (2 * j) = B.coeff j * C.coeff j := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (j, j)
  · intro x hx hne
    have hsum : x.1 + x.2 = 2 * j := Finset.mem_antidiagonal.mp hx
    by_cases hx1 : x.1 < j
    · rw [hB x.1 hx1]
      simp
    · by_cases hx2 : x.2 < j
      · rw [hC x.2 hx2]
        simp
      · have hx1ge : j ≤ x.1 := Nat.le_of_not_gt hx1
        have hx2ge : j ≤ x.2 := Nat.le_of_not_gt hx2
        have heq1 : x.1 = j := by omega
        have heq2 : x.2 = j := by omega
        exact (hne (Prod.ext heq1 heq2)).elim
  · intro hnot
    have hmem : (j, j) ∈ Finset.antidiagonal (2 * j) := by
      rw [Finset.mem_antidiagonal]
      omega
    exact (hnot hmem).elim

/-- For an identically singular rank-one Schur series, the first
transverse departure cannot occur in the kernel direction.  The determinant
linearisation at the first transverse order kills that coefficient, so the
off-diagonal coefficient is necessarily nonzero. -/
theorem firstTransverse_offDiag_ne_zero_of_determinant_eq_zero
    [NoZeroDivisors R]
    (S : RankOneSchurSeries R)
    (hlead : S.leading ≠ 0)
    (hdet : S.determinant = 0)
    (htrans : S.HasPositiveTransverseLayer) :
    S.offDiag.coeff (S.firstPositiveTransverseOrder htrans) ≠ 0 := by
  let j := S.firstPositiveTransverseOrder htrans
  have hj : 0 < j := by
    dsimp [j]
    exact S.firstPositiveTransverseOrder_pos htrans
  have hkernelLower :
      ∀ r : ℕ, r < j → S.kernel.coeff r = 0 := by
    intro r hr
    exact S.kernel_coeff_eq_zero_of_lt_first htrans (by simpa [j] using hr)
  have hoffLower :
      ∀ r : ℕ, r < j → S.offDiag.coeff r = 0 := by
    intro r hr
    exact S.offDiag_coeff_eq_zero_of_lt_first htrans (by simpa [j] using hr)
  have hactiveKernel :
      (S.active * S.kernel).coeff j =
        S.active.coeff 0 * S.kernel.coeff j :=
    coeff_mul_eq_constant_mul_of_right_vanishes_below
      S.active S.kernel hkernelLower
  have hoffSquare : (S.offDiag * S.offDiag).coeff j = 0 :=
    coeff_sq_eq_zero_of_vanishes_below S.offDiag hj hoffLower
  have hcoeff : S.determinant.coeff j = 0 := by
    rw [hdet]
    rfl
  have hkernel : S.kernel.coeff j = 0 := by
    unfold RankOneSchurSeries.determinant at hcoeff
    rw [Polynomial.coeff_sub, hactiveKernel, hoffSquare,
      S.active_coeff_zero] at hcoeff
    simp only [sub_zero] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left hlead
  rcases S.transverse_nonzero_at_first htrans with hoff | hker
  · simpa [j] using hoff
  · exact False.elim (hker (by simpa [j] using hkernel))

/-- In the same identically singular rank-one series, the kernel entry remains
zero strictly before twice the first transverse order. -/
theorem kernel_coeff_eq_zero_before_twice_firstTransverse
    [NoZeroDivisors R]
    (S : RankOneSchurSeries R)
    (hlead : S.leading ≠ 0)
    (hdet : S.determinant = 0)
    (htrans : S.HasPositiveTransverseLayer) :
    ∀ n : ℕ, n < 2 * S.firstPositiveTransverseOrder htrans →
      S.kernel.coeff n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      let j := S.firstPositiveTransverseOrder htrans
      by_cases hnj : n < j
      · exact S.kernel_coeff_eq_zero_of_lt_first htrans (by simpa [j] using hnj)
      · have hkerLower :
            ∀ r : ℕ, r < n → S.kernel.coeff r = 0 := by
          intro r hr
          exact ih r hr (lt_trans hr hn)
        have hoffLower :
            ∀ r : ℕ, r < j → S.offDiag.coeff r = 0 := by
          intro r hr
          exact S.offDiag_coeff_eq_zero_of_lt_first htrans
            (by simpa [j] using hr)
        have hoffSquare :
            (S.offDiag * S.offDiag).coeff n = 0 := by
          exact coeff_mul_eq_zero_before_twice_of_lower_zero
            S.offDiag S.offDiag (by simpa [j] using hn) hoffLower hoffLower
        have hactiveKernel :
            (S.active * S.kernel).coeff n =
              S.active.coeff 0 * S.kernel.coeff n := by
          exact coeff_mul_eq_constant_mul_of_right_vanishes_below
            S.active S.kernel hkerLower
        have hcoeff : S.determinant.coeff n = 0 := by
          rw [hdet]
          rfl
        unfold RankOneSchurSeries.determinant at hcoeff
        rw [Polynomial.coeff_sub, hactiveKernel, hoffSquare,
          S.active_coeff_zero] at hcoeff
        simp only [sub_zero] at hcoeff
        exact (mul_eq_zero.mp hcoeff).resolve_left hlead

/-- Exact first quadratic interaction in an identically singular rank-one
Schur series.  If the first transverse order is `j`, then the kernel first
appears at `2*j` and satisfies the square identity
`leading * C_(2j) = B_j^2`. -/
theorem kernel_coeff_twice_firstTransverse_identity
    [NoZeroDivisors R]
    (S : RankOneSchurSeries R)
    (hlead : S.leading ≠ 0)
    (hdet : S.determinant = 0)
    (htrans : S.HasPositiveTransverseLayer) :
    S.leading *
        S.kernel.coeff (2 * S.firstPositiveTransverseOrder htrans) =
      S.offDiag.coeff (S.firstPositiveTransverseOrder htrans) *
        S.offDiag.coeff (S.firstPositiveTransverseOrder htrans) := by
  let j := S.firstPositiveTransverseOrder htrans
  have hkerLower :
      ∀ r : ℕ, r < 2 * j → S.kernel.coeff r = 0 := by
    intro r hr
    exact S.kernel_coeff_eq_zero_before_twice_firstTransverse
      hlead hdet htrans r (by simpa [j] using hr)
  have hactiveKernel :
      (S.active * S.kernel).coeff (2 * j) =
        S.active.coeff 0 * S.kernel.coeff (2 * j) := by
    exact coeff_mul_eq_constant_mul_of_right_vanishes_below
      S.active S.kernel hkerLower
  have hoffLower :
      ∀ r : ℕ, r < j → S.offDiag.coeff r = 0 := by
    intro r hr
    exact S.offDiag_coeff_eq_zero_of_lt_first htrans (by simpa [j] using hr)
  have hoffSquare :
      (S.offDiag * S.offDiag).coeff (2 * j) =
        S.offDiag.coeff j * S.offDiag.coeff j :=
    coeff_mul_twice_eq_leading_mul_of_lower_zero
      S.offDiag S.offDiag hoffLower hoffLower
  have hcoeff : S.determinant.coeff (2 * j) = 0 := by
    rw [hdet]
    rfl
  unfold RankOneSchurSeries.determinant at hcoeff
  rw [Polynomial.coeff_sub, hactiveKernel, hoffSquare,
    S.active_coeff_zero] at hcoeff
  have hid :
      S.leading * S.kernel.coeff (2 * j) =
        S.offDiag.coeff j * S.offDiag.coeff j :=
    sub_eq_zero.mp hcoeff
  simpa [j] using hid

/-- The forced kernel coefficient at twice the first transverse order is
genuinely nonzero. -/
theorem kernel_coeff_twice_firstTransverse_ne_zero
    [NoZeroDivisors R]
    (S : RankOneSchurSeries R)
    (hlead : S.leading ≠ 0)
    (hdet : S.determinant = 0)
    (htrans : S.HasPositiveTransverseLayer) :
    S.kernel.coeff (2 * S.firstPositiveTransverseOrder htrans) ≠ 0 := by
  have hoff :=
    S.firstTransverse_offDiag_ne_zero_of_determinant_eq_zero
      hlead hdet htrans
  have hid :=
    S.kernel_coeff_twice_firstTransverse_identity
      hlead hdet htrans
  intro hzero
  rw [hzero, mul_zero] at hid
  exact (mul_ne_zero hoff hoff) hid.symm

/-- A genuine cleared determinant identity with nonzero constant clearing
factor forces a positive transverse Schur layer.  Thus the local proof never
needs a separate existence hypothesis for the first departure. -/
theorem hasPositiveTransverseLayer_of_determinant_eq_factor_mul_X_pow
    (S : RankOneSchurSeries R)
    (factor : Polynomial R)
    (Delta : ℕ)
    (hfactor :
      S.determinant = factor * Polynomial.X ^ Delta)
    (hfactor0 : factor.coeff 0 ≠ 0) :
    S.HasPositiveTransverseLayer := by
  by_contra hnone
  have hdet0 : S.determinant = 0 :=
    S.determinant_eq_zero_of_not_hasPositiveTransverseLayer hnone
  have hcoeff :
      (factor * Polynomial.X ^ Delta).coeff Delta =
        factor.coeff 0 := by
    simpa using
      (Polynomial.coeff_mul_X_pow factor Delta 0)
  apply hfactor0
  rw [← hcoeff, ← hfactor, hdet0]
  simp

/-- Under the same exact cleared identity, the first transverse order cannot
occur after determinant closure.  Hence the only possibilities are the
preterminal case `j < Delta` and the closing case `j = Delta`. -/
theorem firstPositiveTransverseOrder_le_of_determinant_eq_factor_mul_X_pow
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer)
    (factor : Polynomial R)
    {Delta : ℕ}
    (hfactor :
      S.determinant = factor * Polynomial.X ^ Delta)
    (hfactor0 : factor.coeff 0 ≠ 0) :
    S.firstPositiveTransverseOrder h ≤ Delta := by
  by_contra hnot
  have hlt : Delta < S.firstPositiveTransverseOrder h :=
    Nat.lt_of_not_ge hnot
  have hdet0 : S.determinant.coeff Delta = 0 :=
    S.determinant_coeff_eq_zero_of_lt_first h hlt
  have hcoeff :
      (factor * Polynomial.X ^ Delta).coeff Delta =
        factor.coeff 0 := by
    simpa using
      (Polynomial.coeff_mul_X_pow factor Delta 0)
  apply hfactor0
  calc
    factor.coeff 0 =
        (factor * Polynomial.X ^ Delta).coeff Delta := hcoeff.symm
    _ = S.determinant.coeff Delta := by rw [← hfactor]
    _ = 0 := hdet0

/-- The finite first-transverse selector automatically packages the exact
lower-vanishing hypotheses required by `FirstRankOneSchurDeparture`. -/
noncomputable def firstDeparture
    (S : RankOneSchurSeries R)
    (h : S.HasPositiveTransverseLayer) :
    FirstRankOneSchurDeparture R where
  order := S.firstPositiveTransverseOrder h
  leading := S.leading
  active := S.active
  offDiag := S.offDiag
  kernel := S.kernel
  order_pos := S.firstPositiveTransverseOrder_pos h
  active_coeff_zero := S.active_coeff_zero
  offDiag_lower_zero := by
    intro n hn
    exact S.offDiag_coeff_eq_zero_of_lt_first h hn
  kernel_lower_zero := by
    intro n hn
    exact S.kernel_coeff_eq_zero_of_lt_first h hn

end RankOneSchurSeries

/-! ## HC4 preterminal specialisation -/

variable {σ K : Type*} [Field K]

/-- A first rank-one Schur departure whose new kernel entry is the second
`V`-derivative of an actual coefficient potential.

This package contains no determinant-vanishing hypothesis.  It only records
the local Schur normal form and the identification of the first kernel
coefficient with the potential that will be passed to the existing
preterminal machinery. -/
structure PreterminalSchurDepartureData
    (σ K : Type*) [Field K] where
  order : ℕ
  leadingScalar : K
  U : σ
  V : σ
  potential : MvPolynomial σ K
  active : Polynomial (MvPolynomial σ K)
  offDiag : Polynomial (MvPolynomial σ K)
  kernel : Polynomial (MvPolynomial σ K)
  order_pos : 0 < order
  leadingScalar_ne_zero : leadingScalar ≠ 0
  active_coeff_zero :
    active.coeff 0 = MvPolynomial.C leadingScalar
  offDiag_lower_zero :
    ∀ n : ℕ, n < order → offDiag.coeff n = 0
  kernel_lower_zero :
    ∀ n : ℕ, n < order → kernel.coeff n = 0
  kernel_coeff_order :
    kernel.coeff order =
      directionalSecondDerivative V potential

namespace PreterminalSchurDepartureData

/-- Binary Schur determinant represented by the departure data. -/
def determinant
    (E : PreterminalSchurDepartureData σ K) :
    Polynomial (MvPolynomial σ K) :=
  E.active * E.kernel - E.offDiag * E.offDiag

/-- The abstract first-Schur convolution theorem becomes exactly the
preterminal linear source `b * P_VV`. -/
theorem determinant_coeff_order_eq_linearSource
    (E : PreterminalSchurDepartureData σ K) :
    E.determinant.coeff E.order =
      preterminalSchurLinearSource
        E.leadingScalar E.V E.potential := by
  unfold determinant
  rw [Polynomial.coeff_sub]
  rw [coeff_mul_eq_constant_mul_of_right_vanishes_below
      E.active E.kernel E.kernel_lower_zero]
  rw [coeff_sq_eq_zero_of_vanishes_below
      E.offDiag E.order_pos E.offDiag_lower_zero]
  rw [E.active_coeff_zero, E.kernel_coeff_order]
  unfold preterminalSchurLinearSource
  simp

/-- **Denominator-cleared preterminal vanishing.**

Suppose the binary Schur determinant is a polynomial multiple of a full
determinant series `H`.  If `H` has no coefficients through the departure
order, then the Schur determinant coefficient at that order is zero.  No
division by the active block and no unit hypothesis is required. -/
theorem determinant_coeff_order_eq_zero_of_clearedFactor
    (E : PreterminalSchurDepartureData σ K)
    (factor fullDet : Polynomial (MvPolynomial σ K))
    (hfactor :
      E.determinant = factor * fullDet)
    (hfull :
      ∀ n : ℕ, n ≤ E.order → fullDet.coeff n = 0) :
    E.determinant.coeff E.order = 0 := by
  rw [hfactor]
  exact
    coeff_mul_eq_zero_of_right_vanishes_through
      factor fullDet hfull

/-- The cleared determinant factorisation therefore kills the exact
preterminal Schur linear source. -/
theorem linearSource_eq_zero_of_clearedFactor
    (E : PreterminalSchurDepartureData σ K)
    (factor fullDet : Polynomial (MvPolynomial σ K))
    (hfactor :
      E.determinant = factor * fullDet)
    (hfull :
      ∀ n : ℕ, n ≤ E.order → fullDet.coeff n = 0) :
    preterminalSchurLinearSource
      E.leadingScalar E.V E.potential = 0 := by
  rw [← E.determinant_coeff_order_eq_linearSource]
  exact
    E.determinant_coeff_order_eq_zero_of_clearedFactor
      factor fullDet hfactor hfull

end PreterminalSchurDepartureData

end

end HC4.Newton
