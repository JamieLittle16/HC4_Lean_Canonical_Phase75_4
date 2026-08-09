import HC4.Newton.RankOneSchurSeriesAlignment
import HC4.Newton.RankOneRepairProgress
import Mathlib.Tactic

/-!
# Zero-Schur first-entry clock

The rigid Smith packet exposed by the defect-preserving family has Hessian
rank at most two.  After choosing a nonzero active `2 x 2` Hessian minor,
the denominator-cleared binary Schur complement therefore has *zero*
constant block.  The correct first-departure object is consequently not the
rank-one Schur line of `FirstSchurLayerLinearization`, but a zero Schur block
whose first nonzero coefficient is selected automatically.

This file isolates the purely algebraic clock needed for that situation.
For a binary polynomial Schur series

    S(X) = [[A(X), B(X)], [B(X), C(X)]]

with `A(0)=B(0)=C(0)=0`, let `e>0` be the first order at which any entry is
nonzero.  All three entries are divisible by `X^e`; after writing

    A = X^e A₁,  B = X^e B₁,  C = X^e C₁,

the determinant factors as

    det S = X^(2e) (A₁ C₁ - B₁^2).

If in addition

    det S = Q X^N,     Q(0) ≠ 0,

then necessarily `2e ≤ N`, and cancellation gives

    det S₁ = Q X^(N-2e).

Hence:

* if `2e = N`, the first coefficient block is already nondegenerate and
  occurs exactly at determinant closure;
* if `2e < N`, the first coefficient block has determinant zero.  Since it
  is nonzero, it has a ring-level left or right rank-one pivot.  Constant
  alignment then produces the rank-one Schur clock used by the green
  first-transverse machinery.

No HC4 geometry appears here.  The next valuation module only has to prove
that the actual exposed Hessian four-block satisfies the zero-constant and
active-minor hypotheses.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

namespace BinarySchurPolynomialSeries

/-- At least one entry of the constant binary block is nonzero. -/
def ConstantBlockNonzero (S : BinarySchurPolynomialSeries R) : Prop :=
  S.active.coeff 0 ≠ 0 ∨
    S.offDiag.coeff 0 ≠ 0 ∨
    S.kernel.coeff 0 ≠ 0

/-- Over a domain, a nonzero determinant-zero constant symmetric block has
one of the two coordinate pivot forms used by the rank-one alignment layer. -/
theorem leftPivot_or_rightAxisPivot_of_constantBlock
    [IsDomain R]
    (S : BinarySchurPolynomialSeries R)
    (hnz : S.ConstantBlockNonzero)
    (hdet :
      S.active.coeff 0 * S.kernel.coeff 0 =
        S.offDiag.coeff 0 * S.offDiag.coeff 0) :
    S.LeftPivot ∨ S.RightAxisPivot := by
  by_cases ha : S.active.coeff 0 = 0
  · right
    have hbb : S.offDiag.coeff 0 * S.offDiag.coeff 0 = 0 := by
      rw [ha, zero_mul] at hdet
      exact hdet.symm
    have hb : S.offDiag.coeff 0 = 0 := by
      rcases mul_eq_zero.mp hbb with hb | hb
      · exact hb
      · exact hb
    have hc : S.kernel.coeff 0 ≠ 0 := by
      rcases hnz with hA | hB | hC
      · exact False.elim (hA ha)
      · exact False.elim (hB hb)
      · exact hC
    exact ⟨ha, hb, hc⟩
  · left
    exact ⟨ha, hdet⟩

end BinarySchurPolynomialSeries

/-! ## Zero-constant Schur series and the first common order -/

/-- A symmetric binary polynomial Schur series whose complete constant
coefficient block vanishes. -/
structure ZeroSchurSeries (R : Type*) [CommRing R] where
  series : BinarySchurPolynomialSeries R
  active_coeff_zero : series.active.coeff 0 = 0
  offDiag_coeff_zero : series.offDiag.coeff 0 = 0
  kernel_coeff_zero : series.kernel.coeff 0 = 0

namespace ZeroSchurSeries

/-- Positive parameter orders at which at least one Schur entry is nonzero. -/
noncomputable def positiveEntryOrders
    (S : ZeroSchurSeries R) : Finset Nat :=
  (S.series.active.support ∪
      (S.series.offDiag.support ∪
        S.series.kernel.support)).filter (fun n => 0 < n)

/-- There is a genuine positive Schur layer. -/
def HasPositiveEntryLayer (S : ZeroSchurSeries R) : Prop :=
  S.positiveEntryOrders.Nonempty

/-- Least positive order at which any of the three Schur entries is nonzero. -/
noncomputable def firstPositiveEntryOrder
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) : Nat :=
  S.positiveEntryOrders.min' h

 theorem firstPositiveEntryOrder_mem
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.firstPositiveEntryOrder h ∈ S.positiveEntryOrders := by
  unfold firstPositiveEntryOrder
  exact Finset.min'_mem _ h

 theorem firstPositiveEntryOrder_pos
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    0 < S.firstPositiveEntryOrder h := by
  have hm := S.firstPositiveEntryOrder_mem h
  exact (Finset.mem_filter.mp hm).2

/-- Every active coefficient before the first selected Schur order vanishes. -/
theorem active_coeff_eq_zero_of_lt_first
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    {n : Nat}
    (hn : n < S.firstPositiveEntryOrder h) :
    S.series.active.coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.active_coeff_zero
  · by_contra hcoeff
    have hmem : n ∈ S.positiveEntryOrders := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_union.mpr
        left
        exact Polynomial.mem_support_iff.mpr hcoeff
      · omega
    have hle : S.firstPositiveEntryOrder h ≤ n := by
      unfold firstPositiveEntryOrder
      exact Finset.min'_le S.positiveEntryOrders n hmem
    omega

/-- Every off-diagonal coefficient before the first selected order vanishes. -/
theorem offDiag_coeff_eq_zero_of_lt_first
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    {n : Nat}
    (hn : n < S.firstPositiveEntryOrder h) :
    S.series.offDiag.coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.offDiag_coeff_zero
  · by_contra hcoeff
    have hmem : n ∈ S.positiveEntryOrders := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        left
        exact Polynomial.mem_support_iff.mpr hcoeff
      · omega
    have hle : S.firstPositiveEntryOrder h ≤ n := by
      unfold firstPositiveEntryOrder
      exact Finset.min'_le S.positiveEntryOrders n hmem
    omega

/-- Every kernel coefficient before the first selected order vanishes. -/
theorem kernel_coeff_eq_zero_of_lt_first
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    {n : Nat}
    (hn : n < S.firstPositiveEntryOrder h) :
    S.series.kernel.coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.kernel_coeff_zero
  · by_contra hcoeff
    have hmem : n ∈ S.positiveEntryOrders := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        right
        exact Polynomial.mem_support_iff.mpr hcoeff
      · omega
    have hle : S.firstPositiveEntryOrder h ≤ n := by
      unfold firstPositiveEntryOrder
      exact Finset.min'_le S.positiveEntryOrders n hmem
    omega

/-- The selected first order has a genuinely nonzero coefficient ∈ at least
one entry. -/
theorem entry_nonzero_at_first
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.active.coeff (S.firstPositiveEntryOrder h) ≠ 0 ∨
      S.series.offDiag.coeff (S.firstPositiveEntryOrder h) ≠ 0 ∨
      S.series.kernel.coeff (S.firstPositiveEntryOrder h) ≠ 0 := by
  have hm := S.firstPositiveEntryOrder_mem h
  have hu := (Finset.mem_filter.mp hm).1
  rcases Finset.mem_union.mp hu with hA | hrest
  · exact Or.inl (Polynomial.mem_support_iff.mp hA)
  · rcases Finset.mem_union.mp hrest with hB | hC
    · exact Or.inr (Or.inl (Polynomial.mem_support_iff.mp hB))
    · exact Or.inr (Or.inr (Polynomial.mem_support_iff.mp hC))

/-- If no positive layer exists, the active series is zero. -/
theorem active_eq_zero_of_not_hasPositiveEntryLayer
    (S : ZeroSchurSeries R)
    (h : ¬ S.HasPositiveEntryLayer) :
    S.series.active = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn0 : n = 0
  · subst n
    exact S.active_coeff_zero
  · by_contra hcoeff
    apply h
    refine ⟨n, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_union.mpr
      left
      exact Polynomial.mem_support_iff.mpr hcoeff
    · omega

/-- If no positive layer exists, the off-diagonal series is zero. -/
theorem offDiag_eq_zero_of_not_hasPositiveEntryLayer
    (S : ZeroSchurSeries R)
    (h : ¬ S.HasPositiveEntryLayer) :
    S.series.offDiag = 0 := by
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
      right
      apply Finset.mem_union.mpr
      left
      exact Polynomial.mem_support_iff.mpr hcoeff
    · omega

/-- If no positive layer exists, the kernel series is zero. -/
theorem kernel_eq_zero_of_not_hasPositiveEntryLayer
    (S : ZeroSchurSeries R)
    (h : ¬ S.HasPositiveEntryLayer) :
    S.series.kernel = 0 := by
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
      apply Finset.mem_union.mpr
      right
      exact Polynomial.mem_support_iff.mpr hcoeff
    · omega

/-- If the zero-constant Schur series never moves, its determinant vanishes. -/
theorem determinant_eq_zero_of_not_hasPositiveEntryLayer
    (S : ZeroSchurSeries R)
    (h : ¬ S.HasPositiveEntryLayer) :
    S.series.determinant = 0 := by
  unfold BinarySchurPolynomialSeries.determinant
  rw [S.active_eq_zero_of_not_hasPositiveEntryLayer h,
    S.offDiag_eq_zero_of_not_hasPositiveEntryLayer h,
    S.kernel_eq_zero_of_not_hasPositiveEntryLayer h]
  simp

/-- The selected first order divides the active entry. -/
theorem firstFactor_dvd_active
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ∣
      S.series.active := by
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  exact S.active_coeff_eq_zero_of_lt_first h hn

/-- The selected first order divides the off-diagonal entry. -/
theorem firstFactor_dvd_offDiag
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ∣
      S.series.offDiag := by
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  exact S.offDiag_coeff_eq_zero_of_lt_first h hn

/-- The selected first order divides the kernel entry. -/
theorem firstFactor_dvd_kernel
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ∣
      S.series.kernel := by
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  exact S.kernel_coeff_eq_zero_of_lt_first h hn

/-- Tail after removing the first common power from the active entry. -/
noncomputable def tailActive
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) : Polynomial R :=
  Classical.choose (S.firstFactor_dvd_active h)

/-- Tail after removing the first common power from the off-diagonal entry. -/
noncomputable def tailOffDiag
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) : Polynomial R :=
  Classical.choose (S.firstFactor_dvd_offDiag h)

/-- Tail after removing the first common power from the kernel entry. -/
noncomputable def tailKernel
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) : Polynomial R :=
  Classical.choose (S.firstFactor_dvd_kernel h)

/-- The normalised binary tail at the first nonzero Schur layer. -/
noncomputable def tailSeries
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) : BinarySchurPolynomialSeries R where
  active := S.tailActive h
  offDiag := S.tailOffDiag h
  kernel := S.tailKernel h

 theorem active_eq_firstFactor_mul_tail
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.active =
      Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailActive h := by
  exact Classical.choose_spec (S.firstFactor_dvd_active h)

 theorem offDiag_eq_firstFactor_mul_tail
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.offDiag =
      Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailOffDiag h := by
  exact Classical.choose_spec (S.firstFactor_dvd_offDiag h)

 theorem kernel_eq_firstFactor_mul_tail
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.kernel =
      Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailKernel h := by
  exact Classical.choose_spec (S.firstFactor_dvd_kernel h)

/-- Coefficient at the first selected order is the constant coefficient of
its normalised tail. -/
theorem active_coeff_first_eq_tail_zero
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.active.coeff (S.firstPositiveEntryOrder h) =
      (S.tailSeries h).active.coeff 0 := by
  rw [S.active_eq_firstFactor_mul_tail h]
  simp only [tailSeries]
  rw [Polynomial.coeff_X_pow_mul']
  simp

 theorem offDiag_coeff_first_eq_tail_zero
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.offDiag.coeff (S.firstPositiveEntryOrder h) =
      (S.tailSeries h).offDiag.coeff 0 := by
  rw [S.offDiag_eq_firstFactor_mul_tail h]
  simp only [tailSeries]
  rw [Polynomial.coeff_X_pow_mul']
  simp

 theorem kernel_coeff_first_eq_tail_zero
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.kernel.coeff (S.firstPositiveEntryOrder h) =
      (S.tailSeries h).kernel.coeff 0 := by
  rw [S.kernel_eq_firstFactor_mul_tail h]
  simp only [tailSeries]
  rw [Polynomial.coeff_X_pow_mul']
  simp

/-- The first normalised tail has a nonzero constant block. -/
theorem tailSeries_constantBlock_nonzero
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    (S.tailSeries h).ConstantBlockNonzero := by
  rcases S.entry_nonzero_at_first h with hA | hB | hC
  · left
    rw [← S.active_coeff_first_eq_tail_zero h]
    exact hA
  · right
    left
    rw [← S.offDiag_coeff_first_eq_tail_zero h]
    exact hB
  · right
    right
    rw [← S.kernel_coeff_first_eq_tail_zero h]
    exact hC

/-- Removing the common first order removes its square from the determinant. -/
theorem determinant_eq_firstFactor_sq_mul_tail
    (S : ZeroSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.determinant =
      Polynomial.X ^ (2 * S.firstPositiveEntryOrder h) *
        (S.tailSeries h).determinant := by
  unfold BinarySchurPolynomialSeries.determinant
  rw [S.active_eq_firstFactor_mul_tail h,
    S.offDiag_eq_firstFactor_mul_tail h,
    S.kernel_eq_firstFactor_mul_tail h]
  simp only [tailSeries]
  have hpow :
      (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ^ 2 =
        Polynomial.X ^ (2 * S.firstPositiveEntryOrder h) := by
    calc
      (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ^ 2 =
          Polynomial.X ^ (S.firstPositiveEntryOrder h * 2) :=
        (pow_mul (Polynomial.X : Polynomial R)
          (S.firstPositiveEntryOrder h) 2).symm
      _ = Polynomial.X ^ (2 * S.firstPositiveEntryOrder h) := by
        congr 1
        omega
  calc
    (Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailActive h) *
          (Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailKernel h) -
        (Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailOffDiag h) *
          (Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailOffDiag h) =
      (Polynomial.X ^ S.firstPositiveEntryOrder h) ^ 2 *
        (S.tailActive h * S.tailKernel h -
          S.tailOffDiag h * S.tailOffDiag h) := by ring
    _ = Polynomial.X ^ (2 * S.firstPositiveEntryOrder h) *
        (S.tailActive h * S.tailKernel h -
          S.tailOffDiag h * S.tailOffDiag h) := by rw [hpow]

end ZeroSchurSeries

/-! ## Exact determinant clock for a zero Schur block -/

/-- A zero-constant Schur series whose determinant carries one exact pure
parameter clock up to a clearing factor with nonzero constant coefficient. -/
structure ExactZeroSchurClock (R : Type*) [CommRing R] where
  zeroSeries : ZeroSchurSeries R
  clearingFactor : Polynomial R
  defect : Nat
  clearingFactor_coeff_zero_ne_zero : clearingFactor.coeff 0 ≠ 0
  determinantFactor :
    zeroSeries.series.determinant =
      clearingFactor * Polynomial.X ^ defect

namespace ExactZeroSchurClock

variable [IsDomain R]

/-- A nonzero exact determinant clock forces a positive Schur layer. -/
theorem hasPositiveEntryLayer
    (E : ExactZeroSchurClock R) :
    E.zeroSeries.HasPositiveEntryLayer := by
  by_contra hnone
  have hdet0 := E.zeroSeries.determinant_eq_zero_of_not_hasPositiveEntryLayer hnone
  have hcoeff :
      (E.clearingFactor * Polynomial.X ^ E.defect).coeff E.defect =
        E.clearingFactor.coeff 0 := by
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, ← E.determinantFactor, hdet0]
  simp

/-- First nonzero Schur order. -/
noncomputable def firstOrder (E : ExactZeroSchurClock R) : Nat :=
  E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer

/-- Normalised first-entry tail. -/
noncomputable def tailSeries
    (E : ExactZeroSchurClock R) : BinarySchurPolynomialSeries R :=
  E.zeroSeries.tailSeries E.hasPositiveEntryLayer

 theorem firstOrder_pos (E : ExactZeroSchurClock R) :
    0 < E.firstOrder := by
  exact E.zeroSeries.firstPositiveEntryOrder_pos E.hasPositiveEntryLayer

/-- Exact determinant factorisation after removing the first common Schur
order. -/
theorem determinant_eq_firstFactor_sq_mul_tail
    (E : ExactZeroSchurClock R) :
    E.zeroSeries.series.determinant =
      Polynomial.X ^ (2 * E.firstOrder) * E.tailSeries.determinant := by
  simpa [firstOrder, tailSeries] using
    E.zeroSeries.determinant_eq_firstFactor_sq_mul_tail E.hasPositiveEntryLayer

/-- The first common Schur order cannot consume more than half of the exact
determinant order. -/
theorem twice_firstOrder_le_defect
    (E : ExactZeroSchurClock R) :
    2 * E.firstOrder ≤ E.defect := by
  by_contra hnot
  have hlt : E.defect < 2 * E.firstOrder := Nat.lt_of_not_ge hnot
  have hzero : E.zeroSeries.series.determinant.coeff E.defect = 0 := by
    rw [E.determinant_eq_firstFactor_sq_mul_tail]
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le_of_lt hlt]
  have hcoeff :
      E.zeroSeries.series.determinant.coeff E.defect =
        E.clearingFactor.coeff 0 := by
    rw [E.determinantFactor]
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, hzero]

/-- Residual determinant order after removing the first common Schur factor. -/
def residualDefect (E : ExactZeroSchurClock R) : Nat :=
  E.defect - 2 * E.firstOrder

/-- Cancelling the nonzero first common factor gives the exact determinant
clock of the normalised tail. -/
theorem tail_determinantFactor
    (E : ExactZeroSchurClock R) :
    E.tailSeries.determinant =
      E.clearingFactor * Polynomial.X ^ E.residualDefect := by
  have hle := E.twice_firstOrder_le_defect
  have hsplit :
      E.defect = 2 * E.firstOrder + E.residualDefect := by
    unfold residualDefect
    omega
  have hscaled :
      Polynomial.X ^ (2 * E.firstOrder) * E.tailSeries.determinant =
        Polynomial.X ^ (2 * E.firstOrder) *
          (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
    calc
      Polynomial.X ^ (2 * E.firstOrder) * E.tailSeries.determinant =
          E.zeroSeries.series.determinant :=
        E.determinant_eq_firstFactor_sq_mul_tail.symm
      _ = E.clearingFactor * Polynomial.X ^ E.defect := E.determinantFactor
      _ = Polynomial.X ^ (2 * E.firstOrder) *
          (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
        rw [hsplit, pow_add]
        ring
  exact mul_left_cancel₀
    (pow_ne_zero (2 * E.firstOrder) Polynomial.X_ne_zero)
    hscaled

/-- The normalised first coefficient block is nonzero. -/
theorem tail_constantBlock_nonzero
    (E : ExactZeroSchurClock R) :
    E.tailSeries.ConstantBlockNonzero := by
  simpa [tailSeries] using
    E.zeroSeries.tailSeries_constantBlock_nonzero E.hasPositiveEntryLayer

/-- If some determinant order remains after the first common Schur factor,
the first coefficient block has determinant zero. -/
theorem tail_constant_det_zero_of_residual_pos
    (E : ExactZeroSchurClock R)
    (hres : 0 < E.residualDefect) :
    E.tailSeries.active.coeff 0 * E.tailSeries.kernel.coeff 0 =
      E.tailSeries.offDiag.coeff 0 * E.tailSeries.offDiag.coeff 0 := by
  have hcoeff : E.tailSeries.determinant.coeff 0 = 0 := by
    rw [E.tail_determinantFactor]
    rw [Polynomial.coeff_mul_X_pow']
    simp [Nat.not_le.mpr hres]
  have hzero :
      E.tailSeries.active.coeff 0 * E.tailSeries.kernel.coeff 0 -
        E.tailSeries.offDiag.coeff 0 * E.tailSeries.offDiag.coeff 0 = 0 := by
    simpa [BinarySchurPolynomialSeries.determinant] using hcoeff
  exact sub_eq_zero.mp hzero

/-- Before determinant closure, the first nonzero Schur coefficient is a
rank-one pivot over the coefficient domain. -/
theorem tail_pivot_of_residual_pos
    (E : ExactZeroSchurClock R)
    (hres : 0 < E.residualDefect) :
    E.tailSeries.LeftPivot ∨ E.tailSeries.RightAxisPivot := by
  exact E.tailSeries.leftPivot_or_rightAxisPivot_of_constantBlock
    E.tail_constantBlock_nonzero
    (E.tail_constant_det_zero_of_residual_pos hres)

/-- If no residual determinant order remains, the first coefficient block
is already nondegenerate exactly at closure. -/
theorem tail_constant_det_ne_zero_of_residual_zero
    (E : ExactZeroSchurClock R)
    (hres : E.residualDefect = 0) :
    E.tailSeries.active.coeff 0 * E.tailSeries.kernel.coeff 0 -
        E.tailSeries.offDiag.coeff 0 * E.tailSeries.offDiag.coeff 0 ≠ 0 := by
  have hcoeff :
      E.tailSeries.determinant.coeff 0 = E.clearingFactor.coeff 0 := by
    rw [E.tail_determinantFactor, hres]
    simp [BinarySchurPolynomialSeries.determinant]
  intro hzero
  have hzeroCoeff : E.tailSeries.determinant.coeff 0 = 0 := by
    simpa [BinarySchurPolynomialSeries.determinant] using hzero
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff]
  exact hzeroCoeff

end ExactZeroSchurClock

/-! ## Residual rank-one clock after a zero-Schur first entry -/

/-- Exact rank-one Schur clock independent of any particular frontier. -/
structure ExactRankOneSchurClockAt (R : Type*) [CommRing R] where
  series : RankOneSchurSeries R
  clearingFactor : Polynomial R
  defect : Nat
  leading_ne_zero : series.leading ≠ 0
  clearingFactor_coeff_zero_ne_zero : clearingFactor.coeff 0 ≠ 0
  determinantFactor :
    series.determinant = clearingFactor * Polynomial.X ^ defect

namespace ExactRankOneSchurClockAt

variable [IsDomain R]

 theorem hasTransverse (S : ExactRankOneSchurClockAt R) :
    S.series.HasPositiveTransverseLayer :=
  S.series.hasPositiveTransverseLayer_of_determinant_eq_factor_mul_X_pow
    S.clearingFactor S.defect S.determinantFactor
    S.clearingFactor_coeff_zero_ne_zero

noncomputable def firstOrder (S : ExactRankOneSchurClockAt R) : Nat :=
  S.series.firstPositiveTransverseOrder S.hasTransverse

 theorem firstOrder_pos (S : ExactRankOneSchurClockAt R) :
    0 < S.firstOrder :=
  S.series.firstPositiveTransverseOrder_pos S.hasTransverse

 theorem firstOrder_le_defect (S : ExactRankOneSchurClockAt R) :
    S.firstOrder ≤ S.defect :=
  S.series.firstPositiveTransverseOrder_le_of_determinant_eq_factor_mul_X_pow
    S.hasTransverse S.clearingFactor S.determinantFactor
    S.clearingFactor_coeff_zero_ne_zero

/-- Below closure the first transverse kernel coefficient vanishes. -/
theorem kernel_coeff_firstOrder_eq_zero_of_preterminal
    (S : ExactRankOneSchurClockAt R)
    (hpre : S.firstOrder < S.defect) :
    S.series.kernel.coeff S.firstOrder = 0 := by
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        S.series.leading * S.series.kernel.coeff S.firstOrder := by
    simpa [FirstRankOneSchurDeparture.determinant,
      RankOneSchurSeries.determinant, firstOrder] using
      (S.series.firstDeparture S.hasTransverse).coeff_order_determinant
  have hdet0 : S.series.determinant.coeff S.firstOrder = 0 := by
    rw [S.determinantFactor]
    rw [Polynomial.coeff_mul_X_pow']
    simp [Nat.not_le_of_lt hpre]
  have hprod :
      S.series.leading * S.series.kernel.coeff S.firstOrder = 0 := by
    rw [← hlin]
    exact hdet0
  exact (mul_eq_zero.mp hprod).resolve_left S.leading_ne_zero

/-- Therefore a preterminal first transverse coefficient is necessarily
mixed/off-diagonal and gives strict rank-one to rank-two repair progress. -/
theorem offDiag_coeff_firstOrder_ne_zero_of_preterminal
    (S : ExactRankOneSchurClockAt R)
    (hpre : S.firstOrder < S.defect) :
    S.series.offDiag.coeff S.firstOrder ≠ 0 := by
  rcases S.series.transverse_nonzero_at_first S.hasTransverse with hB | hC
  · exact hB
  · exact False.elim (hC (S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre))

 theorem rankTwoProgress_or_closing
    (S : ExactRankOneSchurClockAt R)
    (complexity : Nat) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      S.series.offDiag.coeff S.firstOrder ≠ 0) ∨
    (S.firstOrder = S.defect ∧
      (S.series.offDiag.coeff S.defect ≠ 0 ∨
       S.series.kernel.coeff S.defect ≠ 0)) := by
  rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
  · left
    exact ⟨rankOne_to_rankTwo_repairProgress complexity,
      S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre⟩
  · right
    refine ⟨hclose, ?_⟩
    have h := S.series.transverse_nonzero_at_first S.hasTransverse
    have hfirst :
        S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
      simpa [firstOrder] using hclose
    rw [hfirst] at h
    exact h

end ExactRankOneSchurClockAt

/-! ## Automatic handoff from the zero-Schur clock to the rank-one clock -/

namespace ExactZeroSchurClock

variable [IsDomain R]

/-- Left-pivot residual tail becomes an exact rank-one Schur clock. -/
noncomputable def toRankOneClockLeft
    (E : ExactZeroSchurClock R)
    (hres : 0 < E.residualDefect)
    (hleft : E.tailSeries.LeftPivot) :
    ExactRankOneSchurClockAt R where
  series := E.tailSeries.alignLeft hleft
  clearingFactor :=
    (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 * E.clearingFactor
  defect := E.residualDefect
  leading_ne_zero := E.tailSeries.alignLeft_leading_ne_zero hleft
  clearingFactor_coeff_zero_ne_zero := by
    have ha : E.tailSeries.active.coeff 0 ≠ 0 := hleft.1
    have hprod :
        (E.tailSeries.active.coeff 0) ^ 2 * E.clearingFactor.coeff 0 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 ha) E.clearingFactor_coeff_zero_ne_zero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hprod
  determinantFactor := by
    calc
      (E.tailSeries.alignLeft hleft).determinant =
          (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 *
            E.tailSeries.determinant :=
        E.tailSeries.alignLeft_determinant hleft
      _ =
          (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 *
            (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
        rw [E.tail_determinantFactor]
      _ =
          ((Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 *
            E.clearingFactor) * Polynomial.X ^ E.residualDefect := by ring

/-- Right-axis residual tail becomes an exact rank-one Schur clock. -/
noncomputable def toRankOneClockRight
    (E : ExactZeroSchurClock R)
    (hres : 0 < E.residualDefect)
    (hright : E.tailSeries.RightAxisPivot) :
    ExactRankOneSchurClockAt R where
  series := E.tailSeries.alignRight hright
  clearingFactor := E.clearingFactor
  defect := E.residualDefect
  leading_ne_zero := E.tailSeries.alignRight_leading_ne_zero hright
  clearingFactor_coeff_zero_ne_zero := E.clearingFactor_coeff_zero_ne_zero
  determinantFactor := by
    calc
      (E.tailSeries.alignRight hright).determinant =
          E.tailSeries.determinant :=
        E.tailSeries.alignRight_determinant hright
      _ = E.clearingFactor * Polynomial.X ^ E.residualDefect :=
        E.tail_determinantFactor

/-- Complete two-stage local clock.  Either the first zero-Schur entry itself
lands exactly at determinant closure, or it produces a rank-one residual
clock; that second clock yields strict rank-two repair progress unless its
first transverse layer is exactly closing. -/
theorem rankTwoProgress_or_closing
    (E : ExactZeroSchurClock R)
    (complexity : Nat) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity)) ∨
    (E.residualDefect = 0 ∧
      E.tailSeries.active.coeff 0 * E.tailSeries.kernel.coeff 0 -
          E.tailSeries.offDiag.coeff 0 * E.tailSeries.offDiag.coeff 0 ≠ 0) ∨
    (∃ S : ExactRankOneSchurClockAt R,
      0 < E.residualDefect ∧
      S.defect = E.residualDefect ∧
      S.firstOrder = S.defect ∧
      (S.series.offDiag.coeff S.defect ≠ 0 ∨
       S.series.kernel.coeff S.defect ≠ 0)) := by
  by_cases hres0 : E.residualDefect = 0
  · exact Or.inr (Or.inl
      ⟨hres0, E.tail_constant_det_ne_zero_of_residual_zero hres0⟩)
  · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
    rcases E.tail_pivot_of_residual_pos hres with hleft | hright
    · let S := E.toRankOneClockLeft hres hleft
      rcases S.rankTwoProgress_or_closing complexity with hprogress | hclose
      · exact Or.inl hprogress.1
      · exact Or.inr (Or.inr
          ⟨S, hres, rfl, hclose.1, hclose.2⟩)
    · let S := E.toRankOneClockRight hres hright
      rcases S.rankTwoProgress_or_closing complexity with hprogress | hclose
      · exact Or.inl hprogress.1
      · exact Or.inr (Or.inr
          ⟨S, hres, rfl, hclose.1, hclose.2⟩)

end ExactZeroSchurClock

/-! ## Direct constructor from an exact four-block -/

/-- A polynomial-valued four-block whose special Schur block is zero and
whose full determinant carries an exact pure parameter clock.  This is the
precise algebraic object the exposed rigid-packet Hessian will supply. -/
structure ExactZeroSchurFourBlockData (R : Type*) [CommRing R] where
  block : GeneralFourBlock (Polynomial R)
  defect : Nat
  fullDet : block.determinantCore = Polynomial.X ^ defect
  activeDet_coeff_zero_ne_zero : block.activeDet.coeff 0 ≠ 0
  schurA_coeff_zero : block.schurA.coeff 0 = 0
  schurB_coeff_zero : block.schurB.coeff 0 = 0
  schurC_coeff_zero : block.schurC.coeff 0 = 0

namespace ExactZeroSchurFourBlockData

/-- Every exact zero-Schur four-block canonically gives the two-stage clock. -/
noncomputable def toClock
    (B : ExactZeroSchurFourBlockData R) : ExactZeroSchurClock R where
  zeroSeries := {
    series := B.block.polynomialSchurSeries
    active_coeff_zero := by
      simpa [GeneralFourBlock.polynomialSchurSeries] using B.schurA_coeff_zero
    offDiag_coeff_zero := by
      simpa [GeneralFourBlock.polynomialSchurSeries] using B.schurB_coeff_zero
    kernel_coeff_zero := by
      simpa [GeneralFourBlock.polynomialSchurSeries] using B.schurC_coeff_zero }
  clearingFactor := B.block.activeDet
  defect := B.defect
  clearingFactor_coeff_zero_ne_zero := B.activeDet_coeff_zero_ne_zero
  determinantFactor := by
    calc
      B.block.polynomialSchurSeries.determinant =
          B.block.activeDet * B.block.determinantCore :=
        B.block.polynomialSchurSeries_determinant
      _ = B.block.activeDet * Polynomial.X ^ B.defect := by
        rw [B.fullDet]

/-- The complete two-stage local dichotomy is therefore automatic from the
four-block data. -/
theorem rankTwoProgress_or_closing
    [IsDomain R]
    (B : ExactZeroSchurFourBlockData R)
    (complexity : Nat) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity)) ∨
    ((B.toClock.residualDefect = 0 ∧
      B.toClock.tailSeries.active.coeff 0 *
          B.toClock.tailSeries.kernel.coeff 0 -
        B.toClock.tailSeries.offDiag.coeff 0 *
          B.toClock.tailSeries.offDiag.coeff 0 ≠ 0) ∨
     (∃ S : ExactRankOneSchurClockAt R,
       0 < B.toClock.residualDefect ∧
       S.defect = B.toClock.residualDefect ∧
       S.firstOrder = S.defect ∧
       (S.series.offDiag.coeff S.defect ≠ 0 ∨
        S.series.kernel.coeff S.defect ≠ 0))) := by
  exact B.toClock.rankTwoProgress_or_closing complexity

end ExactZeroSchurFourBlockData

end

end HC4.Newton
