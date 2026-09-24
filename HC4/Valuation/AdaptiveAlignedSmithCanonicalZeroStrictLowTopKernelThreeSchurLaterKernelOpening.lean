import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurTangentStaircaseSeed
import Mathlib.Tactic

/-!
# Strictly later projected kernel opening in the tangent three-Schur branch

Let j be the first physical reverse-Rees order at which the original Hessian
kernel row opens.  In the tangent branch the cleared 1+3 Schur quotient
kernel column is still zero at that order.

Because the original kernel row is zero at every order below j, every entry
of the projected Schur kernel column is also zero below j.  On the other hand
that whole projected column cannot vanish identically: the exact 3x3 Schur
determinant is a nonzero clearing factor times a pure parameter power.

Hence there is a least projected kernel-column opening order J with

    j < J.

This file records J and its complete lower-order gap.  Thus a tangent first
opening forces a genuinely second, strictly later projected opening on the
same honest ordinary reverse-Rees family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

private theorem tangent_kernelColumn_coeff_zero_of_lt_firstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M)
    (i : Fin 3)
    {n : ℕ}
    (hn : n < M.mixed.layer.order) :
    (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n = 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let j := M.mixed.layer.order
  have hlower := firstBreak_kernelRow_lower_zero' M
  have hqLower : ∀ m : ℕ, m < j → B.q.coeff m = 0 :=
    fun m hm => (hlower m (by simpa [j] using hm)).1
  have hsLower : ∀ m : ℕ, m < j → B.s.coeff m = 0 :=
    fun m hm => (hlower m (by simpa [j] using hm)).2.1
  have hyLower : ∀ m : ℕ, m < j → B.y.coeff m = 0 :=
    fun m hm => (hlower m (by simpa [j] using hm)).2.2.1
  have hzLower : ∀ m : ℕ, m < j → B.z.coeff m = 0 :=
    fun m hm => (hlower m (by simpa [j] using hm)).2.2.2
  have hn' : n < j := by simpa [j] using hn
  by_cases hn0 : n = 0
  · subst n
    exact S.toExactZeroThreeSchurClock.zeroSeries.coeff_zero i 2
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0

  cases S with
  | pivotA hpivot hzero hdet =>
      fin_cases i
      · change (B.a * B.s - B.b * B.q).coeff n = 0
        have has :
            (B.a * B.s).coeff n = B.a.coeff 0 * B.s.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.a B.s (fun m hm => hsLower m (lt_trans hm hn'))
        have hbq :
            (B.b * B.q).coeff n = B.b.coeff 0 * B.q.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.b B.q (fun m hm => hqLower m (lt_trans hm hn'))
        rw [Polynomial.coeff_sub, has, hbq, hsLower n hn', hqLower n hn']
        simp
      · change (B.a * B.y - B.p * B.q).coeff n = 0
        have hay :
            (B.a * B.y).coeff n = B.a.coeff 0 * B.y.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.a B.y (fun m hm => hyLower m (lt_trans hm hn'))
        have hpq :
            (B.p * B.q).coeff n = B.p.coeff 0 * B.q.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.p B.q (fun m hm => hqLower m (lt_trans hm hn'))
        rw [Polynomial.coeff_sub, hay, hpq, hyLower n hn', hqLower n hn']
        simp
      · change (B.a * B.z - B.q * B.q).coeff n = 0
        have haz :
            (B.a * B.z).coeff n = B.a.coeff 0 * B.z.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.a B.z (fun m hm => hzLower m (lt_trans hm hn'))
        have hqq :
            (B.q * B.q).coeff n = 0 :=
          coeff_kernelPair_eq_zero_through
            B.q B.q hnpos
            (fun m hm => hqLower m (lt_trans hm hn'))
            (fun m hm => hqLower m (lt_trans hm hn'))
            n le_rfl
        rw [Polynomial.coeff_sub, haz, hqq, hzLower n hn']
        simp

  | pivotD hpivot hzero hdet =>
      fin_cases i
      · change (B.d * B.q - B.b * B.s).coeff n = 0
        have hdq :
            (B.d * B.q).coeff n = B.d.coeff 0 * B.q.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.d B.q (fun m hm => hqLower m (lt_trans hm hn'))
        have hbs :
            (B.b * B.s).coeff n = B.b.coeff 0 * B.s.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.b B.s (fun m hm => hsLower m (lt_trans hm hn'))
        rw [Polynomial.coeff_sub, hdq, hbs, hqLower n hn', hsLower n hn']
        simp
      · change (B.d * B.y - B.r * B.s).coeff n = 0
        have hdy :
            (B.d * B.y).coeff n = B.d.coeff 0 * B.y.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.d B.y (fun m hm => hyLower m (lt_trans hm hn'))
        have hrs :
            (B.r * B.s).coeff n = B.r.coeff 0 * B.s.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.r B.s (fun m hm => hsLower m (lt_trans hm hn'))
        rw [Polynomial.coeff_sub, hdy, hrs, hyLower n hn', hsLower n hn']
        simp
      · change (B.d * B.z - B.s * B.s).coeff n = 0
        have hdz :
            (B.d * B.z).coeff n = B.d.coeff 0 * B.z.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.d B.z (fun m hm => hzLower m (lt_trans hm hn'))
        have hss :
            (B.s * B.s).coeff n = 0 :=
          coeff_kernelPair_eq_zero_through
            B.s B.s hnpos
            (fun m hm => hsLower m (lt_trans hm hn'))
            (fun m hm => hsLower m (lt_trans hm hn'))
            n le_rfl
        rw [Polynomial.coeff_sub, hdz, hss, hzLower n hn']
        simp

  | pivotX hpivot hzero hdet =>
      fin_cases i
      · change (B.x * B.q - B.p * B.y).coeff n = 0
        have hxq :
            (B.x * B.q).coeff n = B.x.coeff 0 * B.q.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.x B.q (fun m hm => hqLower m (lt_trans hm hn'))
        have hpy :
            (B.p * B.y).coeff n = B.p.coeff 0 * B.y.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.p B.y (fun m hm => hyLower m (lt_trans hm hn'))
        rw [Polynomial.coeff_sub, hxq, hpy, hqLower n hn', hyLower n hn']
        simp
      · change (B.x * B.s - B.r * B.y).coeff n = 0
        have hxs :
            (B.x * B.s).coeff n = B.x.coeff 0 * B.s.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.x B.s (fun m hm => hsLower m (lt_trans hm hn'))
        have hry :
            (B.r * B.y).coeff n = B.r.coeff 0 * B.y.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.r B.y (fun m hm => hyLower m (lt_trans hm hn'))
        rw [Polynomial.coeff_sub, hxs, hry, hsLower n hn', hyLower n hn']
        simp
      · change (B.x * B.z - B.y * B.y).coeff n = 0
        have hxz :
            (B.x * B.z).coeff n = B.x.coeff 0 * B.z.coeff n :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below
            B.x B.z (fun m hm => hzLower m (lt_trans hm hn'))
        have hyy :
            (B.y * B.y).coeff n = 0 :=
          coeff_kernelPair_eq_zero_through
            B.y B.y hnpos
            (fun m hm => hyLower m (lt_trans hm hn'))
            (fun m hm => hyLower m (lt_trans hm hn'))
            n le_rfl
        rw [Polynomial.coeff_sub, hxz, hyy, hzLower n hn']
        simp

/-- In the tangent branch the complete projected kernel column is zero
through the physical first-break order. -/
theorem ThreeSchurTangentAtFirstBreak.kernelColumn_coeff_zero_of_le_firstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M)
    (i : Fin 3)
    {n : ℕ}
    (hn : n ≤ M.mixed.layer.order) :
    (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n = 0 := by
  by_cases hlt : n < M.mixed.layer.order
  · exact tangent_kernelColumn_coeff_zero_of_lt_firstBreak R i hlt
  · have heq : n = M.mixed.layer.order := by omega
    subst n
    fin_cases i
    · exact R.mixed0_zero
    · exact R.mixed1_zero
    · exact R.diagonal_zero

/-- The projected 3x3 Schur kernel column cannot be the zero polynomial
column, because its determinant has an exact nonzero clock. -/
theorem TopKernelThreeSchurClockData.exists_kernelColumn_series_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    ∃ i : Fin 3,
      S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2 ≠ 0 := by
  let E := S.toExactZeroThreeSchurClock
  let Z := E.zeroSeries
  by_contra hnone
  push_neg at hnone
  have hsymm : Z.matrix.IsSymm := by
    simpa [E, Z] using S.exactZeroThreeSchurClock_isSymm
  have h02 : Z.matrix 0 2 = 0 := hnone 0
  have h12 : Z.matrix 1 2 = 0 := hnone 1
  have h22 : Z.matrix 2 2 = 0 := hnone 2
  have h20 : Z.matrix 2 0 = 0 := by
    have hs20 : Z.matrix 2 0 = Z.matrix 0 2 := by
      have h := congrArg
        (fun N : Matrix (Fin 3) (Fin 3)
            (Polynomial (MvPolynomial (Fin 4) K)) => N 0 2) hsymm
      simpa using h
    rw [hs20, h02]
  have h21 : Z.matrix 2 1 = 0 := by
    have hs21 : Z.matrix 2 1 = Z.matrix 1 2 := by
      have h := congrArg
        (fun N : Matrix (Fin 3) (Fin 3)
            (Polynomial (MvPolynomial (Fin 4) K)) => N 1 2) hsymm
      simpa using h
    rw [hs21, h12]
  have hdetzero : Z.matrix.det = 0 := by
    simp [Matrix.det_fin_three, h02, h12, h22, h20, h21]
  have hcoeff :
      (E.clearingFactor * Polynomial.X ^ E.defect).coeff E.defect =
        E.clearingFactor.coeff 0 := by
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, ← E.determinantFactor, hdetzero]
  simp

/-- A later projected kernel-column opening exists after the tangent physical
first break. -/
def ThreeSchurTangentAtFirstBreak.HasLaterKernelOpening
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) : Prop :=
  ∃ n : ℕ, M.mixed.layer.order < n ∧
    ∃ i : Fin 3,
      (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n ≠ 0

theorem ThreeSchurTangentAtFirstBreak.hasLaterKernelOpening
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    R.HasLaterKernelOpening := by
  rcases S.exists_kernelColumn_series_ne_zero with ⟨i, hi⟩
  rcases Polynomial.support_nonempty.mpr hi with ⟨n, hn⟩
  have hcoeff : (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hgt : M.mixed.layer.order < n := by
    by_contra hnot
    have hle : n ≤ M.mixed.layer.order := by omega
    exact hcoeff (R.kernelColumn_coeff_zero_of_le_firstBreak i hle)
  exact ⟨n, hgt, i, hcoeff⟩

/-- Least strictly later projected kernel opening order. -/
noncomputable def ThreeSchurTangentAtFirstBreak.laterKernelOpeningOrder
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) : ℕ := by
  classical
  exact Nat.find R.hasLaterKernelOpening

theorem ThreeSchurTangentAtFirstBreak.laterKernelOpeningOrder_spec
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    M.mixed.layer.order < R.laterKernelOpeningOrder ∧
      ∃ i : Fin 3,
        (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff
          R.laterKernelOpeningOrder ≠ 0 := by
  classical
  exact Nat.find_spec R.hasLaterKernelOpening

theorem ThreeSchurTangentAtFirstBreak.kernelColumn_coeff_zero_of_lt_later
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M)
    (i : Fin 3)
    {n : ℕ}
    (hn : n < R.laterKernelOpeningOrder) :
    (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n = 0 := by
  by_cases hle : n ≤ M.mixed.layer.order
  · exact R.kernelColumn_coeff_zero_of_le_firstBreak i hle
  · have hjn : M.mixed.layer.order < n := by omega
    by_contra hcoeff
    have hcand :
        M.mixed.layer.order < n ∧
          ∃ i : Fin 3,
            (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n ≠ 0 :=
      ⟨hjn, i, hcoeff⟩
    have hmin : R.laterKernelOpeningOrder ≤ n := by
      classical
      unfold laterKernelOpeningOrder
      exact Nat.find_min' R.hasLaterKernelOpening hcand
    omega

/-- The tangent branch therefore carries a strict two-stage physical clock:
the original Hessian kernel row opens at j, while the projected Schur kernel
column first opens at a strictly later order J. -/
structure ThreeSchurTangentLaterKernelOpeningData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1) where
  tangent : ThreeSchurTangentAtFirstBreak S M
  laterOrder : ℕ
  first_lt_later : M.mixed.layer.order < laterOrder
  index : Fin 3
  opens :
    (S.toExactZeroThreeSchurClock.zeroSeries.matrix index 2).coeff laterOrder ≠ 0
  lower_zero :
    ∀ i : Fin 3, ∀ n : ℕ, n < laterOrder →
      (S.toExactZeroThreeSchurClock.zeroSeries.matrix i 2).coeff n = 0

theorem ThreeSchurTangentAtFirstBreak.toLaterKernelOpeningData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    Nonempty (ThreeSchurTangentLaterKernelOpeningData S M) := by
  rcases R.laterKernelOpeningOrder_spec with ⟨hlt, i, hi⟩
  exact ⟨{
    tangent := R
    laterOrder := R.laterKernelOpeningOrder
    first_lt_later := hlt
    index := i
    opens := hi
    lower_zero := fun i n hn =>
      R.kernelColumn_coeff_zero_of_lt_later i hn
  }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
