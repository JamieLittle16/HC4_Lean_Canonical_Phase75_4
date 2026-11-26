import HC4.Polynomial.RationalCharacteristicRankOneBivariateChart

/-!
# Normalized rank-one source contradiction

The chart coefficients of the Euler-gradient equation give the
recurrence of the verified source Hessian obstruction. In the
normalized x/y chart, a polynomial parameter vector with U0 = T U1
and independent components cannot symmetrize a regular polynomial
Hessian via the normalized rank-one factorization.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)

private theorem chartExponent_shift_x (n j l : ℕ) (hn : n ≤ j) :
    rankOne_chartExponent n j l + Finsupp.single 0 1 =
      rankOne_chartExponent (n + 1) (j + 1) l := by
  ext i
  fin_cases i <;> simp [rankOne_chartExponent] <;> omega

private theorem chartExponent_shift_y (n j l : ℕ) (hn : n ≤ j) :
    rankOne_chartExponent n j l + Finsupp.single 1 1 =
      rankOne_chartExponent n (j + 1) l := by
  ext i
  fin_cases i <;> simp [rankOne_chartExponent] <;> omega

private theorem chartExponent_shift_z (n j l : ℕ) :
    rankOne_chartExponent n j l + Finsupp.single 2 1 =
      rankOne_chartExponent n j (l + 1) := by
  ext i
  fin_cases i <;> simp [rankOne_chartExponent]

/-- Exact coefficientwise chain rule in the y direction. -/
theorem rankOne_chartCoeff_pderiv_y
    (f : B K) (j l : ℕ) :
    _root_.Polynomial.X * rankOne_chartCoeff (pderiv 0 f) j l +
      rankOne_chartCoeff (pderiv 1 f) j l =
      _root_.Polynomial.C ((j + 1 : ℕ) : K) *
        rankOne_chartCoeff f (j + 1) l := by
  apply _root_.Polynomial.ext
  intro n
  cases n with
  | zero =>
    simp only [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_X_mul_zero,
      zero_add, _root_.Polynomial.coeff_C_mul, rankOne_chartCoeff_coeff,
      Nat.zero_le, if_true, HC4.Newton.coeff_pderiv_backport]
    rw [chartExponent_shift_y 0 j l (Nat.zero_le _)]
    simp [rankOne_chartExponent, Nat.cast_add]
    <;> ring
  | succ n =>
    simp only [Nat.succ_eq_add_one, _root_.Polynomial.coeff_add,
      _root_.Polynomial.coeff_X_mul, _root_.Polynomial.coeff_C_mul,
      rankOne_chartCoeff_coeff]
    by_cases hn : n + 1 ≤ j
    · have hn0 : n ≤ j := by omega
      have hn1 : n + 1 ≤ j + 1 := by omega
      rw [if_pos hn0, if_pos hn, if_pos hn1]
      simp only [HC4.Newton.coeff_pderiv_backport]
      rw [chartExponent_shift_x n j l hn0, chartExponent_shift_y (n + 1) j l hn]
      have hnat : n + 1 + (j - (n + 1) + 1) = j + 1 := by omega
      have hk := congrArg (fun d : ℕ => (d : K)) hnat
      simp only [Nat.cast_add, Nat.cast_one] at hk
      have hx : rankOne_chartExponent n j l 0 = n := by simp [rankOne_chartExponent]
      have hy : rankOne_chartExponent (n + 1) j l 1 = j - (n + 1) := by
        simp [rankOne_chartExponent]
      rw [hx, hy]
      push_cast
      linear_combination (f.coeff (rankOne_chartExponent (n + 1) (j + 1) l)) * hk
    · by_cases hn0 : n ≤ j
      · have he : n = j := by omega
        subst n
        rw [if_pos (Nat.le_refl _), if_neg (by omega : ¬j + 1 ≤ j),
          if_pos (Nat.le_refl _), add_zero]
        simp only [HC4.Newton.coeff_pderiv_backport]
        rw [chartExponent_shift_x j j l (Nat.le_refl _)]
        simp [rankOne_chartExponent, Nat.cast_add]
        <;> ring
      · have hn1 : ¬ n + 1 ≤ j + 1 := by omega
        rw [if_neg hn0, if_neg hn, if_neg hn1, add_zero, mul_zero]

/-- Exact coefficientwise chain rule in the z direction. -/
theorem rankOne_chartCoeff_pderiv_z
    (f : B K) (j l : ℕ) :
    rankOne_chartCoeff (pderiv 2 f) j l =
      _root_.Polynomial.C ((l + 1 : ℕ) : K) *
        rankOne_chartCoeff f j (l + 1) := by
  apply _root_.Polynomial.ext
  intro n
  simp only [_root_.Polynomial.coeff_C_mul, rankOne_chartCoeff_coeff]
  by_cases hn : n ≤ j
  · rw [if_pos hn, if_pos hn]
    simp only [HC4.Newton.coeff_pderiv_backport]
    rw [chartExponent_shift_z]
    simp [rankOne_chartExponent, Nat.cast_add]
    <;> ring
  · rw [if_neg hn, if_neg hn, mul_zero]

variable [CharZero K]

private theorem rankOne_coeff_euler
    (f : B K) (m : Fin 3 →₀ ℕ) :
    (transverseEuler f).coeff m = (m.degree : K) * f.coeff m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
    have ha : transverseEuler (p + q) = transverseEuler p + transverseEuler q := by
      simp [transverseEuler, map_add, mul_add, Finset.sum_add_distrib]
    rw [ha, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
    ring
  | monomial d a =>
    have hh : (MvPolynomial.monomial d a : B K).IsHomogeneous d.degree :=
      MvPolynomial.isHomogeneous_monomial a rfl
    have he := hh.sum_X_mul_pderiv
    change transverseEuler (MvPolynomial.monomial d a : B K) =
      d.degree • MvPolynomial.monomial d a at he
    rw [he, MvPolynomial.coeff_smul, nsmul_eq_mul]
    by_cases h : m = d
    · subst m
      simp [MvPolynomial.coeff_monomial]
    · simp [MvPolynomial.coeff_monomial, h, Ne.symm h]

/-- Euler minus identity acts by j+l-1 on each chart coefficient. -/
theorem rankOne_chartCoeff_euler_sub
    (f : B K) (j l : ℕ) :
    rankOne_chartCoeff (transverseEuler f - f) j l =
      _root_.Polynomial.C (((j + l : ℕ) : K) - 1) *
        rankOne_chartCoeff f j l := by
  apply _root_.Polynomial.ext
  intro n
  simp only [_root_.Polynomial.coeff_C_mul, rankOne_chartCoeff_coeff]
  by_cases hn : n ≤ j
  · rw [if_pos hn, if_pos hn, MvPolynomial.coeff_sub, rankOne_coeff_euler]
    have hd : (rankOne_chartExponent n j l).degree = j + l := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
      simp [rankOne_chartExponent]
      <;> omega
    rw [hd]
    ring
  · rw [if_neg hn, if_neg hn, mul_zero]

/-- The exact chart Euler equation implies the recurrence on the
original source chart coefficients, with no degree bound assumed. -/
theorem rankOne_chartRecurrence_of_chartEuler
    (f : B K) (U : Fin 3 → _root_.Polynomial K)
    (hU : U 0 = _root_.Polynomial.X * U 1)
    (he : rankOne_normalizedChartTime
      (rankOne_tracePolynomial (transverseEuler f - f) U) = 0)
    (j l : ℕ) (hpos : 1 ≤ j + l) :
    _root_.Polynomial.C ((j + 1 : ℕ) : K) * U 1 *
        rankOne_chartCoeff f (j + 1) l +
      _root_.Polynomial.C ((l + 1 : ℕ) : K) * U 2 *
        rankOne_chartCoeff f j (l + 1) = 0 := by
  let g := transverseEuler f - f
  have h := rankOne_chartCoeff_trace_zero g U he j l
  rw [Fin.sum_univ_three, hU] at h
  have hc : U 1 * (_root_.Polynomial.X * rankOne_chartCoeff (pderiv 0 g) j l +
      rankOne_chartCoeff (pderiv 1 g) j l) +
        U 2 * rankOne_chartCoeff (pderiv 2 g) j l = 0 := by
    linear_combination h
  rw [rankOne_chartCoeff_pderiv_y, rankOne_chartCoeff_pderiv_z] at hc
  change U 1 * (_root_.Polynomial.C ((j + 1 : ℕ) : K) *
      rankOne_chartCoeff (transverseEuler f - f) (j + 1) l) +
    U 2 * (_root_.Polynomial.C ((l + 1 : ℕ) : K) *
      rankOne_chartCoeff (transverseEuler f - f) j (l + 1)) = 0 at hc
  rw [rankOne_chartCoeff_euler_sub, rankOne_chartCoeff_euler_sub] at hc
  have hj : (((j + 1 + l : ℕ) : K) - 1) = ((j + l : ℕ) : K) := by
    push_cast
    ring
  have hl : (((j + (l + 1) : ℕ) : K) - 1) = ((j + l : ℕ) : K) := by
    push_cast
    ring
  rw [hj, hl] at hc
  have hcast : ((j + l : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have hz : _root_.Polynomial.C ((j + l : ℕ) : K) *
    (_root_.Polynomial.C ((j + 1 : ℕ) : K) * U 1 *
      rankOne_chartCoeff f (j + 1) l +
    _root_.Polynomial.C ((l + 1 : ℕ) : K) * U 2 *
      rankOne_chartCoeff f j (l + 1)) = 0 := by
    linear_combination hc
  exact (mul_eq_zero.mp hz).resolve_left (_root_.Polynomial.C_ne_zero.mpr hcast)

/-- The normalized rank-one polynomial factorization with independent
parameter components is incompatible with a regular source Hessian. -/
theorem rankOne_normalized_independent_impossible
    (f : B K) (N : Matrix (Fin 3) (Fin 3) (E K))
    (U : Fin 3 → _root_.Polynomial K)
    (hN : ∀ i j, N i j =
      (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
        rankOne_normalizedRow j)
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N)
    (hU : U 0 = _root_.Polynomial.X * U 1)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U 0 + _root_.Polynomial.C b * U 1 +
        _root_.Polynomial.C c * U 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hreg : (hessian f).det ≠ 0) : False := by
  have he := rankOne_normalized_chartEuler_zero f N U hN hself
  apply rankOne_source_chartRecurrence_impossible f (U 0) (U 1) (U 2)
    hU hind _ hreg
  intro j l hjl
  exact rankOne_chartRecurrence_of_chartEuler f U hU he j l hjl

end
end HC4.Polynomial.RankThreeCubic
