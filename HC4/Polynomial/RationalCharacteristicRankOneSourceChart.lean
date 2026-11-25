import HC4.Polynomial.RationalCharacteristicRankOneChartObstruction

/-!
# Actual source coefficients in the normalized affine parameter chart

The coefficient of y^j z^l in f(T y,y,z) is an explicit polynomial in
T whose nth coefficient is the source coefficient at x^n y^(j-n) z^l.
The construction supplies the degree bounds and recovers the original
source coefficients. The verified chart recurrence obstruction therefore
forces the actual source Hessian to vanish.

Deriving the recurrence from the source Hessian symmetry and reducing
an arbitrary affine ratio to this chart remain separate obligations.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- The source exponent corresponding to the T^n y^j z^l coefficient
after the substitution x = T y. Used only with n <= j. -/
def rankOne_chartExponent (n j l : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 n + Finsupp.single 1 (j - n) + Finsupp.single 2 l

/-- The actual coefficient of y^j z^l in the normalized chart. -/
def rankOne_chartCoeff (f : B K) (j l : ℕ) : _root_.Polynomial K :=
  ∑ n ∈ Finset.range (j + 1),
    _root_.Polynomial.monomial n (f.coeff (rankOne_chartExponent n j l))

/-- Each time coefficient is precisely the corresponding source
coefficient, or zero if its time degree exceeds its y degree. -/
theorem rankOne_chartCoeff_coeff (f : B K) (j l n : ℕ) :
    (rankOne_chartCoeff f j l).coeff n =
      if n ≤ j then f.coeff (rankOne_chartExponent n j l) else 0 := by
  classical
  unfold rankOne_chartCoeff
  rw [_root_.Polynomial.finset_sum_coeff]
  by_cases hn : n ≤ j
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      simp [_root_.Polynomial.coeff_monomial, hb, Ne.symm hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hb' := Finset.mem_range.mp hb
    have hne : b ≠ n := by omega
    simp [_root_.Polynomial.coeff_monomial, hne, Ne.symm hne]

/-- Polynomiality of the original source supplies the full degree
bound of the chart coefficient family. -/
theorem rankOne_chartCoeff_natDegree_le (f : B K) (j l : ℕ) :
    (rankOne_chartCoeff f j l).natDegree ≤ j := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [rankOne_chartCoeff_coeff, if_neg (Nat.not_le.mpr hn)]

/-- Every original monomial is recovered from the chart coefficient
at its combined x,y degree and its z degree. -/
theorem rankOne_chartCoeff_recovers_source (f : B K) (m : Fin 3 →₀ ℕ) :
    (rankOne_chartCoeff f (m 0 + m 1) (m 2)).coeff (m 0) = f.coeff m := by
  have hm : rankOne_chartExponent (m 0) (m 0 + m 1) (m 2) = m := by
    ext i
    fin_cases i <;> simp [rankOne_chartExponent, Finsupp.single_apply]
  rw [rankOne_chartCoeff_coeff, if_pos (Nat.le_add_right _ _), hm]

variable [CharZero K]

/-- The abstract chart recurrence implies vanishing of all actual
source coefficients of total degree at least two. -/
theorem rankOne_source_coeff_zero_of_chartRecurrence
    (f : B K) (U0 U1 U2 : _root_.Polynomial K)
    (hU : U0 = _root_.Polynomial.X * U1)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U0 + _root_.Polynomial.C b * U1 +
        _root_.Polynomial.C c * U2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hrec : ∀ j l : ℕ, 1 ≤ j + l →
      _root_.Polynomial.C ((j + 1 : ℕ) : K) * U1 *
          rankOne_chartCoeff f (j + 1) l +
        _root_.Polynomial.C ((l + 1 : ℕ) : K) * U2 *
          rankOne_chartCoeff f j (l + 1) = 0)
    (m : Fin 3 →₀ ℕ) (hm : 2 ≤ m 0 + m 1 + m 2) :
    f.coeff m = 0 := by
  have h0 (l : ℕ) : (rankOne_chartCoeff f 0 l).natDegree = 0 :=
    Nat.eq_zero_of_le_zero (rankOne_chartCoeff_natDegree_le f 0 l)
  have hz := rankOne_chart_coefficients_zero_of_independent U0 U1 U2
    (rankOne_chartCoeff f) hU hind h0
    (rankOne_chartCoeff_natDegree_le f 1) hrec (m 0 + m 1) (m 2) hm
  rw [← rankOne_chartCoeff_recovers_source f m, hz, _root_.Polynomial.coeff_zero]

/-- The coefficient obstruction forces the actual source Hessian
to vanish, not merely a formally affine expression in a chart. -/
theorem rankOne_source_hessian_zero_of_chartRecurrence
    (f : B K) (U0 U1 U2 : _root_.Polynomial K)
    (hU : U0 = _root_.Polynomial.X * U1)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U0 + _root_.Polynomial.C b * U1 +
        _root_.Polynomial.C c * U2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hrec : ∀ j l : ℕ, 1 ≤ j + l →
      _root_.Polynomial.C ((j + 1 : ℕ) : K) * U1 *
          rankOne_chartCoeff f (j + 1) l +
        _root_.Polynomial.C ((l + 1 : ℕ) : K) * U2 *
          rankOne_chartCoeff f j (l + 1) = 0) :
    hessian f = 0 := by
  classical
  apply Matrix.ext
  intro i j
  apply MvPolynomial.ext
  intro m
  simp only [Matrix.zero_apply, MvPolynomial.coeff_zero, hessian_apply,
    HC4.Newton.coeff_pderiv_backport]
  have hsum : 2 ≤
      (m + Finsupp.single j 1 + Finsupp.single i 1) 0 +
      (m + Finsupp.single j 1 + Finsupp.single i 1) 1 +
      (m + Finsupp.single j 1 + Finsupp.single i 1) 2 := by
    fin_cases i <;> fin_cases j <;>
      simp [Finsupp.single_apply] <;> omega
  rw [rankOne_source_coeff_zero_of_chartRecurrence f U0 U1 U2 hU hind hrec _ hsum,
    zero_mul, zero_mul]

/-- A regular source Hessian is incompatible with the chart
recurrence and an independent parameter derivative vector. -/
theorem rankOne_source_chartRecurrence_impossible
    (f : B K) (U0 U1 U2 : _root_.Polynomial K)
    (hU : U0 = _root_.Polynomial.X * U1)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U0 + _root_.Polynomial.C b * U1 +
        _root_.Polynomial.C c * U2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hrec : ∀ j l : ℕ, 1 ≤ j + l →
      _root_.Polynomial.C ((j + 1 : ℕ) : K) * U1 *
          rankOne_chartCoeff f (j + 1) l +
        _root_.Polynomial.C ((l + 1 : ℕ) : K) * U2 *
          rankOne_chartCoeff f j (l + 1) = 0)
    (hreg : (hessian f).det ≠ 0) : False := by
  apply hreg
  rw [rankOne_source_hessian_zero_of_chartRecurrence f U0 U1 U2 hU hind hrec]
  simp

end
end HC4.Polynomial.RankThreeCubic
