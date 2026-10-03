import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Heterogeneous top coefficients of polynomial products

Mathlib has convenient uniform-degree product lemmas.  The final HC4 mixed
variation instead has factors with two different degree bounds.  This file
records the elementary two-factor and four-factor endpoint formulas once.
-/

namespace HC4.Polynomial

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- If `p` and `q` have degree bounds `m` and `n`, the coefficient at the sum
of those bounds is the product of the corresponding endpoint coefficients. -/
theorem coeff_mul_at_degree_bounds
    {p q : Polynomial R} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  rw [Polynomial.coeff_mul]
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal (m + n)
  let f : ℕ × ℕ → R := fun x => p.coeff x.1 * q.coeff x.2
  have hmn : (m, n) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  rw [show (∑ x ∈ Finset.antidiagonal (m + n),
      p.coeff x.1 * q.coeff x.2) = ∑ x ∈ s, f x by rfl]
  rw [Finset.sum_eq_single (m, n)]
  · rfl
  · intro x hx hne
    have hsum : x.1 + x.2 = m + n :=
      Finset.mem_antidiagonal.mp (by simpa [s] using hx)
    by_cases hxle : x.1 ≤ m
    · have hx2ge : n ≤ x.2 := by omega
      have hx1ne : x.1 ≠ m := by
        intro hxm
        have hx2 : x.2 = n := by omega
        exact hne (Prod.ext hxm hx2)
      have hx1lt : x.1 < m := lt_of_le_of_ne hxle hx1ne
      have hx2gt : n < x.2 := by omega
      have hqzero : q.coeff x.2 = 0 :=
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hq) x.2 hx2gt
      simp [f, hqzero]
    · have hx1gt : m < x.1 := Nat.lt_of_not_ge hxle
      have hpzero : p.coeff x.1 = 0 :=
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp) x.1 hx1gt
      simp [f, hpzero]
  · exact hmn

/-- Four-factor version with separate degree bounds. -/
theorem coeff_mul_four_at_degree_bounds
    {p q r s : Polynomial R} {a b c d : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (hr : r.natDegree ≤ c) (hs : s.natDegree ≤ d) :
    (p * q * r * s).coeff (a + b + c + d) =
      p.coeff a * q.coeff b * r.coeff c * s.coeff d := by
  have hpq : (p * q).natDegree ≤ a + b := by
    exact le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hp hq)
  have hrs : (r * s).natDegree ≤ c + d := by
    exact le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hr hs)
  have htop := coeff_mul_at_degree_bounds
    (p := p * q) (q := r * s) hpq hrs
  rw [show p * q * r * s = (p * q) * (r * s) by ring] at htop
  rw [show a + b + c + d = (a + b) + (c + d) by omega] at htop
  rw [coeff_mul_at_degree_bounds hp hq,
    coeff_mul_at_degree_bounds hr hs] at htop
  simpa [mul_assoc] using htop

end

end HC4.Polynomial
