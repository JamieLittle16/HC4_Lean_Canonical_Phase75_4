import HC4.Newton.PolynomialFirstOpeningTransport
import Mathlib.Tactic

/-!
# Coefficient transport at an explicit shifted factor

If

    p * W = X^m * S

and p has nonzero constant coefficient, then W has no coefficients below m
and its coefficient at m satisfies

    p(0) * W[m] = S[0].

Unlike the first-opening theorem, S[0] is allowed to vanish.  This is the
identity needed to replace aligned Schur pivot constants by honest
whole-family coefficients at the binary base order.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

theorem polynomial_lower_zero_and_coeff_at_shift_of_mul_eq_X_pow_mul
    {p W S : Polynomial R}
    {m : ℕ}
    (hp0 : p.coeff 0 ≠ 0)
    (hEq : p * W = Polynomial.X ^ m * S) :
    (∀ n : ℕ, n < m → W.coeff n = 0) ∧
      p.coeff 0 * W.coeff m = S.coeff 0 := by
  have hProdLower :
      ∀ n : ℕ, n < m → (p * W).coeff n = 0 := by
    intro n hn
    rw [hEq, Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le_of_lt hn]

  have hWLower :
      ∀ n : ℕ, n < m → W.coeff n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        have hconv :
            (p * W).coeff n = p.coeff 0 * W.coeff n := by
          exact coeff_mul_eq_constant_mul_of_right_vanishes_below
            p W (fun k hk => ih k hk (lt_trans hk hn))
        have hz : p.coeff 0 * W.coeff n = 0 := by
          rw [← hconv]
          exact hProdLower n hn
        exact (mul_eq_zero.mp hz).resolve_left hp0

  constructor
  · exact hWLower
  · have hconv :
        (p * W).coeff m = p.coeff 0 * W.coeff m := by
      exact coeff_mul_eq_constant_mul_of_right_vanishes_below
        p W (fun k hk => hWLower k hk)
    have hright :
        (Polynomial.X ^ m * S).coeff m = S.coeff 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      simp
    calc
      p.coeff 0 * W.coeff m = (p * W).coeff m := hconv.symm
      _ = (Polynomial.X ^ m * S).coeff m := by rw [hEq]
      _ = S.coeff 0 := hright

end

end HC4.Newton
