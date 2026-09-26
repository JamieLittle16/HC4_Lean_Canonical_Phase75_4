import HC4.Newton.FirstSchurLayerLinearization
import Mathlib.Tactic

/-!
# First-order transport through a polynomial factor with nonzero constant term

If a polynomial factor `p` has nonzero constant coefficient, multiplication
by `p` cannot change the least nonzero order of a second factor.

The form needed by the HC4 nested-Schur seam is slightly shifted:

    p * W = X^m * S.

If `S` vanishes below `r` and opens at `r`, then `W` vanishes below
`m+r` and opens exactly at `m+r`.

This is proved coefficientwise and requires only a domain.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Transport an exact first opening through multiplication by a factor with
nonzero constant coefficient and an explicit power of `X`. -/
theorem polynomial_firstOpening_of_mul_eq_X_pow_mul
    {p W S : Polynomial R}
    {m r : ℕ}
    (hp0 : p.coeff 0 ≠ 0)
    (hEq : p * W = Polynomial.X ^ m * S)
    (hLower : ∀ n : ℕ, n < r → S.coeff n = 0)
    (hOpen : S.coeff r ≠ 0) :
    (∀ n : ℕ, n < m + r → W.coeff n = 0) ∧
      W.coeff (m + r) ≠ 0 := by
  have hProdLower :
      ∀ n : ℕ, n < m + r → (p * W).coeff n = 0 := by
    intro n hn
    rw [hEq, Polynomial.coeff_X_pow_mul']
    by_cases hmn : m ≤ n
    · simp only [if_pos hmn]
      apply hLower
      omega
    · simp [hmn]

  have hWLower :
      ∀ n : ℕ, n < m + r → W.coeff n = 0 := by
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
        (p * W).coeff (m + r) =
          p.coeff 0 * W.coeff (m + r) := by
      exact coeff_mul_eq_constant_mul_of_right_vanishes_below
        p W (fun k hk => hWLower k hk)
    have hright :
        (Polynomial.X ^ m * S).coeff (m + r) = S.coeff r := by
      rw [Polynomial.coeff_X_pow_mul']
      simp
    intro hzero
    apply hOpen
    rw [← hright, ← hEq, hconv, hzero]
    simp

end

end HC4.Newton
