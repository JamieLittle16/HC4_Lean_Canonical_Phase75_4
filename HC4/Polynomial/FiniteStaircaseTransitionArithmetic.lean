import Mathlib.Tactic

/-!
# Finite staircase transition arithmetic

This file isolates the integer contradiction at the only possible transition
between the two characteristic roofs of the final A19 `(1,V)` staircase.

Write `n` for the primitive highest pair degree and `ell` for the locked
height. Every strict-interior quotient fibre `(k,j)` satisfies

    (n-1) j = ell (n-k).

At a transition from the rising roof to the falling roof, the extremal Hessian
coefficient at the rising endpoint forces the missing coordinate of the first
falling endpoint to be exactly one, hence `k₁ = j₁`. Running the same
extremal coefficient from the falling endpoint backwards forces
`k₀ = j₀ + 2`.

The two wall equations would then imply

    (n-1+ell) (j₁-j₀) = 2 ell.

In the live branch `2 <= n <= ell`. Since `j₀ < j₁`, the gap is either one or
at least two. Gap one would force `ell = n-1`, contradicting `n <= ell`;
gap at least two makes the left hand side strictly larger than `2 ell`.

No HC4 state, Rees parameter, Hessian package, or JC2 hypothesis occurs here.
-/

namespace HC4.Polynomial

noncomputable section

/-- **No unit two-sided transition on the finite staircase.**

This is the arithmetic endpoint of the finite-staircase coupling argument.
The wall equalities are kept in the same integer form used by the live A19
staircase theorem, so the source-facing adapter does not need divisibility or
gcd normalization. -/
theorem no_left_staircase_unit_transition
    {n ell k₀ j₀ k₁ j₁ : ℕ}
    (hn : 2 ≤ n)
    (hnell : n ≤ ell)
    (hj : j₀ < j₁)
    (hwall₀ :
      ((n : ℤ) - 1) * (j₀ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k₀ : ℤ)))
    (hwall₁ :
      ((n : ℤ) - 1) * (j₁ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k₁ : ℤ)))
    (hy₀ : k₀ = j₀ + 2)
    (hz₁ : k₁ = j₁) : False := by
  have hy₀Z : (k₀ : ℤ) = (j₀ : ℤ) + 2 := by
    exact_mod_cast hy₀
  have hz₁Z : (k₁ : ℤ) = (j₁ : ℤ) := by
    exact_mod_cast hz₁
  have hL :
      (((n : ℤ) - 1) + (ell : ℤ)) * (j₀ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - 2) := by
    rw [hy₀Z] at hwall₀
    nlinarith
  have hR :
      (((n : ℤ) - 1) + (ell : ℤ)) * (j₁ : ℤ) =
        (ell : ℤ) * (n : ℤ) := by
    rw [hz₁Z] at hwall₁
    nlinarith
  have hdiff :
      (((n : ℤ) - 1) + (ell : ℤ)) *
          ((j₁ : ℤ) - (j₀ : ℤ)) =
        2 * (ell : ℤ) := by
    nlinarith [hL, hR]
  have hjZ : (j₀ : ℤ) < (j₁ : ℤ) := by
    exact_mod_cast hj
  have hnZ : (2 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hn
  have hnellZ : (n : ℤ) ≤ (ell : ℤ) := by
    exact_mod_cast hnell
  by_cases hadj : j₁ = j₀ + 1
  · have hadjZ : (j₁ : ℤ) = (j₀ : ℤ) + 1 := by
      exact_mod_cast hadj
    have hdelta : (j₁ : ℤ) - (j₀ : ℤ) = 1 := by
      linarith
    rw [hdelta] at hdiff
    nlinarith
  · have hgapNat : j₀ + 2 ≤ j₁ := by
      omega
    have hgapCast : ((j₀ + 2 : ℕ) : ℤ) ≤ (j₁ : ℤ) := by
      exact_mod_cast hgapNat
    have hgap : (2 : ℤ) ≤ (j₁ : ℤ) - (j₀ : ℤ) := by
      push_cast at hgapCast
      omega
    have hs :
        (ell : ℤ) + 1 ≤ ((n : ℤ) - 1) + (ell : ℤ) := by
      nlinarith
    have hdelta_nonneg :
        (0 : ℤ) ≤ (j₁ : ℤ) - (j₀ : ℤ) := by
      linarith
    have hell1_nonneg : (0 : ℤ) ≤ (ell : ℤ) + 1 := by
      positivity
    have hp :
        2 * ((ell : ℤ) + 1) ≤
          (((n : ℤ) - 1) + (ell : ℤ)) *
            ((j₁ : ℤ) - (j₀ : ℤ)) := by
      calc
        2 * ((ell : ℤ) + 1) ≤
            ((j₁ : ℤ) - (j₀ : ℤ)) * ((ell : ℤ) + 1) := by
          exact mul_le_mul_of_nonneg_right hgap hell1_nonneg
        _ ≤
            ((j₁ : ℤ) - (j₀ : ℤ)) *
              (((n : ℤ) - 1) + (ell : ℤ)) := by
          exact mul_le_mul_of_nonneg_left hs hdelta_nonneg
        _ = (((n : ℤ) - 1) + (ell : ℤ)) *
              ((j₁ : ℤ) - (j₀ : ℤ)) := by ring
    rw [hdiff] at hp
    nlinarith

end

end HC4.Polynomial
