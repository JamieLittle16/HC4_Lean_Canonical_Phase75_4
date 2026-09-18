import Mathlib.Tactic

/-!
# Adjacent deficits cannot lie on one finite-staircase source layer

For the left non-unit staircase, every honest source exponent satisfies the
deficit chord equation

    ell * e1 + (n-1) * e2
      = ell * (n-1) + (ell+n-1) * (1-e0).

If two source exponents have adjacent deficit pairs

    (f1,f2) = (e1+1,e2-1),

then subtracting their chord equations gives

    ell - (n-1) = (ell+n-1) * (e0-f0).

The left side is strictly positive but strictly smaller than ell+n-1 when
2 <= n <= ell, whereas the right side is an integer multiple of that
larger positive number. Hence such adjacent deficit pairs are impossible.

This is state-free arithmetic.
-/

namespace HC4.Polynomial

noncomputable section

/-- **No adjacent equal-total-deficit points on the live staircase chord.** -/
theorem no_adjacent_deficits_on_staircase_chord
    {ell n e0 e1 e2 f0 f1 f2 : ℕ}
    (hn : 2 ≤ n)
    (hnell : n ≤ ell)
    (he :
      (ell : ℤ) * (e1 : ℤ) +
          ((n : ℤ) - 1) * (e2 : ℤ) =
        (ell : ℤ) * ((n : ℤ) - 1) +
          ((ell : ℤ) + (n : ℤ) - 1) * (1 - (e0 : ℤ)))
    (hf :
      (ell : ℤ) * (f1 : ℤ) +
          ((n : ℤ) - 1) * (f2 : ℤ) =
        (ell : ℤ) * ((n : ℤ) - 1) +
          ((ell : ℤ) + (n : ℤ) - 1) * (1 - (f0 : ℤ)))
    (hf1 : f1 = e1 + 1)
    (he2 : e2 = f2 + 1) :
    False := by
  have hnZ : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hnellZ : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
  have hstepPos :
      (0 : ℤ) < (ell : ℤ) - ((n : ℤ) - 1) := by
    omega
  have hlevelPos :
      (0 : ℤ) < (ell : ℤ) + (n : ℤ) - 1 := by
    omega
  have hstepLt :
      (ell : ℤ) - ((n : ℤ) - 1) <
        (ell : ℤ) + (n : ℤ) - 1 := by
    omega
  have hf1Z : (f1 : ℤ) = (e1 : ℤ) + 1 := by
    exact_mod_cast hf1
  have he2Z : (e2 : ℤ) = (f2 : ℤ) + 1 := by
    exact_mod_cast he2
  have hmultiple :
      (ell : ℤ) - ((n : ℤ) - 1) =
        ((ell : ℤ) + (n : ℤ) - 1) *
          ((e0 : ℤ) - (f0 : ℤ)) := by
    nlinarith [he, hf]
  have hdiffPos : (0 : ℤ) < (e0 : ℤ) - (f0 : ℤ) := by
    by_contra hnot
    have hnonpos : (e0 : ℤ) - (f0 : ℤ) ≤ 0 := le_of_not_gt hnot
    have hprodNonpos :
        ((ell : ℤ) + (n : ℤ) - 1) *
            ((e0 : ℤ) - (f0 : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlevelPos) hnonpos
    rw [← hmultiple] at hprodNonpos
    exact (not_le_of_gt hstepPos) hprodNonpos
  have hdiffOne : (1 : ℤ) ≤ (e0 : ℤ) - (f0 : ℤ) := by
    omega
  have hlevelLe :
      (ell : ℤ) + (n : ℤ) - 1 ≤
        ((ell : ℤ) + (n : ℤ) - 1) *
          ((e0 : ℤ) - (f0 : ℤ)) := by
    have h := mul_le_mul_of_nonneg_left hdiffOne (le_of_lt hlevelPos)
    simpa using h
  rw [← hmultiple] at hlevelLe
  exact (not_le_of_gt hstepLt) hlevelLe

end

end HC4.Polynomial
