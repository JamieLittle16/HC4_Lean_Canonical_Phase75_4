import Mathlib.Tactic

/-!
# Middle-staircase endpoint-gap arithmetic

On the middle diagonal `j+1=k`, write

    q = n-k,   r = k-1.

The wall equation is

    (n-1)(k-1) = ell(n-k).

In the live non-unit contact range one also has `n <= ell`.  Therefore `q=r`
is impossible: it would cancel the positive factor `k-1` from the wall and
give `ell=n-1`, contradicting `n <= ell`.
-/

namespace HC4.Polynomial

/-- **The two middle endpoint gaps are distinct.** -/
theorem middle_pairGap_ne_lockedGap
    {n ell k : ℕ}
    (hnell : n ≤ ell)
    (hk : 1 < k)
    (hkn : k < n)
    (hwall : (n - 1) * (k - 1) = ell * (n - k)) :
    n - k ≠ k - 1 := by
  intro hgap
  have hpos : 0 < k - 1 := by omega
  have hcancel : (n - 1) * (k - 1) = ell * (k - 1) := by
    simpa [hgap] using hwall
  have hell : n - 1 = ell := by
    exact Nat.eq_of_mul_eq_mul_right hpos hcancel
  omega

end HC4.Polynomial
