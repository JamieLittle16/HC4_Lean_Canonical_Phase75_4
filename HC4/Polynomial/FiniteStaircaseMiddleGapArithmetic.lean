import Mathlib.Tactic

/-!
# Middle-staircase endpoint-gap arithmetic

On the middle diagonal `j+1=k`, write

    q = n-k,   r = k-1.

The wall equation is

    (n-1)(k-1) = ell(n-k).

In the live non-unit contact range one also has `n <= ell`.  In fact the
locked-side gap is strictly larger than the pair-Rees gap:

    n-k < k-1.

Indeed `n-1 < ell`, and if `k-1 <= n-k` then multiplying by the positive
factors would force the left side of the wall strictly below its right side.
-/

namespace HC4.Polynomial

/-- **The locked-side middle gap is strictly larger than the pair gap.** -/
theorem middle_pairGap_lt_lockedGap
    {n ell k : ℕ}
    (hnell : n ≤ ell)
    (hk : 1 < k)
    (hkn : k < n)
    (hwall : (n - 1) * (k - 1) = ell * (n - k)) :
    n - k < k - 1 := by
  by_contra hnot
  have hrle : k - 1 ≤ n - k := Nat.le_of_not_gt hnot
  have hNlt : n - 1 < ell := by omega
  have hqpos : 0 < n - k := by omega
  have hle :
      (n - 1) * (k - 1) ≤ (n - 1) * (n - k) :=
    Nat.mul_le_mul_left (n - 1) hrle
  have hlt :
      (n - 1) * (n - k) < ell * (n - k) :=
    Nat.mul_lt_mul_of_pos_right hNlt hqpos
  omega

/-- In particular, the two middle endpoint gaps are distinct. -/
theorem middle_pairGap_ne_lockedGap
    {n ell k : ℕ}
    (hnell : n ≤ ell)
    (hk : 1 < k)
    (hkn : k < n)
    (hwall : (n - 1) * (k - 1) = ell * (n - k)) :
    n - k ≠ k - 1 := by
  exact Nat.ne_of_lt (middle_pairGap_lt_lockedGap hnell hk hkn hwall)

end HC4.Polynomial
