import Mathlib.Tactic

/-!
# One-fibre finite-staircase resonance arithmetic

The remaining one-fibre determinant calculation naturally produces the
balanced second-order resonance

    n - 1 = 2 * (n - k),

which is equivalent, for an interior pair degree `1 < k < n`, to equality of
the two endpoint distances

    k - 1 = n - k.

This file records what that resonance does on the three diagonals already
forced by the dual endpoint Euler equations.

* middle `j+1=k`: impossible with `n <= ell`;
* lower  `j+2=k`: impossible with `n <= ell`;
* upper  `j=k`: the only arithmetic survivor is

      n = 2*k - 1,   ell = 2*k.

No Hessian, Rees family, or HC4 state occurs here.
-/

namespace HC4.Polynomial

noncomputable section

private theorem balanced_distance_of_resonance
    {n k : ℕ}
    (hk : 1 < k) (hkn : k < n)
    (hres : n - 1 = 2 * (n - k)) :
    k - 1 = n - k := by
  omega

/-- The balanced quadratic resonance is incompatible with the middle diagonal
`j+1=k` and the live endpoint separation `n <= ell`. -/
theorem no_middle_oneFiber_balanced_resonance
    {n ell k : ℕ}
    (hnell : n ≤ ell)
    (hk : 1 < k) (hkn : k < n)
    (hwall :
      ((n : ℤ) - 1) * ((k : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ)))
    (hres : n - 1 = 2 * (n - k)) : False := by
  have hbalNat : k - 1 = n - k :=
    balanced_distance_of_resonance hk hkn hres
  have hbalZ : (k : ℤ) - 1 = (n : ℤ) - (k : ℤ) := by
    rw [← Nat.cast_sub (show 1 ≤ k by omega),
      ← Nat.cast_sub (show k ≤ n by omega)]
    exact_mod_cast hbalNat
  have hkpos : (0 : ℤ) < (k : ℤ) - 1 := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hnellZ : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
  nlinarith [hwall]

/-- The same balanced resonance is impossible on the lower diagonal
`j+2=k`. -/
theorem no_lower_oneFiber_balanced_resonance
    {n ell k : ℕ}
    (hnell : n ≤ ell)
    (hk : 2 < k) (hkn : k < n)
    (hwall :
      ((n : ℤ) - 1) * ((k : ℤ) - 2) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ)))
    (hres : n - 1 = 2 * (n - k)) : False := by
  have hk1 : 1 < k := by omega
  have hbalNat : k - 1 = n - k :=
    balanced_distance_of_resonance hk1 hkn hres
  have hbalZ : (k : ℤ) - 1 = (n : ℤ) - (k : ℤ) := by
    rw [← Nat.cast_sub (show 1 ≤ k by omega),
      ← Nat.cast_sub (show k ≤ n by omega)]
    exact_mod_cast hbalNat
  have hresZ : (n : ℤ) - 1 = 2 * ((n : ℤ) - (k : ℤ)) := by
    have hn1 : 1 ≤ n := by omega
    have hknle : k ≤ n := by omega
    rw [← Nat.cast_sub hn1, ← Nat.cast_mul,
      ← Nat.cast_sub hknle]
    exact_mod_cast hres
  have hkpos : (0 : ℤ) < (k : ℤ) - 1 := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hnellZ : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
  nlinarith [hwall]

/-- On the upper diagonal `j=k`, balanced resonance has one exact arithmetic
shape.  This is the sole one-fibre resonance that must be eliminated by an
additional mixed determinant coefficient. -/
theorem upper_oneFiber_balanced_resonance_shape
    {n ell k : ℕ}
    (hk : 1 < k) (hkn : k < n)
    (hwall :
      ((n : ℤ) - 1) * (k : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ)))
    (hres : n - 1 = 2 * (n - k)) :
    n = 2 * k - 1 ∧ ell = 2 * k := by
  have hbalNat : k - 1 = n - k :=
    balanced_distance_of_resonance hk hkn hres
  have hnshape : n = 2 * k - 1 := by omega
  have hbalZ : (k : ℤ) - 1 = (n : ℤ) - (k : ℤ) := by
    rw [← Nat.cast_sub (show 1 ≤ k by omega),
      ← Nat.cast_sub (show k ≤ n by omega)]
    exact_mod_cast hbalNat
  have hnshapeZ : (n : ℤ) = 2 * (k : ℤ) - 1 := by
    exact_mod_cast hnshape
  have hkpos : (0 : ℤ) < (k : ℤ) - 1 := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hellZ : (ell : ℤ) = 2 * (k : ℤ) := by
    nlinarith [hwall]
  refine ⟨hnshape, ?_⟩
  exact_mod_cast hellZ

end

end HC4.Polynomial
