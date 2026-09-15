import Mathlib.Tactic

/-!
# Cross-roof arithmetic on the finite staircase

For two distinct points on the left `(1,V)` staircase

    (n-1) j = ell (n-k),      n <= ell,

write `(kLo,jLo)` for the lower pair-degree point and `(kHi,jHi)` for the
higher pair-degree point.  The staircase is steeper than slope `-1` because
`ell > n-1`, so the transverse-height drop is strictly larger than the
pair-degree gain.

When the lower point lies on the `y=0` roof and the higher point lies on the
`z=0` roof, the two positive residual coordinates are

    q = jLo + 1 - kLo,
    v = kHi - jHi - 1.

The identities below translate the exceptional affine-line directions from
the rank-three terminal stack into this arithmetic.  They are state-free and
contain no HC4 objects.
-/

namespace HC4.Polynomial

noncomputable section

/-- Along the live non-unit staircase, transverse height falls strictly faster
than pair degree rises. -/
theorem staircase_heightDrop_gt_pairGain
    {n ell kLo jLo kHi jHi : ℕ}
    (hn : 2 ≤ n) (hnell : n ≤ ell)
    (hk : kLo < kHi)
    (hLo :
      ((n : ℤ) - 1) * (jLo : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kLo : ℤ)))
    (hHi :
      ((n : ℤ) - 1) * (jHi : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kHi : ℤ))) :
    kHi - kLo < jLo - jHi := by
  have hn1pos : (0 : ℤ) < (n : ℤ) - 1 := by
    exact_mod_cast (show 1 < n by omega)
  have hellgt : (n : ℤ) - 1 < (ell : ℤ) := by
    have hnellZ : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
    omega
  have hkZ : (kLo : ℤ) < (kHi : ℤ) := by exact_mod_cast hk
  have hjZ : (jHi : ℤ) < (jLo : ℤ) := by
    nlinarith [hLo, hHi]
  have hdiff :
      ((n : ℤ) - 1) * ((jLo : ℤ) - (jHi : ℤ)) =
        (ell : ℤ) * ((kHi : ℤ) - (kLo : ℤ)) := by
    nlinarith [hLo, hHi]
  have hpairpos : (0 : ℤ) < (kHi : ℤ) - (kLo : ℤ) := by linarith
  have hlt :
      ((n : ℤ) - 1) * ((kHi : ℤ) - (kLo : ℤ)) <
        (ell : ℤ) * ((kHi : ℤ) - (kLo : ℤ)) :=
    mul_lt_mul_of_pos_right hellgt hpairpos
  have hdrop :
      (kHi : ℤ) - (kLo : ℤ) < (jLo : ℤ) - (jHi : ℤ) := by
    nlinarith [hdiff, hlt, hn1pos]
  have hkNat : kLo ≤ kHi := Nat.le_of_lt hk
  have hjNat : jHi ≤ jLo := by exact Nat.le_of_lt (by exact_mod_cast hjZ)
  exact_mod_cast (show
    ((kHi - kLo : ℕ) : ℤ) < ((jLo - jHi : ℕ) : ℤ) by
      rw [Nat.cast_sub hkNat, Nat.cast_sub hjNat]
      exact hdrop)

/-- The two cross-roof residuals add to the pair gain plus the height drop. -/
theorem crossRoof_residual_sum
    {kLo jLo kHi jHi q v : ℕ}
    (hk : kLo ≤ kHi) (hj : jHi ≤ jLo)
    (hq : q = jLo + 1 - kLo)
    (hv : v = kHi - jHi - 1)
    (hqpos : 0 < q) (hvpos : 0 < v) :
    q + v = (kHi - kLo) + (jLo - jHi) := by
  have hkLo : kLo ≤ jLo + 1 := by omega
  have hjHi : jHi + 1 ≤ kHi := by omega
  omega

/-- Constant source `x` along a cross-roof segment is exactly the equality
`q = heightDrop`. -/
theorem crossRoof_fixed_x_iff
    {kLo jLo kHi jHi q : ℕ}
    (hq : q = jLo + 1 - kLo)
    (hqpos : 0 < q) :
    jHi + 1 = kLo ↔ q = jLo - jHi := by
  have hkLo : kLo ≤ jLo + 1 := by omega
  constructor <;> intro h <;> omega

/-- Constant source `w` along a cross-roof segment is exactly the equality
`q = pairGain`. -/
theorem crossRoof_fixed_w_iff
    {kLo jLo kHi q : ℕ}
    (hk : kLo ≤ kHi)
    (hq : q = jLo + 1 - kLo)
    (hqpos : 0 < q) :
    kHi = jLo + 1 ↔ q = kHi - kLo := by
  have hkLo : kLo ≤ jLo + 1 := by omega
  constructor <;> intro h <;> omega

/-- On staircase exponents, fixed `w` is also exactly ordinary-degree
preservation between a falling-roof point and a rising-roof point. -/
theorem crossRoof_fixed_w_iff_ordinaryDegree
    {V kLo jLo kHi jHi : ℕ} :
    V * jLo + kLo + (jLo + 1 - kLo) =
        V * (kHi - 1) + (jHi + 1) + (kHi - jHi - 1) ↔
      kHi = jLo + 1 := by
  omega

/-- The fixed-`x` and fixed-`w` exceptional directions cannot occur together
on two distinct live staircase fibres. -/
theorem no_crossRoof_fixed_x_and_fixed_w
    {n ell kLo jLo kHi jHi : ℕ}
    (hn : 2 ≤ n) (hnell : n ≤ ell)
    (hk : kLo < kHi)
    (hLo :
      ((n : ℤ) - 1) * (jLo : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kLo : ℤ)))
    (hHi :
      ((n : ℤ) - 1) * (jHi : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kHi : ℤ)))
    (hx : jHi + 1 = kLo)
    (hw : kHi = jLo + 1) : False := by
  have hdrop := staircase_heightDrop_gt_pairGain
    hn hnell hk hLo hHi
  have hgain : kHi - kLo = jLo - jHi := by omega
  omega

/-- If a fixed-`w` homogeneous terminal relation forces `A+B=D`, its
cross-roof interpretation is impossible purely arithmetically.  Here
`A+B = kLo + q = jLo+1` and `D = v = jLo-jHi` in the fixed-`w` case. -/
theorem no_crossRoof_fixed_w_terminal_degree_relation
    {kLo jLo kHi jHi q v : ℕ}
    (hq : q = jLo + 1 - kLo)
    (hqpos : 0 < q)
    (hv : v = kHi - jHi - 1)
    (hw : kHi = jLo + 1)
    (hdeg : kLo + q = v) : False := by
  have hkLo : kLo ≤ jLo + 1 := by omega
  omega

end

end HC4.Polynomial
