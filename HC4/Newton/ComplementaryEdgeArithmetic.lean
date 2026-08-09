import Mathlib

/-!
# Arithmetic endpoint of the complementary rank-two edge obstruction

The analytic calculation for a complementary edge gives

    lim eta/rho = 1/(A0*h),

while the first nonconstant term of the edge polynomial gives the same limit
as a positive integer `m`.  Since `A0 >= 2` and `h,m >= 1`, this is
impossible.  This file kernel-checks that final arithmetic contradiction;
the upstream logarithmic-Hessian limit calculation remains a separate
analytic obligation.
-/

namespace HC4.Newton

/-- No positive integer can equal `1/(A0*h)` when `A0 >= 2`. -/
theorem complementary_limit_arithmetic_impossible
    {A0 h m : ℕ} (hA0 : 2 ≤ A0) (hh : 0 < h) (hm : 0 < m)
    (hlim : (m : ℚ) = 1 / ((A0 : ℚ) * (h : ℚ))) : False := by
  have hA0Q : (0 : ℚ) < (A0 : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hA0)
  have hhQ : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have hden : (A0 : ℚ) * (h : ℚ) ≠ 0 := ne_of_gt (mul_pos hA0Q hhQ)
  have hmul : (m : ℚ) * ((A0 : ℚ) * (h : ℚ)) = 1 :=
    (eq_div_iff hden).mp hlim
  have hcast : ((m * (A0 * h) : ℕ) : ℚ) = 1 := by
    simpa [Nat.cast_mul, mul_assoc] using hmul
  have hnat : m * (A0 * h) = 1 := by exact_mod_cast hcast
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have hh1 : 1 ≤ h := Nat.succ_le_iff.mpr hh
  have hAh : 2 ≤ A0 * h := by
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ A0 * h := Nat.mul_le_mul hA0 hh1
  have hprod : 2 ≤ m * (A0 * h) := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ m * (A0 * h) := Nat.mul_le_mul hm1 hAh
  omega

/-- Manuscript-ready form: if `A0 = alpha1+alpha2` with both exponents
positive, the complementary-edge limiting equality is impossible. -/
theorem complementary_endpoint_contradiction
    {alpha1 alpha2 h m : ℕ}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hh : 0 < h) (hm : 0 < m)
    (hlim : (m : ℚ) =
      1 / (((alpha1 + alpha2 : ℕ) : ℚ) * (h : ℚ))) : False := by
  have hA0 : 2 ≤ alpha1 + alpha2 := by omega
  exact complementary_limit_arithmetic_impossible hA0 hh hm hlim

end HC4.Newton
