import Mathlib.Tactic

/-!
# Scalar elimination for a ray-kernel coefficient calculation

This is the finite algebra suggested by the model ray
`x (z*w)^m + y (z*w)^(m+1)`. It does not assert that an arbitrary
terminal supplies either coefficient equation. Those adapters remain open.
-/

namespace HC4.Newton

/-- A division-free elimination certificate for a quadratic/cubic pair of
extremal equations. The two nonzero scalars are the coefficients left after
eliminating the auxiliary variable in its zero and nonzero branches. -/
theorem quadratic_cubic_extremal_elimination
    {K : Type*} [Field K] (A q r s a b c : K)
    (ha : a ≠ 0) (hresultant : a * r^2 + b * r * s + c * s^2 ≠ 0)
    (hsecond : q * (r * q - s * A) = 0)
    (hthird : A * (a * A^2 + b * A * q + c * q^2) = 0) : A = 0 := by
  by_contra hA
  have hbracket := (mul_eq_zero.mp hthird).resolve_left hA
  rcases mul_eq_zero.mp hsecond with hq | hlinear
  · have hz : a * A^2 = 0 := by simpa [hq] using hbracket
    exact (mul_ne_zero ha (pow_ne_zero 2 hA)) hz
  · have hz : (a * r^2 + b * r * s + c * s^2) * A^2 = 0 := by
      linear_combination r^2 * hbracket -
        (b * A * r + c * r * q + c * s * A) * hlinear
    exact (mul_ne_zero hresultant (pow_ne_zero 2 hA)) hz

/-- The scalar pair arising at the first positive order of the level-9
model, after the outer kernel coefficients have vanished. -/
theorem ray_kernel_order_one_extremal_elimination
    {K : Type*} [Field K] [CharZero K] (A q : K)
    (hsecond : q * (q - 32 * A) = 0)
    (hthird : A * (64 * A^2 - 8 * A * q + q^2) = 0) : A = 0 := by
  apply quadratic_cubic_extremal_elimination A q 1 32 64 (-8) 1
  · norm_num
  · norm_num
  · simpa using hsecond
  · simpa [sub_eq_add_neg] using hthird

/-- Two successive extremal equations exclude the candidate quadratic
coefficient. No ordering or division by `m - 3` is required. -/
theorem ray_kernel_extremal_elimination
    {K : Type*} [Field K] [CharZero K] (m A q : K)
    (hplus : m + 1 ≠ 0) (hminus : m - 1 ≠ 0)
    (hsecond : q * ((m - 3) * q - 4 * (m + 1) * A) = 0)
    (hthird : A * (8 * (m + 1)^2 * A^2 +
      4 * (m + 1) * A * q + (m - 1) * q^2) = 0) : A = 0 := by
  by_contra hA
  have hbracket := (mul_eq_zero.mp hthird).resolve_left hA
  rcases mul_eq_zero.mp hsecond with hq | hlinear
  · have hz : (8 : K) * (m + 1)^2 * A^2 = 0 := by
      simpa [hq] using hbracket
    exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hplus))
      (pow_ne_zero 2 hA)) hz
  · have hz : (8 : K) * (m + 1)^2 * (m - 1)^2 * A^2 = 0 := by
      linear_combination (m - 3)^2 * hbracket -
        (8 * A * m^2 - 8 * A * m - 16 * A +
          q * (m^2 - 4 * m + 3)) * hlinear
    exact (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hplus))
        (pow_ne_zero 2 hminus)) (pow_ne_zero 2 hA)) hz

/-- The balanced coefficients eliminate the formerly surviving mixed
quadratic term once the higher longitudinal equations remove the two
contaminating later-layer coefficients. -/
theorem ray_kernel_order_one_mixed_elimination
    {K : Type*} [Field K] [CharZero K] (b q : K)
    (hsecond : q * (32*b + 3*q) = 0)
    (hthird : b * (q^2 - 16*b*q - 128*b^2) = 0) : b = 0 := by
  apply quadratic_cubic_extremal_elimination b q 3 (-32) (-128) (-16) 1
  · norm_num
  · norm_num
  · linear_combination hsecond
  · linear_combination hthird

/-- Literal model coefficient equations, including the later source terms.
The hypotheses `hk`, `hr` must come from the full-source highest coefficients;
they cannot be inferred from first-layer kernel compatibility alone. -/
theorem ray_kernel_order_one_mixed_elimination_of_coefficients
    {K : Type*} [Field K] [CharZero K] (b q k r : K)
    (hk : k = 0) (hr : r = 0)
    (hsecond : -9*(288*b*q - 12*r + 32*k + 27*q^2) = 0)
    (hthird : -54*(-1152*b^3 - 144*b^2*q + 32*b*k + 9*b*q^2 - 2*k*q) = 0) :
    b = 0 := by
  subst k
  subst r
  apply ray_kernel_order_one_mixed_elimination b q
  · linear_combination (-1/81 : K) * hsecond
  · linear_combination (-1/486 : K) * hthird

end HC4.Newton
