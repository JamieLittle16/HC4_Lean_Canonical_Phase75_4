import Mathlib.Tactic

/-!
# Scalar elimination for a ray-kernel coefficient calculation

This is the finite algebra suggested by the model ray
`x (z*w)^m + y (z*w)^(m+1)`. It does not assert that an arbitrary
terminal supplies either coefficient equation. Those adapters remain open.
-/

namespace HC4.Newton

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

end HC4.Newton
