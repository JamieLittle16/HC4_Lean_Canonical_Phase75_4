import HC4.Polynomial.FiniteStaircaseMiddleDoubleRootVariation
import Mathlib.Tactic

/-!
# Middle two-endpoint second-variation rigidity

On the middle staircase diagonal the evaluated interior moment matrix is a
linear combination of the translated modes `X^(k-1)` and `X^k`.

The highest- and locked-end second variations have the same `2*k*v` term but
different coefficients of the lower mode.  Their difference is exactly

    (k - 1) * (ell - n + 1) * u.

Thus, whenever the endpoint prefactors and this separation scalar are nonzero,
simultaneous vanishing of the two second variations forces `u = 0`.

This file is completely state-free.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K]

/-- **Dual-endpoint middle rigidity.**  The lower translated mode disappears
as soon as both endpoint second variations vanish and the two endpoint
coefficients are genuinely separated. -/
theorem middleLowerMode_eq_zero_of_twoEndpoint_secondVariations
    (V n ell k a b u0 v0 : K)
    (hHighPref :
      8 * V * (V + 1) * a ^ 2 * n ^ 2 * (n - 1) ^ 2 * (k - 1) ≠ 0)
    (hLockPref :
      8 * V * (V + 1) * b ^ 2 * ell ^ 2 * (ell + 1) ^ 2 * (k - 1) ≠ 0)
    (hSep : (k - 1) * (ell - n + 1) ≠ 0)
    (hHigh :
      TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (middleHighestSecondJet V n k a u0 v0).det) = 0)
    (hLock :
      TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (middleLockedSecondJet V ell k b u0 v0).det) = 0) :
    u0 = 0 := by
  rw [snd_snd_det_middleHighestSecondJet] at hHigh
  rw [snd_snd_det_middleLockedSecondJet] at hLock
  by_contra hu
  have hHighBracket :
      ((k * n + k - n - 3) * u0) + 2 * k * v0 = 0 := by
    have hp :
        (8 * V * (V + 1) * a ^ 2 * n ^ 2 * (n - 1) ^ 2 * (k - 1)) * u0 ≠ 0 :=
      mul_ne_zero hHighPref hu
    apply (mul_eq_zero.mp hHigh).resolve_left hp
  have hLockBracket :
      ((ell * k - ell + 2 * k - 4) * u0) + 2 * k * v0 = 0 := by
    have hp :
        (8 * V * (V + 1) * b ^ 2 * ell ^ 2 * (ell + 1) ^ 2 * (k - 1)) * u0 ≠ 0 :=
      mul_ne_zero hLockPref hu
    apply (mul_eq_zero.mp hLock).resolve_left hp
  have hdiff :
      ((k - 1) * (ell - n + 1)) * u0 = 0 := by
    linear_combination hLockBracket - hHighBracket
  exact (mul_ne_zero hSep hu) hdiff

end

end HC4.Polynomial
