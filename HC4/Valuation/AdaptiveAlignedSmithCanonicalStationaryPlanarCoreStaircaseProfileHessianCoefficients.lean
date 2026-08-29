import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessian
import Mathlib.Tactic

/-!
# A19.R10: coefficient formulas for the staircase Hessian block

A19.R6 packages the stationary binary staircase equation as the determinant
of the Euler-normalised Hessian block

    [[H00, H01],
     [H01, H11]].

The contact-Rees side of the final A19 adapter is coefficientwise: after the
transverse inflation of A19.123, the longitudinal coefficient of order `n`
has parameter exponent `D - r*n`.  This file records the matching
coefficient formulas on the profile side.

For `a_n = [z^n] h`, the three entries are exactly

    [z^n] H00 = (D-rn)(D-rn-1) a_n,
    [z^n] H01 = n(D-rn) a_n,
    [z^n] H11 = n(n-1) a_n.

The identities are stated in the coefficient field, so no natural-number
subtraction hypothesis is needed.  This is the algebraic form consumed by the
contact-family Hessian coefficient comparison.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Coefficient of the longitudinal-longitudinal staircase Hessian entry. -/
@[simp]
theorem coeff_binaryStaircaseProfileHessian11
    (h : Polynomial K) (n : ℕ) :
    (binaryStaircaseProfileHessian11 h).coeff n =
      (n : K) * ((n : K) - 1) * h.coeff n := by
  unfold binaryStaircaseProfileHessian11
  exact coeff_binaryStaircaseProfileSecondEuler h n

/-- Coefficient of the mixed staircase Hessian entry. -/
@[simp]
theorem coeff_binaryStaircaseProfileHessian01
    (D r : ℕ) (h : Polynomial K) (n : ℕ) :
    (binaryStaircaseProfileHessian01 D r h).coeff n =
      (n : K) * ((D : K) - (r : K) * (n : K)) * h.coeff n := by
  unfold binaryStaircaseProfileHessian01
  rw [Polynomial.coeff_sub]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  simp only [coeff_eulerDerivative, coeff_binaryStaircaseProfileSecondEuler]
  ring

/-- Coefficient of the parameter-parameter staircase Hessian entry. -/
@[simp]
theorem coeff_binaryStaircaseProfileHessian00
    (D r : ℕ) (h : Polynomial K) (n : ℕ) :
    (binaryStaircaseProfileHessian00 D r h).coeff n =
      (((D : K) - (r : K) * (n : K)) *
          ((D : K) - (r : K) * (n : K) - 1)) *
        h.coeff n := by
  unfold binaryStaircaseProfileHessian00
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  simp only [coeff_eulerDerivative, coeff_binaryStaircaseProfileSecondEuler]
  ring

end

end HC4.Valuation
