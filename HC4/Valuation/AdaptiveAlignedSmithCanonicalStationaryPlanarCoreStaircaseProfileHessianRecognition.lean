import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessianCoefficients
import Mathlib.Tactic

/-!
# A19.R14: coefficientwise recognition of the staircase Hessian

The contact/Schur adapter naturally produces three one-variable polynomial
entries coefficient by coefficient.  A19.R10 already proved that the canonical
stationary staircase Hessian entries have coefficients

    H00[n] = (D-rn)(D-rn-1) a_n,
    H01[n] = n(D-rn) a_n,
    H11[n] = n(n-1) a_n.

This file packages the converse recognition step.  Hence the geometric adapter
never has to unfold the Euler operators or the profile residual: once its
three entries have these coefficients, they *are* the R6 Hessian block.  A
zero determinant then gives the exact residual equation consumed by A19.119.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A polynomial with the weighted parameter-parameter Hessian coefficients is
exactly the canonical staircase `H00` entry. -/
theorem binaryStaircaseProfileHessian00_eq_of_coeff
    (D r : ℕ) (h A : Polynomial K)
    (hcoeff : ∀ n : ℕ,
      A.coeff n =
        (((D : K) - (r : K) * (n : K)) *
          ((D : K) - (r : K) * (n : K) - 1)) * h.coeff n) :
    A = binaryStaircaseProfileHessian00 D r h := by
  ext n
  rw [hcoeff]
  exact (coeff_binaryStaircaseProfileHessian00 D r h n).symm

/-- A polynomial with the weighted mixed Hessian coefficients is exactly the
canonical staircase `H01` entry. -/
theorem binaryStaircaseProfileHessian01_eq_of_coeff
    (D r : ℕ) (h B : Polynomial K)
    (hcoeff : ∀ n : ℕ,
      B.coeff n =
        (n : K) * ((D : K) - (r : K) * (n : K)) * h.coeff n) :
    B = binaryStaircaseProfileHessian01 D r h := by
  ext n
  rw [hcoeff]
  exact (coeff_binaryStaircaseProfileHessian01 D r h n).symm

/-- A polynomial with the longitudinal-longitudinal Hessian coefficients is
exactly the canonical staircase `H11` entry. -/
theorem binaryStaircaseProfileHessian11_eq_of_coeff
    (h C : Polynomial K)
    (hcoeff : ∀ n : ℕ,
      C.coeff n = (n : K) * ((n : K) - 1) * h.coeff n) :
    C = binaryStaircaseProfileHessian11 h := by
  ext n
  rw [hcoeff]
  exact (coeff_binaryStaircaseProfileHessian11 h n).symm

/-- **Coefficientwise Schur-to-residual bridge.**

Any symmetric binary block whose three entries have the weighted binary
homogenization coefficients of `h` is the R6 staircase Hessian.  Therefore a
zero determinant of that block is exactly the stationary profile residual
equation required by the finite staircase rigidity theorem. -/
theorem binaryStaircaseProfileResidual_eq_zero_of_coeffwise_hessian
    (D r : ℕ) (h A B C : Polynomial K)
    (hA : ∀ n : ℕ,
      A.coeff n =
        (((D : K) - (r : K) * (n : K)) *
          ((D : K) - (r : K) * (n : K) - 1)) * h.coeff n)
    (hB : ∀ n : ℕ,
      B.coeff n =
        (n : K) * ((D : K) - (r : K) * (n : K)) * h.coeff n)
    (hC : ∀ n : ℕ,
      C.coeff n = (n : K) * ((n : K) - 1) * h.coeff n)
    (hdet : A * C - B * B = 0) :
    binaryStaircaseProfileResidual D r h = 0 := by
  have hAeq : A = binaryStaircaseProfileHessian00 D r h :=
    binaryStaircaseProfileHessian00_eq_of_coeff D r h A hA
  have hBeq : B = binaryStaircaseProfileHessian01 D r h :=
    binaryStaircaseProfileHessian01_eq_of_coeff D r h B hB
  have hCeq : C = binaryStaircaseProfileHessian11 h :=
    binaryStaircaseProfileHessian11_eq_of_coeff h C hC
  apply binaryStaircaseProfileResidual_eq_zero_of_hessianDet_eq_zero
  unfold binaryStaircaseProfileHessianDet
  simpa [hAeq, hBeq, hCeq] using hdet

end

end HC4.Valuation
