import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# Hessian form of the stationary staircase profile residual

The final weighted-profile contradiction is stated in terms of
`binaryStaircaseProfileResidual`.  Geometrically, however, the object produced
by the rank-three/Schur calculation is a symmetric binary Hessian block.

For a weighted homogeneous binary potential

    Q(x,y) = x^D h(y / x^r),

the Euler-normalised Hessian entries are polynomial expressions in

    h,  E h = z h',  F h = z^2 h''.

After removing the harmless monomial coordinate factors, those entries are

    A = D(D-1)h + r(r-2D+1)Eh + r^2 Fh,
    B = (D-r)Eh - r Fh,
    C = Fh.

Their determinant is exactly the stationary profile residual already used by
the finite staircase rigidity theorem.  This file freezes that identity so
the remaining A19 adapter only has to identify the honest cleared Schur block
with `A,B,C`; it never has to expand the profile residual again.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Euler-normalised `(0,0)` Hessian entry of a weighted staircase profile. -/
def binaryStaircaseProfileHessian00
    (D r : ℕ) (h : Polynomial K) : Polynomial K :=
  Polynomial.C ((D : K) * ((D : K) - 1)) * h +
    Polynomial.C ((r : K) * ((r : K) - 2 * (D : K) + 1)) *
      eulerDerivative h +
    Polynomial.C ((r : K) ^ 2) *
      binaryStaircaseProfileSecondEuler h

/-- Euler-normalised mixed Hessian entry of a weighted staircase profile. -/
def binaryStaircaseProfileHessian01
    (D r : ℕ) (h : Polynomial K) : Polynomial K :=
  Polynomial.C ((D : K) - (r : K)) * eulerDerivative h -
    Polynomial.C (r : K) * binaryStaircaseProfileSecondEuler h

/-- Euler-normalised `(1,1)` Hessian entry of a weighted staircase profile. -/
def binaryStaircaseProfileHessian11
    (h : Polynomial K) : Polynomial K :=
  binaryStaircaseProfileSecondEuler h

/-- Determinant of the Euler-normalised weighted profile Hessian block. -/
def binaryStaircaseProfileHessianDet
    (D r : ℕ) (h : Polynomial K) : Polynomial K :=
  binaryStaircaseProfileHessian00 D r h *
      binaryStaircaseProfileHessian11 h -
    binaryStaircaseProfileHessian01 D r h *
      binaryStaircaseProfileHessian01 D r h

/-- **Exact Hessian/residual identity.**  This is the canonical polynomial
normal form consumed by the final binary Schur adapter. -/
theorem binaryStaircaseProfileHessianDet_eq_residual
    (D r : ℕ) (h : Polynomial K) :
    binaryStaircaseProfileHessianDet D r h =
      binaryStaircaseProfileResidual D r h := by
  unfold binaryStaircaseProfileHessianDet
    binaryStaircaseProfileHessian00
    binaryStaircaseProfileHessian01
    binaryStaircaseProfileHessian11
    binaryStaircaseProfileResidual
  simp [map_mul, map_sub, map_add, map_pow]
  rw [show (Polynomial.C (2 : K) : Polynomial K) = 2 by norm_num]
  ring

/-- A zero weighted-profile Hessian block determinant is exactly the residual
hypothesis required by the existing staircase rigidity theorem. -/
theorem binaryStaircaseProfileResidual_eq_zero_of_hessianDet_eq_zero
    (D r : ℕ) (h : Polynomial K)
    (hdet : binaryStaircaseProfileHessianDet D r h = 0) :
    binaryStaircaseProfileResidual D r h = 0 := by
  rw [← binaryStaircaseProfileHessianDet_eq_residual]
  exact hdet

end

end HC4.Valuation