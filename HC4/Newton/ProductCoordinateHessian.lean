import HC4.Newton.GeneralFourBlockSchur
import HC4.Newton.CharZeroHessianKernelRigidity
import HC4.Polynomial.HessianDeterminant
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic

/-!
# Hessian determinant of an actual product-coordinate source

For an arbitrary polynomial `f(x,y,h)`, substitute `h=z*w`. The resulting
four-variable Hessian determinant is divisible by the substituted `f_h`.
Consequently Hessian determinant one forces that derivative to be constant.

This uses the actual source substitution and its chain rule. It does not
assert that the later layers of an HC4 terminal admit this substitution.
-/

namespace HC4.Newton

noncomputable section
open MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- Substitute the product of the last two coordinates for the third one. -/
def productCoordinateLift : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.aeval ![X 0, X 1, X 2 * X 3]

private def productCoordinateIndex : Fin 4 → Fin 3 := ![0, 1, 2, 2]
private def productCoordinateMultiplier : Fin 4 → MvPolynomial (Fin 4) K :=
  ![1, 1, X 3, X 2]

/-- Exact polynomial chain rule for the product-coordinate substitution. -/
theorem pderiv_productCoordinateLift (f : MvPolynomial (Fin 3) K) (i : Fin 4) :
    pderiv i (productCoordinateLift f) =
      productCoordinateMultiplier i *
        productCoordinateLift (pderiv (productCoordinateIndex i) f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [productCoordinateLift, pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp =>
    rw [map_mul, pderiv_mul, hp, pderiv_mul, map_add, map_mul]
    fin_cases i <;> fin_cases j <;>
      simp [productCoordinateLift, productCoordinateIndex,
        productCoordinateMultiplier, pderiv_mul] <;> ring

/-- The actual Hessian entries after the product-coordinate substitution. -/
def productCoordinateHessianBlock (f : MvPolynomial (Fin 3) K) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) where
  a := productCoordinateLift (HC4.Polynomial.hessian f 0 0)
  b := productCoordinateLift (HC4.Polynomial.hessian f 0 1)
  d := productCoordinateLift (HC4.Polynomial.hessian f 1 1)
  p := X 3 * productCoordinateLift (HC4.Polynomial.hessian f 0 2)
  q := X 2 * productCoordinateLift (HC4.Polynomial.hessian f 0 2)
  r := X 3 * productCoordinateLift (HC4.Polynomial.hessian f 1 2)
  s := X 2 * productCoordinateLift (HC4.Polynomial.hessian f 1 2)
  x := X 3 ^ 2 * productCoordinateLift (HC4.Polynomial.hessian f 2 2)
  y := productCoordinateLift (pderiv 2 f) +
    X 2 * X 3 * productCoordinateLift (HC4.Polynomial.hessian f 2 2)
  z := X 2 ^ 2 * productCoordinateLift (HC4.Polynomial.hessian f 2 2)

theorem hessian_productCoordinateLift (f : MvPolynomial (Fin 3) K) :
    HC4.Polynomial.hessian (productCoordinateLift f) =
      (productCoordinateHessianBlock f).matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HC4.Polynomial.hessian_apply, pderiv_productCoordinateLift,
      productCoordinateIndex, productCoordinateMultiplier, pderiv_mul,
      productCoordinateHessianBlock, GeneralFourBlock.matrix,
      pderiv_comm_backport] <;> ring

/-- The second factor in the product-coordinate Hessian determinant. -/
def productCoordinateHessianCofactor (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K :=
  productCoordinateLift (pderiv 2 f) *
    productCoordinateLift (HC4.Polynomial.hessian f 0 0 *
      HC4.Polynomial.hessian f 1 1 - HC4.Polynomial.hessian f 0 1 ^ 2) +
  2 * X 2 * X 3 * productCoordinateLift (HC4.Polynomial.hessianDeterminant f)

/-- Source-level determinant factorization, without inverse Hessian entries. -/
theorem hessianDeterminant_productCoordinateLift (f : MvPolynomial (Fin 3) K) :
    HC4.Polynomial.hessianDeterminant (productCoordinateLift f) =
      -productCoordinateLift (pderiv 2 f) * productCoordinateHessianCofactor f := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_productCoordinateLift, GeneralFourBlock.matrix_det]
  simp [productCoordinateHessianBlock, GeneralFourBlock.determinantCore,
    productCoordinateHessianCofactor, HC4.Polynomial.hessianDeterminant,
    Matrix.det_fin_three, HC4.Polynomial.hessian_apply, pderiv_comm_backport]
  <;> ring

/-- Determinant one forces the substituted derivative in the product
coordinate to be a constant unit. No hypothesis on a terminal is added here. -/
theorem productCoordinate_derivative_constant_of_hessianDeterminant_one
    (f : MvPolynomial (Fin 3) K)
    (hdet : HC4.Polynomial.hessianDeterminant (productCoordinateLift f) = 1) :
    ∃ c : K, IsUnit c ∧ productCoordinateLift (pderiv 2 f) = C c := by
  apply MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp
  apply isUnit_of_mul_eq_one _ (-productCoordinateHessianCofactor f)
  calc
    _ = -productCoordinateLift (pderiv 2 f) * productCoordinateHessianCofactor f := by
      ring
    _ = 1 := by rw [← hessianDeterminant_productCoordinateLift]; exact hdet

end
end HC4.Newton
