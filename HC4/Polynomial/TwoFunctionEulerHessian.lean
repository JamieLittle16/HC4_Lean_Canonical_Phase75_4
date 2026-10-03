import HC4.Polynomial.Hessian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Two-function carrier Euler-Hessian factorisation

This is the state-free algebraic core of the A19 no-singleton carrier closure.
After the substitutions

    Y = y w^V,
    H = z w^V,

and writing `q1,q2,p1,p2` for the first and second `Y` derivatives of the two
coefficient functions, the Euler-scaled Hessian of

    x (Q(Y) + b H^ell) + z (P(Y) + a H^ell Y)

has the explicit symmetric matrix below.  Its determinant factors without any
Laurent monomials as

    V * ell * (V+1) * x^2 * Y^2 * H^ell * A * B.

Using the Euler-scaled Hessian is important: it is the polynomial identity
behind the paper's raw-Hessian formula and avoids negative powers such as
`z^(ell-2)` and `w^(-2)`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- First nontrivial factor in the two-function Euler-Hessian determinant. -/
def twoFunctionEulerFactorA
    {R : Type*} [CommRing R]
    (V ell : ℕ) (x z Y H a b q1 p1 : R) : R :=
  Y * (x * q1 + z * p1) +
    H ^ ell * (b * (ell : R) * x + a * ((ell : R) + 1) * z * Y)

/-- Second nontrivial factor in the two-function Euler-Hessian determinant. -/
def twoFunctionEulerFactorB
    {R : Type*} [CommRing R]
    (V ell : ℕ) (x z Y H a b q1 q2 p1 p2 : R) : R :=
  x *
      (b * ((ell : R) - 1) * q1 ^ 2 +
        b ^ 2 * (ell : R) * H ^ ell * q2) +
    z *
      (a * ((ell : R) + 1) * Y * q1 ^ 2 -
        2 * b * p1 * q1 -
        2 * a * b * ((ell : R) + 1) * H ^ ell * q1 +
        b ^ 2 * (ell : R) * H ^ ell * p2)

/-- Explicit Euler-scaled Hessian matrix of the abstract two-function carrier.
The entries use only the algebraic symbols `x,z,Y,H` and derivative values
`q1,q2,p1,p2`. -/
def twoFunctionEulerHessianMatrix
    {R : Type*} [CommRing R]
    (V ell : ℕ) (x z Y H a b q1 q2 p1 p2 : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![
    0,
      x * Y * q1,
      b * (ell : R) * x * H ^ ell,
      (V : R) * x * (b * (ell : R) * H ^ ell + Y * q1);
    x * Y * q1,
      Y ^ 2 * (x * q2 + z * p2),
      Y * z * (a * ((ell : R) + 1) * H ^ ell + p1),
      (V : R) * Y *
        (a * ((ell : R) + 1) * z * H ^ ell + p1 * z + p2 * Y * z +
          q1 * x + q2 * x * Y);
    b * (ell : R) * x * H ^ ell,
      Y * z * (a * ((ell : R) + 1) * H ^ ell + p1),
      (ell : R) * H ^ ell *
        (a * ((ell : R) + 1) * Y * z + b * ((ell : R) - 1) * x),
      (V : R) *
        (a * ((ell : R) + 1) ^ 2 * Y * z * H ^ ell +
          b * (ell : R) ^ 2 * x * H ^ ell + p1 * Y * z);
    (V : R) * x * (b * (ell : R) * H ^ ell + Y * q1),
      (V : R) * Y *
        (a * ((ell : R) + 1) * z * H ^ ell + p1 * z + p2 * Y * z +
          q1 * x + q2 * x * Y),
      (V : R) *
        (a * ((ell : R) + 1) ^ 2 * Y * z * H ^ ell +
          b * (ell : R) ^ 2 * x * H ^ ell + p1 * Y * z),
      (V : R) *
        ((V : R) * a * ((ell : R) + 1) ^ 2 * Y * z * H ^ ell +
          (V : R) * b * (ell : R) ^ 2 * x * H ^ ell +
          (V : R) * p1 * Y * z +
          (V : R) * p2 * Y ^ 2 * z +
          (V : R) * q1 * x * Y +
          (V : R) * q2 * x * Y ^ 2 -
          a * ((ell : R) + 1) * Y * z * H ^ ell -
          b * (ell : R) * x * H ^ ell - p1 * Y * z - q1 * x * Y)
  ]

/-- **Exact two-function Euler-Hessian determinant factorisation.** -/
theorem det_twoFunctionEulerHessianMatrix
    {R : Type*} [CommRing R]
    (V ell : ℕ) (x z Y H a b q1 q2 p1 p2 : R) :
    (twoFunctionEulerHessianMatrix
      V ell x z Y H a b q1 q2 p1 p2).det =
      (V : R) * (ell : R) * ((V : R) + 1) *
        x ^ 2 * Y ^ 2 * H ^ ell *
        twoFunctionEulerFactorA V ell x z Y H a b q1 p1 *
        twoFunctionEulerFactorB V ell x z Y H a b q1 q2 p1 p2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [twoFunctionEulerHessianMatrix, Matrix.det_fin_three, Fin.succAbove,
    twoFunctionEulerFactorA, twoFunctionEulerFactorB]
  ring

end

end HC4.Polynomial
