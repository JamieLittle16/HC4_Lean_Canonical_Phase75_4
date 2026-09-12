import HC4.Polynomial.ComplementaryMvSubstitution
import HC4.Polynomial.TwoFunctionEulerHessian
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Concrete Euler calculus for the two-function carrier

This file bridges the state-free determinant identity in
`TwoFunctionEulerHessian` to an actual four-variable polynomial carrier.
The basic substitutions are

    Y = y * w^V,
    H = z * w^V,

and a univariate polynomial is lifted by evaluation at `Y`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- The concrete monomial `Y = y w^V`. -/
def twoFunctionY
    {K : Type*} [CommRing K] (V : ℕ) : MvPolynomial (Fin 4) K :=
  MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ V

/-- The concrete monomial `H = z w^V`. -/
def twoFunctionH
    {K : Type*} [CommRing K] (V : ℕ) : MvPolynomial (Fin 4) K :=
  MvPolynomial.X (2 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ V

/-- Lift a one-variable polynomial by substituting an arbitrary multivariate
polynomial `t` for its variable. -/
def polynomialLift
    {K : Type*} [CommRing K]
    (t : MvPolynomial (Fin 4) K) (p : Polynomial K) :
    MvPolynomial (Fin 4) K :=
  Polynomial.eval₂ MvPolynomial.C t p

/-- Formal chain rule for a univariate polynomial evaluated at a
multivariate polynomial. -/
theorem pderiv_polynomialLift
    {K : Type*} [CommRing K]
    (i : Fin 4) (t : MvPolynomial (Fin 4) K) (p : Polynomial K) :
    MvPolynomial.pderiv i (polynomialLift t p) =
      polynomialLift t p.derivative * MvPolynomial.pderiv i t := by
  unfold polynomialLift
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp only [Polynomial.eval₂_add, Polynomial.derivative_add]
    rw [map_add, hp, hq]
    ring
  · intro n a
    simp [Polynomial.derivative_monomial, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow]
    ring

/-- Euler form of the chain rule. -/
theorem mvEuler_polynomialLift
    {K : Type*} [CommRing K]
    (i : Fin 4) (t : MvPolynomial (Fin 4) K) (p : Polynomial K) :
    mvEuler i (polynomialLift t p) =
      polynomialLift t p.derivative * mvEuler i t := by
  rw [mvEuler, pderiv_polynomialLift]
  rw [mvEuler]
  ring

/-- `Y` has Euler weight one in the `y` coordinate. -/
theorem mvEuler_one_twoFunctionY
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (1 : Fin 4) (twoFunctionY (K := K) V) = twoFunctionY V := by
  simp [mvEuler, twoFunctionY, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow]

/-- `Y` has Euler weight `V` in the `w` coordinate. -/
theorem mvEuler_three_twoFunctionY
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionY (K := K) V) =
      (V : K) • twoFunctionY V := by
  simp [mvEuler, twoFunctionY, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow]
  ring

/-- `H` has Euler weight one in the `z` coordinate. -/
theorem mvEuler_two_twoFunctionH
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (2 : Fin 4) (twoFunctionH (K := K) V) = twoFunctionH V := by
  simp [mvEuler, twoFunctionH, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow]

/-- `H` has Euler weight `V` in the `w` coordinate. -/
theorem mvEuler_three_twoFunctionH
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionH (K := K) V) =
      (V : K) • twoFunctionH V := by
  simp [mvEuler, twoFunctionH, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow]
  ring

/-- The actual four-variable no-singleton carrier from the paper argument:

`x (Q(Y) + b H^ell) + z (P(Y) + a H^ell Y)`.
-/
def twoFunctionCarrier
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    MvPolynomial (Fin 4) K :=
  let Y := twoFunctionY (K := K) V
  let H := twoFunctionH (K := K) V
  MvPolynomial.X (0 : Fin 4) *
      (polynomialLift Y Q + MvPolynomial.C b * H ^ ell) +
    MvPolynomial.X (2 : Fin 4) *
      (polynomialLift Y P + MvPolynomial.C a * H ^ ell * Y)

/-- The Euler-scaled Hessian of the concrete two-function carrier is exactly
the abstract matrix used in `TwoFunctionEulerHessian`. -/
theorem eulerScaledHessian_twoFunctionCarrier
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    eulerScaledHessian (twoFunctionCarrier V ell a b P Q) =
      twoFunctionEulerHessianMatrix
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerScaledHessian_apply, twoFunctionCarrier,
      twoFunctionEulerHessianMatrix, pderiv_polynomialLift,
      twoFunctionY, twoFunctionH, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow] <;>
    ring

/-- Determinant factorisation for the **actual** four-variable carrier. -/
theorem det_eulerScaledHessian_twoFunctionCarrier
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    (eulerScaledHessian (twoFunctionCarrier V ell a b P Q)).det =
      (V : MvPolynomial (Fin 4) K) *
        (ell : MvPolynomial (Fin 4) K) *
        ((V : MvPolynomial (Fin 4) K) + 1) *
        MvPolynomial.X (0 : Fin 4) ^ 2 *
        twoFunctionY (K := K) V ^ 2 *
        twoFunctionH (K := K) V ^ ell *
        twoFunctionEulerFactorA
          V ell
          (MvPolynomial.X (0 : Fin 4))
          (MvPolynomial.X (2 : Fin 4))
          (twoFunctionY (K := K) V)
          (twoFunctionH (K := K) V)
          (MvPolynomial.C a)
          (MvPolynomial.C b)
          (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
          (polynomialLift (twoFunctionY (K := K) V) P.derivative) *
        twoFunctionEulerFactorB
          V ell
          (MvPolynomial.X (0 : Fin 4))
          (MvPolynomial.X (2 : Fin 4))
          (twoFunctionY (K := K) V)
          (twoFunctionH (K := K) V)
          (MvPolynomial.C a)
          (MvPolynomial.C b)
          (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
          (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
          (polynomialLift (twoFunctionY (K := K) V) P.derivative)
          (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative) := by
  rw [eulerScaledHessian_twoFunctionCarrier]
  exact det_twoFunctionEulerHessianMatrix
    V ell
    (MvPolynomial.X (0 : Fin 4))
    (MvPolynomial.X (2 : Fin 4))
    (twoFunctionY (K := K) V)
    (twoFunctionH (K := K) V)
    (MvPolynomial.C a)
    (MvPolynomial.C b)
    (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
    (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
    (polynomialLift (twoFunctionY (K := K) V) P.derivative)
    (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative)

end

end HC4.Polynomial
