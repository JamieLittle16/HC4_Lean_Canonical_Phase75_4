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

end

end HC4.Polynomial
