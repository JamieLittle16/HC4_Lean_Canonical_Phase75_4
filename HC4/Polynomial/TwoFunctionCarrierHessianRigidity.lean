import HC4.Polynomial.TwoFunctionEulerConcreteRigidity
import HC4.Polynomial.ComplementaryMvMomentRealisation
import Mathlib.Tactic

/-!
# Complete Hessian contradiction for the concrete two-function carrier

This is the state-free end-to-end algebraic theorem used by the A19
no-singleton rank-three branch.

For

    F = x (Q(Y) + b H^ell) + z (P(Y) + a H^ell Y),
    Y = y w^V,
    H = z w^V,

zero ordinary Hessian determinant implies zero Euler-scaled determinant.  The
concrete factorisation then has the form

    nonzero_monomial_prefactor * A * B = 0.

Under `V>0`, `ell>0` and `A != 0`, the prefactor is nonzero in the
multivariate polynomial domain, hence `B=0`.  The concrete coefficient
extraction theorem then contradicts `a,b,Q' != 0` in characteristic zero.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Complete two-function carrier contradiction.** -/
theorem twoFunctionCarrier_hessian_impossible
    (V ell : ℕ) (hV : 0 < V) (hell : 0 < ell)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (P Q : Polynomial K) (hQ1 : Q.derivative ≠ 0)
    (hA :
      twoFunctionEulerFactorA
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative) ≠ 0)
    (hdet : hessianDeterminant (twoFunctionCarrier V ell a b P Q) = 0) :
    False := by
  let R := MvPolynomial (Fin 4) K
  let Y : R := twoFunctionY (K := K) V
  let H : R := twoFunctionH (K := K) V
  let q1 : R := polynomialLift Y Q.derivative
  let q2 : R := polynomialLift Y Q.derivative.derivative
  let p1 : R := polynomialLift Y P.derivative
  let p2 : R := polynomialLift Y P.derivative.derivative
  let A : R := twoFunctionEulerFactorA
    V ell (MvPolynomial.X (0 : Fin 4)) (MvPolynomial.X (2 : Fin 4))
    Y H (MvPolynomial.C a) (MvPolynomial.C b) q1 p1
  let B : R := twoFunctionEulerFactorB
    V ell (MvPolynomial.X (0 : Fin 4)) (MvPolynomial.X (2 : Fin 4))
    Y H (MvPolynomial.C a) (MvPolynomial.C b) q1 q2 p1 p2

  have hscaled :
      (eulerScaledHessian (twoFunctionCarrier V ell a b P Q)).det = 0 := by
    rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant]
    rw [hdet]
    simp

  rw [det_eulerScaledHessian_twoFunctionCarrier] at hscaled

  have hV0 : (V : R) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hV)
  have hell0 : (ell : R) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)
  have hV1cast : ((V + 1 : ℕ) : R) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by omega)
  have hV1 : (V : R) + 1 ≠ 0 := by
    simpa [Nat.cast_add] using hV1cast
  have hx : (MvPolynomial.X (0 : Fin 4) : R) ^ 2 ≠ 0 :=
    pow_ne_zero _ MvPolynomial.X_ne_zero
  have hY : Y ≠ 0 := by
    dsimp [Y, R]
    unfold twoFunctionY
    exact mul_ne_zero MvPolynomial.X_ne_zero
      (pow_ne_zero _ MvPolynomial.X_ne_zero)
  have hH : H ≠ 0 := by
    dsimp [H, R]
    unfold twoFunctionH
    exact mul_ne_zero MvPolynomial.X_ne_zero
      (pow_ne_zero _ MvPolynomial.X_ne_zero)
  have hA' : A ≠ 0 := by
    simpa [A, Y, H, q1, p1, R] using hA

  have h1 : (V : R) * (ell : R) ≠ 0 := mul_ne_zero hV0 hell0
  have h2 : (V : R) * (ell : R) * ((V : R) + 1) ≠ 0 :=
    mul_ne_zero h1 hV1
  have h3 :
      (V : R) * (ell : R) * ((V : R) + 1) *
        MvPolynomial.X (0 : Fin 4) ^ 2 ≠ 0 :=
    mul_ne_zero h2 hx
  have h4 :
      (V : R) * (ell : R) * ((V : R) + 1) *
        MvPolynomial.X (0 : Fin 4) ^ 2 * Y ^ 2 ≠ 0 :=
    mul_ne_zero h3 (pow_ne_zero _ hY)
  have h5 :
      (V : R) * (ell : R) * ((V : R) + 1) *
        MvPolynomial.X (0 : Fin 4) ^ 2 * Y ^ 2 * H ^ ell ≠ 0 :=
    mul_ne_zero h4 (pow_ne_zero _ hH)
  have hprefix :
      (V : R) * (ell : R) * ((V : R) + 1) *
        MvPolynomial.X (0 : Fin 4) ^ 2 * Y ^ 2 * H ^ ell * A ≠ 0 :=
    mul_ne_zero h5 hA'

  have hB : B = 0 := by
    change
      (V : R) * (ell : R) * ((V : R) + 1) *
          MvPolynomial.X (0 : Fin 4) ^ 2 * Y ^ 2 * H ^ ell * A * B = 0
      at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left hprefix

  exact twoFunction_concrete_factorB_impossible
    V ell hell a b ha hb P Q hQ1 (by
      simpa [B, Y, H, q1, q2, p1, p2, R] using hB)

end

end HC4.Polynomial
