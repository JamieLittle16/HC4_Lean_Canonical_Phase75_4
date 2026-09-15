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
    simp [Polynomial.derivative_monomial]
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
  simp [mvEuler, twoFunctionY]

/-- `Y` has Euler weight `V` in the `w` coordinate. -/
theorem mvEuler_three_twoFunctionY
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionY (K := K) V) =
      (V : K) • twoFunctionY V := by
  by_cases hV : V = 0
  · subst V
    simp [mvEuler, twoFunctionY]
  · have hVpos : 0 < V := Nat.pos_of_ne_zero hV
    simp [mvEuler, twoFunctionY]
    have hpow :
        (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) *
            (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) ^ (V - 1) =
          (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) ^ V := by
      rw [← pow_succ']
      congr 1
      omega
    change
      (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) *
          (MvPolynomial.X (1 : Fin 4) *
            ((V : MvPolynomial (Fin 4) K) *
              MvPolynomial.X (3 : Fin 4) ^ (V - 1))) =
        (V : K) •
          (MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ V)
    calc
      _ = (V : MvPolynomial (Fin 4) K) * MvPolynomial.X (1 : Fin 4) *
          (MvPolynomial.X (3 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ (V - 1)) := by
            ring
      _ = (V : MvPolynomial (Fin 4) K) * MvPolynomial.X (1 : Fin 4) *
          MvPolynomial.X (3 : Fin 4) ^ V := by rw [hpow]
      _ = (V : K) •
          (MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ V) := by
            simp [Algebra.smul_def]
            ring

/-- `H` has Euler weight one in the `z` coordinate. -/
theorem mvEuler_two_twoFunctionH
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (2 : Fin 4) (twoFunctionH (K := K) V) = twoFunctionH V := by
  simp [mvEuler, twoFunctionH]

/-- `H` has Euler weight `V` in the `w` coordinate. -/
theorem mvEuler_three_twoFunctionH
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionH (K := K) V) =
      (V : K) • twoFunctionH V := by
  by_cases hV : V = 0
  · subst V
    simp [mvEuler, twoFunctionH]
  · have hVpos : 0 < V := Nat.pos_of_ne_zero hV
    simp [mvEuler, twoFunctionH]
    have hpow :
        (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) *
            (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) ^ (V - 1) =
          (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) ^ V := by
      rw [← pow_succ']
      congr 1
      omega
    change
      (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) *
          (MvPolynomial.X (2 : Fin 4) *
            ((V : MvPolynomial (Fin 4) K) *
              MvPolynomial.X (3 : Fin 4) ^ (V - 1))) =
        (V : K) •
          (MvPolynomial.X (2 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ V)
    calc
      _ = (V : MvPolynomial (Fin 4) K) * MvPolynomial.X (2 : Fin 4) *
          (MvPolynomial.X (3 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ (V - 1)) := by
            ring
      _ = (V : MvPolynomial (Fin 4) K) * MvPolynomial.X (2 : Fin 4) *
          MvPolynomial.X (3 : Fin 4) ^ V := by rw [hpow]
      _ = (V : K) •
          (MvPolynomial.X (2 : Fin 4) * MvPolynomial.X (3 : Fin 4) ^ V) := by
            simp [Algebra.smul_def]
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

/-! Small Euler rules keep the concrete Hessian proof in the invariant
`Y,H` coordinates.  This avoids expanding `w^V` and `H^ell` into large
expressions involving truncated natural subtraction. -/

private theorem mvEuler_add_local
    {K : Type*} [CommRing K] (i : Fin 4)
    (p q : MvPolynomial (Fin 4) K) :
    mvEuler i (p + q) = mvEuler i p + mvEuler i q := by
  simp [mvEuler, mul_add]

private theorem mvEuler_mul_local
    {K : Type*} [CommRing K] (i : Fin 4)
    (p q : MvPolynomial (Fin 4) K) :
    mvEuler i (p * q) = mvEuler i p * q + p * mvEuler i q := by
  simp [mvEuler, MvPolynomial.pderiv_mul, mul_add]
  ring

private theorem mvEuler_C_local
    {K : Type*} [CommRing K] (i : Fin 4) (a : K) :
    mvEuler i (MvPolynomial.C a : MvPolynomial (Fin 4) K) = 0 := by
  simp [mvEuler]

private theorem mvEuler_natCast_local
    {K : Type*} [CommRing K] (i : Fin 4) (n : ℕ) :
    mvEuler i (n : MvPolynomial (Fin 4) K) = 0 := by
  simp [mvEuler]

private theorem mvEuler_one_local
    {K : Type*} [CommRing K] (i : Fin 4) :
    mvEuler i (1 : MvPolynomial (Fin 4) K) = 0 := by
  simp [mvEuler]

private theorem mvEuler_X_local
    {K : Type*} [CommRing K] (i j : Fin 4) :
    mvEuler i (MvPolynomial.X j : MvPolynomial (Fin 4) K) =
      if i = j then MvPolynomial.X j else 0 := by
  by_cases h : i = j
  · subst j
    simp [mvEuler]
  · simp [mvEuler, h, Ne.symm h]

private theorem mvEuler_pow_of_eigen_local
    {K : Type*} [CommRing K] (i : Fin 4)
    (p c : MvPolynomial (Fin 4) K)
    (h : mvEuler i p = c * p) (n : ℕ) :
    mvEuler i (p ^ n) = (n : MvPolynomial (Fin 4) K) * c * p ^ n := by
  induction n with
  | zero => simp [mvEuler]
  | succ n ih =>
      rw [pow_succ, mvEuler_mul_local, ih, h]
      simp only [Nat.cast_succ]
      ring

private theorem mvEuler_zero_twoFunctionY_local
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (0 : Fin 4) (twoFunctionY (K := K) V) = 0 := by
  simp [mvEuler, twoFunctionY]

private theorem mvEuler_two_twoFunctionY_local
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (2 : Fin 4) (twoFunctionY (K := K) V) = 0 := by
  simp [mvEuler, twoFunctionY]

private theorem mvEuler_three_twoFunctionY_local
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionY (K := K) V) =
      (V : MvPolynomial (Fin 4) K) * twoFunctionY V := by
  simpa [Algebra.smul_def] using
    (mvEuler_three_twoFunctionY (K := K) V)

private theorem mvEuler_zero_twoFunctionH_local
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (0 : Fin 4) (twoFunctionH (K := K) V) = 0 := by
  simp [mvEuler, twoFunctionH]

private theorem mvEuler_one_twoFunctionH_local
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (1 : Fin 4) (twoFunctionH (K := K) V) = 0 := by
  simp [mvEuler, twoFunctionH]

private theorem mvEuler_three_twoFunctionH_local
    {K : Type*} [CommRing K] (V : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionH (K := K) V) =
      (V : MvPolynomial (Fin 4) K) * twoFunctionH V := by
  simpa [Algebra.smul_def] using
    (mvEuler_three_twoFunctionH (K := K) V)

private theorem mvEuler_zero_twoFunctionH_pow_local
    {K : Type*} [CommRing K] (V ell : ℕ) :
    mvEuler (0 : Fin 4) (twoFunctionH (K := K) V ^ ell) = 0 := by
  have hbase :
      mvEuler (0 : Fin 4) (twoFunctionH (K := K) V) =
        (0 : MvPolynomial (Fin 4) K) * twoFunctionH V := by
    simp [mvEuler_zero_twoFunctionH_local]
  simpa using
    (mvEuler_pow_of_eigen_local (K := K) (0 : Fin 4)
      (twoFunctionH V) 0 hbase ell)

private theorem mvEuler_one_twoFunctionH_pow_local
    {K : Type*} [CommRing K] (V ell : ℕ) :
    mvEuler (1 : Fin 4) (twoFunctionH (K := K) V ^ ell) = 0 := by
  have hbase :
      mvEuler (1 : Fin 4) (twoFunctionH (K := K) V) =
        (0 : MvPolynomial (Fin 4) K) * twoFunctionH V := by
    simp [mvEuler_one_twoFunctionH_local]
  simpa using
    (mvEuler_pow_of_eigen_local (K := K) (1 : Fin 4)
      (twoFunctionH V) 0 hbase ell)

private theorem mvEuler_two_twoFunctionH_pow_local
    {K : Type*} [CommRing K] (V ell : ℕ) :
    mvEuler (2 : Fin 4) (twoFunctionH (K := K) V ^ ell) =
      (ell : MvPolynomial (Fin 4) K) * twoFunctionH V ^ ell := by
  have hbase :
      mvEuler (2 : Fin 4) (twoFunctionH (K := K) V) =
        (1 : MvPolynomial (Fin 4) K) * twoFunctionH V := by
    simp [mvEuler_two_twoFunctionH]
  simpa using
    (mvEuler_pow_of_eigen_local (K := K) (2 : Fin 4)
      (twoFunctionH V) 1 hbase ell)

private theorem mvEuler_three_twoFunctionH_pow_local
    {K : Type*} [CommRing K] (V ell : ℕ) :
    mvEuler (3 : Fin 4) (twoFunctionH (K := K) V ^ ell) =
      (ell : MvPolynomial (Fin 4) K) *
        (V : MvPolynomial (Fin 4) K) * twoFunctionH V ^ ell := by
  have hbase :
      mvEuler (3 : Fin 4) (twoFunctionH (K := K) V) =
        (V : MvPolynomial (Fin 4) K) * twoFunctionH V :=
    mvEuler_three_twoFunctionH_local V
  exact mvEuler_pow_of_eigen_local (K := K) (3 : Fin 4)
    (twoFunctionH V) (V : MvPolynomial (Fin 4) K) hbase ell

/-! Cache the four first Euler derivatives of the carrier.  The Hessian proof
below differentiates these compact invariant-coordinate formulas rather than
re-expanding the original carrier in every one of its sixteen entries. -/

private theorem mvEuler_zero_twoFunctionCarrier_local
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    mvEuler (0 : Fin 4) (twoFunctionCarrier V ell a b P Q) =
      MvPolynomial.X (0 : Fin 4) *
        (polynomialLift (twoFunctionY (K := K) V) Q +
          MvPolynomial.C b * twoFunctionH (K := K) V ^ ell) := by
  simp [twoFunctionCarrier, mvEuler_add_local, mvEuler_mul_local,
    mvEuler_C_local, mvEuler_X_local, mvEuler_polynomialLift,
    mvEuler_zero_twoFunctionY_local, mvEuler_zero_twoFunctionH_pow_local]

private theorem mvEuler_one_twoFunctionCarrier_local
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    mvEuler (1 : Fin 4) (twoFunctionCarrier V ell a b P Q) =
      MvPolynomial.X (0 : Fin 4) *
          (twoFunctionY (K := K) V *
            polynomialLift (twoFunctionY (K := K) V) Q.derivative) +
        MvPolynomial.X (2 : Fin 4) *
          (twoFunctionY (K := K) V *
              polynomialLift (twoFunctionY (K := K) V) P.derivative +
            MvPolynomial.C a * twoFunctionH (K := K) V ^ ell *
              twoFunctionY (K := K) V) := by
  simp [twoFunctionCarrier, mvEuler_add_local, mvEuler_mul_local,
    mvEuler_C_local, mvEuler_X_local, mvEuler_polynomialLift,
    mvEuler_one_twoFunctionY, mvEuler_one_twoFunctionH_pow_local]
  ring

private theorem mvEuler_two_twoFunctionCarrier_local
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    mvEuler (2 : Fin 4) (twoFunctionCarrier V ell a b P Q) =
      MvPolynomial.C b * (ell : MvPolynomial (Fin 4) K) *
          MvPolynomial.X (0 : Fin 4) * twoFunctionH (K := K) V ^ ell +
        MvPolynomial.X (2 : Fin 4) *
          (polynomialLift (twoFunctionY (K := K) V) P +
            MvPolynomial.C a * ((ell : MvPolynomial (Fin 4) K) + 1) *
              twoFunctionH (K := K) V ^ ell * twoFunctionY (K := K) V) := by
  simp [twoFunctionCarrier, mvEuler_add_local, mvEuler_mul_local,
    mvEuler_C_local, mvEuler_X_local, mvEuler_polynomialLift,
    mvEuler_two_twoFunctionY_local, mvEuler_two_twoFunctionH_pow_local]
  ring

private theorem mvEuler_three_twoFunctionCarrier_local
    {K : Type*} [CommRing K]
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    mvEuler (3 : Fin 4) (twoFunctionCarrier V ell a b P Q) =
      (V : MvPolynomial (Fin 4) K) *
        (MvPolynomial.X (0 : Fin 4) *
            (twoFunctionY (K := K) V *
                polynomialLift (twoFunctionY (K := K) V) Q.derivative +
              MvPolynomial.C b * (ell : MvPolynomial (Fin 4) K) *
                twoFunctionH (K := K) V ^ ell) +
          MvPolynomial.X (2 : Fin 4) *
            (twoFunctionY (K := K) V *
                polynomialLift (twoFunctionY (K := K) V) P.derivative +
              MvPolynomial.C a * ((ell : MvPolynomial (Fin 4) K) + 1) *
                twoFunctionH (K := K) V ^ ell *
                twoFunctionY (K := K) V)) := by
  simp [twoFunctionCarrier, mvEuler_add_local, mvEuler_mul_local,
    mvEuler_C_local, mvEuler_X_local, mvEuler_polynomialLift,
    mvEuler_three_twoFunctionY_local,
    mvEuler_three_twoFunctionH_pow_local]
  ring

set_option maxHeartbeats 2000000

/-- The Euler-scaled Hessian of the concrete two-function carrier is exactly
the abstract matrix used in `TwoFunctionEulerHessian`, in the non-unit
positive-exponent regime used by the A19 branch. -/
theorem eulerScaledHessian_twoFunctionCarrier
    {K : Type*} [CommRing K]
    (V ell : ℕ) (hV : 1 < V) (hell : 0 < ell)
    (a b : K) (P Q : Polynomial K) :
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
    simp [eulerScaledHessian, twoFunctionEulerHessianMatrix,
      mvEuler_zero_twoFunctionCarrier_local,
      mvEuler_one_twoFunctionCarrier_local,
      mvEuler_two_twoFunctionCarrier_local,
      mvEuler_three_twoFunctionCarrier_local,
      mvEuler_add_local, mvEuler_mul_local, mvEuler_C_local,
      mvEuler_natCast_local, mvEuler_one_local, mvEuler_X_local,
      mvEuler_polynomialLift, mvEuler_zero_twoFunctionY_local,
      mvEuler_one_twoFunctionY, mvEuler_two_twoFunctionY_local,
      mvEuler_three_twoFunctionY_local, mvEuler_zero_twoFunctionH_pow_local,
      mvEuler_one_twoFunctionH_pow_local, mvEuler_two_twoFunctionH_pow_local,
      mvEuler_three_twoFunctionH_pow_local] <;>
    ring

/-- Determinant factorisation for the **actual** four-variable carrier in the
same non-unit positive-exponent regime. -/
theorem det_eulerScaledHessian_twoFunctionCarrier
    {K : Type*} [CommRing K]
    (V ell : ℕ) (hV : 1 < V) (hell : 0 < ell)
    (a b : K) (P Q : Polynomial K) :
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
  rw [eulerScaledHessian_twoFunctionCarrier V ell hV hell]
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