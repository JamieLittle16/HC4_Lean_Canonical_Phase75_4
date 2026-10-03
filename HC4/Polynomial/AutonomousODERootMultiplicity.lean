import HC4.Polynomial.AutonomousODERootFactorisation
import Mathlib.Tactic

/-!
# A18.5.36: quadratic autonomous coefficient detects root multiplicity

The rank-three scalar endgame now knows that the autonomous target is
quadratic.  At a nonzero root of the coefficient polynomial, Phase 78 already
computed the first nonzero coefficients of the translated logarithmic Euler
numerator and eta numerator.

This file performs the one cancellation those formulas imply.  If

    eta = A rho^2 + B rho

and `alpha != 0` is a root of multiplicity `M = n+1`, then the pole-order
coefficient forces

    A * M + 1 = 0.

The linear term is one order too high at the pole and therefore does not enter
this relation.  This is the algebraic version of the local asymptotic
`eta/rho^2 -> -1/M`.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **The quadratic coefficient records the multiplicity of every nonzero
root.** -/
theorem quadraticAutonomous_root_multiplicity_relation
    {A B alpha : K}
    {phi q : Polynomial K} {n : ℕ}
    (halpha : alpha ≠ 0)
    (hq0 : q.coeff 0 ≠ 0)
    (hfactor :
      translatePolynomial alpha phi = Polynomial.X ^ (n + 1) * q)
    (hode : QuadraticAutonomousLogODE A B phi) :
    A * (((n + 1 : ℕ) : K)) + 1 = 0 := by
  have hode' :
      logarithmicEtaNumerator phi =
        Polynomial.C A * (eulerDerivative phi) ^ 2 +
          Polynomial.C B * (phi * eulerDerivative phi) := by
    simpa [QuadraticAutonomousLogODE,
      logarithmicEtaOverRhoDenominator] using hode

  have htrans :
      shiftedEtaNumerator alpha (translatePolynomial alpha phi) =
        Polynomial.C A *
            (shiftedEuler alpha (translatePolynomial alpha phi)) ^ 2 +
          Polynomial.C B *
            (translatePolynomial alpha phi *
              shiftedEuler alpha (translatePolynomial alpha phi)) := by
    calc
      shiftedEtaNumerator alpha (translatePolynomial alpha phi) =
          translatePolynomial alpha (logarithmicEtaNumerator phi) :=
        shiftedEtaNumerator_translatePolynomial alpha phi
      _ = translatePolynomial alpha
          (Polynomial.C A * (eulerDerivative phi) ^ 2 +
            Polynomial.C B * (phi * eulerDerivative phi)) := by
        rw [hode']
      _ =
          Polynomial.C A *
              (shiftedEuler alpha (translatePolynomial alpha phi)) ^ 2 +
            Polynomial.C B *
              (translatePolynomial alpha phi *
                shiftedEuler alpha (translatePolynomial alpha phi)) := by
        rw [shiftedEuler_translatePolynomial alpha phi]
        simp [translatePolynomial]

  rw [hfactor] at htrans

  have hEta :=
    coeff_two_n_shiftedEtaNumerator_X_pow_succ_mul
      (K := K) alpha q n
  have hEsq :=
    coeff_n_mul_d_shiftedEuler_pow
      (K := K) alpha q n 2
  have hphiE :
      ((Polynomial.X ^ (n + 1) * q) *
        shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)).coeff (n + n) = 0 := by
    have h :=
      coeff_n_mul_j_add_e_shiftedEuler_pow_mul_phi_pow_zero
        (K := K) alpha q n 1 1 (by omega)
    simpa [pow_one, Nat.mul_two, mul_comm] using h

  have hcoeff := congrArg (fun p : Polynomial K => p.coeff (n + n)) htrans
  change
    (shiftedEtaNumerator alpha (Polynomial.X ^ (n + 1) * q)).coeff (n + n) =
      (Polynomial.C A *
          (shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)) ^ 2 +
        Polynomial.C B *
          ((Polynomial.X ^ (n + 1) * q) *
            shiftedEuler alpha (Polynomial.X ^ (n + 1) * q))).coeff (n + n)
    at hcoeff
  rw [hEta, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    hphiE] at hcoeff
  have hEsq' :
      ((shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)) ^ 2).coeff
          (n + n) =
        (alpha * (((n + 1 : ℕ) : K)) * q.coeff 0) ^ 2 := by
    simpa [Nat.mul_two] using hEsq
  rw [hEsq'] at hcoeff
  simp only [mul_zero, add_zero] at hcoeff

  have hM : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hpref :
      alpha ^ 2 * (((n + 1 : ℕ) : K)) * (q.coeff 0) ^ 2 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 halpha) hM)
      (pow_ne_zero 2 hq0)
  have hprod :
      (alpha ^ 2 * (((n + 1 : ℕ) : K)) * (q.coeff 0) ^ 2) *
          (A * (((n + 1 : ℕ) : K)) + 1) = 0 := by
    linear_combination -hcoeff
  exact (mul_eq_zero.mp hprod).resolve_left hpref

end

end HC4.Polynomial
