import HC4.Polynomial.FiniteStaircasePureModeReversedFirstVariation
import HC4.Polynomial.AutonomousODETranslation
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# Evaluation of translated pure affine staircase modes

If translating an affine-line coefficient profile by `alpha` gives the pure
mode

    u X^m,

then the original profile has a root of multiplicity `m` at `alpha`.  At the
point `X=2 alpha` its logarithmic moments are

    S0 = s,
    S1 = 2m s,
    S2 = 2m(2m-1) s,

where `s = alpha^m u`.

This file proves those identities directly from polynomial translation and
then packages them at the rank-three affine moment-matrix level.  It is
state-free and is the representation bridge between the A19 translated
one-fibre normal forms and the constant reversed first-variation matrices.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Evaluation commutes with the translation convention used in the affine
Euler package. -/
theorem eval_translatePolynomial
    (alpha x : K) (p : Polynomial K) :
    Polynomial.eval x (translatePolynomial alpha p) =
      Polynomial.eval (x + alpha) p := by
  simp [translatePolynomial, Polynomial.eval_comp]

/-- First two ordinary derivatives at `2 alpha` of a translated pure mode. -/
theorem eval_derivatives_two_mul_of_translate_eq_monomial
    (alpha : K) (phi : Polynomial K) (m : ℕ) (u0 : K)
    (hm : 2 ≤ m)
    (htrans : translatePolynomial alpha phi = Polynomial.monomial m u0) :
    Polynomial.eval (2 * alpha) phi.derivative =
        alpha ^ (m - 1) * ((m : K) * u0) ∧
      Polynomial.eval (2 * alpha) phi.derivative.derivative =
        alpha ^ (m - 2) *
          (((m : K) * ((m - 1 : ℕ) : K)) * u0) := by
  have h1poly := congrArg Polynomial.derivative htrans
  rw [derivative_translatePolynomial] at h1poly
  have h2poly := congrArg Polynomial.derivative h1poly
  rw [derivative_translatePolynomial] at h2poly
  have h1eval := congrArg (Polynomial.eval alpha) h1poly
  have h2eval := congrArg (Polynomial.eval alpha) h2poly
  have hm1 : 1 ≤ m := by omega
  have hm2 : 1 ≤ m - 1 := by omega
  constructor
  · rw [eval_translatePolynomial] at h1eval
    have hadd : alpha + alpha = 2 * alpha := by ring
    rw [hadd] at h1eval
    rw [Polynomial.derivative_monomial] at h1eval
    simpa [Polynomial.eval_monomial, mul_assoc] using h1eval
  · rw [eval_translatePolynomial] at h2eval
    have hadd : alpha + alpha = 2 * alpha := by ring
    rw [hadd] at h2eval
    rw [Polynomial.derivative_monomial] at h2eval
    rw [Polynomial.derivative_monomial] at h2eval
    have hsub : (m - 1) - 1 = m - 2 := by omega
    rw [hsub] at h2eval
    push_cast at h2eval
    simpa [Polynomial.eval_monomial, mul_assoc] using h2eval

/-- The three logarithmic moments at `2 alpha` of a translated pure mode. -/
theorem eval_eulerMoments_two_mul_of_translate_eq_monomial
    (alpha : K) (phi : Polynomial K) (m : ℕ) (u0 : K)
    (hm : 2 ≤ m)
    (htrans : translatePolynomial alpha phi = Polynomial.monomial m u0) :
    let s := alpha ^ m * u0
    Polynomial.eval (2 * alpha) phi = s ∧
      Polynomial.eval (2 * alpha) (eulerDerivative phi) =
        2 * (m : K) * s ∧
      Polynomial.eval (2 * alpha)
          (eulerDerivative (eulerDerivative phi)) =
        2 * (m : K) * (2 * (m : K) - 1) * s := by
  let s : K := alpha ^ m * u0
  have h0eval := congrArg (Polynomial.eval alpha) htrans
  rw [eval_translatePolynomial] at h0eval
  have hadd : alpha + alpha = 2 * alpha := by ring
  rw [hadd] at h0eval
  have h0 : Polynomial.eval (2 * alpha) phi = s := by
    simpa [s, Polynomial.eval_monomial] using h0eval
  rcases eval_derivatives_two_mul_of_translate_eq_monomial
      alpha phi m u0 hm htrans with ⟨h1, h2⟩
  have hm1 : m = (m - 1) + 1 := by omega
  have hm2 : m = (m - 2) + 2 := by omega
  have hpow1 : alpha ^ m = alpha ^ (m - 1) * alpha := by
    rw [hm1, pow_succ]
  have hpow2 : alpha ^ m = alpha ^ (m - 2) * alpha ^ 2 := by
    rw [hm2, pow_add]
  have hE :
      Polynomial.eval (2 * alpha) (eulerDerivative phi) =
        2 * (m : K) * s := by
    rw [eulerDerivative]
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    rw [h1, hpow1]
    dsimp [s]
    ring
  have hEE :
      Polynomial.eval (2 * alpha)
          (eulerDerivative (eulerDerivative phi)) =
        2 * (m : K) * (2 * (m : K) - 1) * s := by
    have hform :
        eulerDerivative (eulerDerivative phi) =
          Polynomial.X * phi.derivative +
            Polynomial.X ^ 2 * phi.derivative.derivative := by
      unfold eulerDerivative
      rw [Polynomial.derivative_mul, Polynomial.derivative_X]
      ring
    rw [hform]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, map_pow]
    rw [h1, h2, hpow1, hpow2]
    dsimp [s]
    push_cast
    ring
  exact ⟨h0, hE, hEE⟩

/-- Evaluating a polynomial affine moment Hessian amounts to evaluating its
three moment polynomials. -/
theorem eval_rankThreeAffinePolynomialMomentHessian
    (A B C u1 : ℕ) (q r s0 : K) (phi : Polynomial K) (x : K) :
    (fun i j => Polynomial.eval x
      (rankThreeAffinePolynomialMomentHessian
        A B C u1 q r s0 phi i j)) =
      lineMomentHessian
        (rankThreeLogBaseExponent (A : K) (B : K) (C : K))
        (rankThreeLogDirection (u1 : K) q r s0)
        (Polynomial.eval x phi)
        (Polynomial.eval x (eulerDerivative phi))
        (Polynomial.eval x (eulerDerivative (eulerDerivative phi)) ) := by
  apply Matrix.ext
  intro i j
  rw [rankThreeAffinePolynomialMomentHessian_apply]
  simp [lineMomentHessian]

/-- **Pure translated affine moment evaluation.**  At `2 alpha`, the complete
moment matrix is the scalar `alpha^m u` times the normalized moment core with
moments `(1, 2m, 2m(2m-1))`. -/
theorem eval_two_mul_rankThreeAffineMoment_of_translate_eq_monomial
    (A B C u1 m : ℕ) (q r s0 alpha u0 : K)
    (hm : 2 ≤ m)
    (phi : Polynomial K)
    (htrans : translatePolynomial alpha phi = Polynomial.monomial m u0) :
    (fun i j => Polynomial.eval (2 * alpha)
      (rankThreeAffinePolynomialMomentHessian
        A B C u1 q r s0 phi i j)) =
      (alpha ^ m * u0) •
        lineMomentHessian
          (rankThreeLogBaseExponent (A : K) (B : K) (C : K))
          (rankThreeLogDirection (u1 : K) q r s0)
          1 (2 * (m : K))
          (2 * (m : K) * (2 * (m : K) - 1)) := by
  rw [eval_rankThreeAffinePolynomialMomentHessian]
  rcases eval_eulerMoments_two_mul_of_translate_eq_monomial
      alpha phi m u0 hm htrans with ⟨h0, h1, h2⟩
  rw [h0, h1, h2]
  apply Matrix.ext
  intro i j
  simp [lineMomentHessian]
  ring

end

end HC4.Polynomial
