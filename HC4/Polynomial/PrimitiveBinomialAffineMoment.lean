import HC4.Polynomial.PrimitiveBinomialHessianEndpoint
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# Degree-one affine moments as a primitive binomial pencil

For a rank-three affine line with coefficient support exactly `{0,1}` and
locked direction `(1,-1,-alpha,-beta)`, the polynomial-valued Euler moment
Hessian is literally

    c0 M(0,n,p,q) + c1 X M(1,n-1,p-alpha,q-beta).

This file makes that identification and extracts the three state-free
geometric determinant coefficients from a zero moment determinant.  It is the
bridge from the mature affine-line realisation stack to
`PrimitiveBinomialHessianEndpoint`.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

/-- Coefficient-scaled primitive two-monomial Hessian pencil. -/
def primitiveBinomialScaledHessianPencil
    {R : Type*} [CommRing R]
    (n p q alpha beta c0 c1 t : R) : Matrix (Fin 4) (Fin 4) R :=
  c0 • scalarExponentHessianCore (primitiveBinomialBaseExponent n p q) +
    (c1 * t) • scalarExponentHessianCore
      (primitiveBinomialFarExponent n p q alpha beta)

set_option maxHeartbeats 2000000 in
/-- Determinant of the coefficient-scaled primitive pencil.  The endpoint
coefficients only occur as nonzero scalar powers, so they can later be
cancelled without any division. -/
theorem det_primitiveBinomialScaledHessianPencil
    {R : Type*} [CommRing R]
    (n p q alpha beta c0 c1 t : R) :
    (primitiveBinomialScaledHessianPencil
      n p q alpha beta c0 c1 t).det =
      -(c0^2 * c1^2 * primitiveBinomialDetCoeff0 n p q alpha beta * t^2) -
      c0 * c1^3 * primitiveBinomialDetCoeff1 n p q alpha beta * t^3 -
      c1^4 * primitiveBinomialDetCoeff2 n p q alpha beta * t^4 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [primitiveBinomialScaledHessianPencil, scalarExponentHessianCore,
    primitiveBinomialBaseExponent, primitiveBinomialFarExponent,
    primitiveBinomialDetCoeff0, primitiveBinomialDetCoeff1,
    primitiveBinomialDetCoeff2, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- A polynomial supported exactly at `0` and `1` is its literal affine
binomial. -/
theorem polynomial_eq_coeff_zero_add_coeff_one_mul_X_of_support_zero_one
    {K : Type*} [Semiring K] (phi : Polynomial K)
    (hsupp : phi.support = {0, 1}) :
    phi = Polynomial.C (phi.coeff 0) +
      Polynomial.C (phi.coeff 1) * Polynomial.X := by
  apply Polynomial.ext
  intro j
  by_cases hj0 : j = 0
  · subst j
    simp
  by_cases hj1 : j = 1
  · subst j
    simp
  have hjnot : j ∉ phi.support := by
    rw [hsupp]
    simp [hj0, hj1]
  have hjzero : phi.coeff j = 0 := by
    simpa [Polynomial.mem_support_iff] using hjnot
  rw [hjzero]
  simp [hj0, hj1]

/-- Exact matrix identification of a degree-one locked affine moment Hessian
with the coefficient-scaled primitive binomial pencil. -/
theorem rankThreeAffineMoment_eq_primitiveBinomialScaledPencil
    {K : Type*} [Field K] [CharZero K]
    (n p q alpha beta : ℕ) (phi : Polynomial K)
    (hsupp : phi.support = {0, 1}) :
    rankThreeAffinePolynomialMomentHessian
        n p q 1 (-(alpha : K)) (-(beta : K)) phi =
      primitiveBinomialScaledHessianPencil
        (Polynomial.C (n : K)) (Polynomial.C (p : K))
        (Polynomial.C (q : K)) (Polynomial.C (alpha : K))
        (Polynomial.C (beta : K))
        (Polynomial.C (phi.coeff 0)) (Polynomial.C (phi.coeff 1))
        Polynomial.X := by
  have hphi :=
    polynomial_eq_coeff_zero_add_coeff_one_mul_X_of_support_zero_one phi hsupp
  rw [hphi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankThreeAffinePolynomialMomentHessian_apply,
      eulerDerivative, primitiveBinomialScaledHessianPencil,
      scalarExponentHessianCore, primitiveBinomialBaseExponent,
      primitiveBinomialFarExponent, rankThreeLogBaseExponent,
      rankThreeLogDirection] <;> ring

/-- Zero determinant of the actual degree-one affine moment matrix forces the
three geometric determinant coefficients to vanish. -/
theorem primitiveBinomial_coefficients_zero_of_affineMoment_det_zero
    {K : Type*} [Field K] [CharZero K]
    {n p q alpha beta : ℕ} {phi : Polynomial K}
    (hsupp : phi.support = {0, 1})
    (hphi0 : phi.coeff 0 ≠ 0) (hphi1 : phi.coeff 1 ≠ 0)
    (hdet :
      (rankThreeAffinePolynomialMomentHessian
        n p q 1 (-(alpha : K)) (-(beta : K)) phi).det = 0) :
    primitiveBinomialDetCoeff0
        (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 ∧
      primitiveBinomialDetCoeff1
        (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 ∧
      primitiveBinomialDetCoeff2
        (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
  rw [rankThreeAffineMoment_eq_primitiveBinomialScaledPencil
    n p q alpha beta phi hsupp] at hdet
  rw [det_primitiveBinomialScaledHessianPencil] at hdet

  have hc0 : Polynomial.C (phi.coeff 0) ≠ (0 : Polynomial K) := by
    simpa using hphi0
  have hc1 : Polynomial.C (phi.coeff 1) ≠ (0 : Polynomial K) := by
    simpa using hphi1

  have hcoeff2 := congrArg (fun f : Polynomial K => f.coeff 2) hdet
  have hcoeff3 := congrArg (fun f : Polynomial K => f.coeff 3) hdet
  have hcoeff4 := congrArg (fun f : Polynomial K => f.coeff 4) hdet

  have h0 :
      (phi.coeff 0)^2 * (phi.coeff 1)^2 *
        primitiveBinomialDetCoeff0
          (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
    simpa using hcoeff2
  have h1 :
      (phi.coeff 0) * (phi.coeff 1)^3 *
        primitiveBinomialDetCoeff1
          (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
    simpa using hcoeff3
  have h2 :
      (phi.coeff 1)^4 *
        primitiveBinomialDetCoeff2
          (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
    simpa using hcoeff4

  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp h0).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hphi0) (pow_ne_zero 2 hphi1))
  · exact (mul_eq_zero.mp h1).resolve_left
      (mul_ne_zero hphi0 (pow_ne_zero 3 hphi1))
  · exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 4 hphi1)

/-- Combined state-free endpoint theorem directly at the affine-moment
interface used by A19. -/
theorem primitiveBinomial_endpoint_orientation_of_affineMoment_det_zero
    {K : Type*} [Field K] [CharZero K]
    {n p q alpha beta : ℕ} {phi : Polynomial K}
    (hn : 2 ≤ n) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hpa : alpha ≤ p) (hbq : beta ≤ q)
    (hsupp : phi.support = {0, 1})
    (hphi0 : phi.coeff 0 ≠ 0) (hphi1 : phi.coeff 1 ≠ 0)
    (hdet :
      (rankThreeAffinePolynomialMomentHessian
        n p q 1 (-(alpha : K)) (-(beta : K)) phi).det = 0) :
    (p = alpha ∧ alpha = 1 ∧ q = beta * n) ∨
      (q = beta ∧ beta = 1 ∧ p = alpha * n) := by
  rcases primitiveBinomial_coefficients_zero_of_affineMoment_det_zero
      hsupp hphi0 hphi1 hdet with ⟨h0, h1, h2⟩
  exact primitiveBinomial_endpoint_orientation_of_coefficients_zero
    hn halpha hbeta hpa hbq h0 h1 h2

end

end HC4.Polynomial
