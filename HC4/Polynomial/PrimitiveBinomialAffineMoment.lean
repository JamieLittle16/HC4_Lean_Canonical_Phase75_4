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

/-- The three primitive determinant coefficients are functorial under
commutative-ring homomorphisms.  Keeping this transport abstract avoids
re-expanding large coefficient formulas after specialising to constant
polynomials. -/
private theorem primitiveBinomialDetCoeff0_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n p q alpha beta : R) :
    primitiveBinomialDetCoeff0 (f n) (f p) (f q) (f alpha) (f beta) =
      f (primitiveBinomialDetCoeff0 n p q alpha beta) := by
  have htwo : f (2 : R) = (2 : S) := by norm_num
  simp [primitiveBinomialDetCoeff0, htwo]

private theorem primitiveBinomialDetCoeff1_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n p q alpha beta : R) :
    primitiveBinomialDetCoeff1 (f n) (f p) (f q) (f alpha) (f beta) =
      f (primitiveBinomialDetCoeff1 n p q alpha beta) := by
  have htwo : f (2 : R) = (2 : S) := by norm_num
  simp [primitiveBinomialDetCoeff1, htwo]

private theorem primitiveBinomialDetCoeff2_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n p q alpha beta : R) :
    primitiveBinomialDetCoeff2 (f n) (f p) (f q) (f alpha) (f beta) =
      f (primitiveBinomialDetCoeff2 n p q alpha beta) := by
  simp [primitiveBinomialDetCoeff2]

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
  have hxzero : (Polynomial.X : Polynomial K).coeff j = 0 := by
    exact Polynomial.coeff_X_of_ne_one hj1
  rw [hjzero]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C]
  simp [hxzero, hj0]

set_option maxHeartbeats 2000000 in
/-- Exact matrix identification of a degree-one locked affine moment Hessian
with the coefficient-scaled primitive binomial pencil. -/
theorem rankThreeAffineMoment_eq_primitiveBinomialScaledPencil
    {K : Type*} [Field K] [CharZero K]
    (n p q alpha beta : ℕ) (phi : Polynomial K)
    (hsupp : phi.support = {0, 1}) :
    rankThreeAffinePolynomialMomentHessian
        n p q 1 (-(1 : K)) (-(alpha : K)) (-(beta : K)) phi =
      primitiveBinomialScaledHessianPencil
        (Polynomial.C (n : K)) (Polynomial.C (p : K))
        (Polynomial.C (q : K)) (Polynomial.C (alpha : K))
        (Polynomial.C (beta : K))
        (Polynomial.C (phi.coeff 0)) (Polynomial.C (phi.coeff 1))
        Polynomial.X := by
  ext i l
  rw [← rankThreeAffineRawMomentEntry_eq_moment
    n p q 1 (-(1 : K)) (-(alpha : K)) (-(beta : K)) phi i l]
  unfold rankThreeAffineRawMomentEntry
  simp only [Polynomial.sum_def]
  rw [hsupp]
  fin_cases i <;> fin_cases l <;>
    simp [primitiveBinomialScaledHessianPencil,
      scalarExponentHessianCore, primitiveBinomialBaseExponent,
      primitiveBinomialFarExponent, rankThreeLogBaseExponent,
      rankThreeLogDirection] <;> ring_nf

/-- Zero determinant of the actual degree-one affine moment matrix forces the
three geometric determinant coefficients to vanish. -/
theorem primitiveBinomial_coefficients_zero_of_affineMoment_det_zero
    {K : Type*} [Field K] [CharZero K]
    {n p q alpha beta : ℕ} {phi : Polynomial K}
    (hsupp : phi.support = {0, 1})
    (hphi0 : phi.coeff 0 ≠ 0) (hphi1 : phi.coeff 1 ≠ 0)
    (hdet :
      (rankThreeAffinePolynomialMomentHessian
        n p q 1 (-(1 : K)) (-(alpha : K)) (-(beta : K)) phi).det = 0) :
    primitiveBinomialDetCoeff0
        (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 ∧
      primitiveBinomialDetCoeff1
        (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 ∧
      primitiveBinomialDetCoeff2
        (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
  rw [rankThreeAffineMoment_eq_primitiveBinomialScaledPencil
    n p q alpha beta phi hsupp] at hdet
  rw [det_primitiveBinomialScaledHessianPencil] at hdet

  have hC0 :
      primitiveBinomialDetCoeff0
          (Polynomial.C (n : K)) (Polynomial.C (p : K))
          (Polynomial.C (q : K)) (Polynomial.C (alpha : K))
          (Polynomial.C (beta : K)) =
        Polynomial.C (primitiveBinomialDetCoeff0
          (n : K) (p : K) (q : K) (alpha : K) (beta : K)) :=
    primitiveBinomialDetCoeff0_map
      (Polynomial.C : K →+* Polynomial K)
      (n : K) (p : K) (q : K) (alpha : K) (beta : K)
  have hC1 :
      primitiveBinomialDetCoeff1
          (Polynomial.C (n : K)) (Polynomial.C (p : K))
          (Polynomial.C (q : K)) (Polynomial.C (alpha : K))
          (Polynomial.C (beta : K)) =
        Polynomial.C (primitiveBinomialDetCoeff1
          (n : K) (p : K) (q : K) (alpha : K) (beta : K)) :=
    primitiveBinomialDetCoeff1_map
      (Polynomial.C : K →+* Polynomial K)
      (n : K) (p : K) (q : K) (alpha : K) (beta : K)
  have hC2 :
      primitiveBinomialDetCoeff2
          (Polynomial.C (n : K)) (Polynomial.C (p : K))
          (Polynomial.C (q : K)) (Polynomial.C (alpha : K))
          (Polynomial.C (beta : K)) =
        Polynomial.C (primitiveBinomialDetCoeff2
          (n : K) (p : K) (q : K) (alpha : K) (beta : K)) :=
    primitiveBinomialDetCoeff2_map
      (Polynomial.C : K →+* Polynomial K)
      (n : K) (p : K) (q : K) (alpha : K) (beta : K)

  rw [hC0, hC1, hC2] at hdet
  simp only [← Polynomial.C_pow, ← Polynomial.C_mul] at hdet

  have h0 :
      primitiveBinomialDetCoeff0
          (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
    have h := congrArg (fun f : Polynomial K => f.coeff 2) hdet
    simp only [Polynomial.coeff_sub, Polynomial.coeff_neg] at h
    rw [Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow] at h
    norm_num at h
    rcases h with (hc0 | hc1) | hcoeff
    · exact (hphi0 hc0).elim
    · exact (hphi1 hc1).elim
    · exact hcoeff
  have h1 :
      primitiveBinomialDetCoeff1
          (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
    have h := congrArg (fun f : Polynomial K => f.coeff 3) hdet
    simp only [Polynomial.coeff_sub, Polynomial.coeff_neg] at h
    rw [Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow] at h
    norm_num at h
    rcases h with (hc0 | hc1) | hcoeff
    · exact (hphi0 hc0).elim
    · exact (hphi1 hc1).elim
    · exact hcoeff
  have h2 :
      primitiveBinomialDetCoeff2
          (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0 := by
    have h := congrArg (fun f : Polynomial K => f.coeff 4) hdet
    simp only [Polynomial.coeff_sub, Polynomial.coeff_neg] at h
    rw [Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow] at h
    norm_num at h
    rcases h with hc1 | hcoeff
    · exact (hphi1 hc1).elim
    · exact hcoeff

  exact ⟨h0, h1, h2⟩

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
        n p q 1 (-(1 : K)) (-(alpha : K)) (-(beta : K)) phi).det = 0) :
    (p = alpha ∧ alpha = 1 ∧ q = beta * n) ∨
      (q = beta ∧ beta = 1 ∧ p = alpha * n) := by
  rcases primitiveBinomial_coefficients_zero_of_affineMoment_det_zero
      hsupp hphi0 hphi1 hdet with ⟨h0, h1, h2⟩
  exact primitiveBinomial_endpoint_orientation_of_coefficients_zero
    hn halpha hbeta hpa hbq h0 h1 h2

end

end HC4.Polynomial
