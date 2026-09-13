import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Primitive two-monomial Hessian endpoint classification

This is the state-free algebra needed after the A19 highest planar slice has
been reduced to two adjacent monomials.  Write the two exponent vectors as

    v = (0, n, p, q),
    u = (1, n - 1, p - alpha, q - beta).

The Euler-scaled Hessian core of a monomial with exponent `d` is
`d d^T - diag(d)`.  Hence, after varying the first coordinate, the two-term
slice gives the matrix pencil

    M(v) + t M(u).

Its determinant is `-t^2 (c0 + c1 t + c2 t^2)`.  The top coefficient factors
as

    c2 = (p-alpha)(q-beta)(n-1)
           (n+p+q-alpha-beta-1).

For `n >= 2` and positive drops this forces one far transverse coordinate to
vanish.  The middle and constant coefficients then force the corresponding
drop to be exactly one and the remaining starting coordinate to be the other
drop times `n`.

No HC4 state, balance hypothesis, repair tag, blocker clock, or JC2 statement
appears here.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

/-- Numerical Euler-Hessian core for a four-component exponent vector. -/
def scalarExponentHessianCore
    {R : Type*} [CommRing R] (d : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => d i * d j - if i = j then d i else 0

/-- Base exponent `(0,n,p,q)` of the primitive binomial slice. -/
def primitiveBinomialBaseExponent
    {R : Type*} [CommRing R] (n p q : R) : Fin 4 → R :=
  ![0, n, p, q]

/-- Far exponent `(1,n-1,p-alpha,q-beta)`. -/
def primitiveBinomialFarExponent
    {R : Type*} [CommRing R] (n p q alpha beta : R) : Fin 4 → R :=
  ![1, n - 1, p - alpha, q - beta]

/-- Euler-Hessian matrix pencil of the two exponent cores. -/
def primitiveBinomialHessianPencil
    {R : Type*} [CommRing R]
    (n p q alpha beta t : R) : Matrix (Fin 4) (Fin 4) R :=
  scalarExponentHessianCore (primitiveBinomialBaseExponent n p q) +
    t • scalarExponentHessianCore
      (primitiveBinomialFarExponent n p q alpha beta)

/-- Constant coefficient of the residual quadratic determinant factor. -/
def primitiveBinomialDetCoeff0
    {R : Type*} [CommRing R] (n p q alpha beta : R) : R :=
  -(alpha^2 * n^2 * q) - alpha^2 * n * q^2 + alpha^2 * n * q +
    2 * alpha * beta * n * p * q - beta^2 * n^2 * p -
    beta^2 * n * p^2 + beta^2 * n * p + n^2 * p * q +
    n * p^2 * q + n * p * q^2 - 2 * n * p * q - p^2 * q -
    p * q^2 + p * q

/-- Linear coefficient of the residual quadratic determinant factor. -/
def primitiveBinomialDetCoeff1
    {R : Type*} [CommRing R] (n p q alpha beta : R) : R :=
  (n - 1) *
    (alpha^2 * beta * n - alpha^2 * n * q - alpha^2 * q^2 +
      alpha^2 * q + alpha * beta^2 * n + 2 * alpha * beta * p * q -
      alpha * n * q - 2 * alpha * p * q - alpha * q^2 + alpha * q -
      beta^2 * n * p - beta^2 * p^2 + beta^2 * p - beta * n * p -
      beta * p^2 - 2 * beta * p * q + beta * p + 2 * n * p * q +
      2 * p^2 * q + 2 * p * q^2 - 2 * p * q)

/-- Top coefficient of the residual quadratic determinant factor. -/
def primitiveBinomialDetCoeff2
    {R : Type*} [CommRing R] (n p q alpha beta : R) : R :=
  (p - alpha) * (q - beta) * (n - 1) *
    (n + p + q - alpha - beta - 1)

set_option maxHeartbeats 2000000 in
/-- Exact determinant of the primitive two-monomial Euler-Hessian pencil. -/
theorem det_primitiveBinomialHessianPencil
    {R : Type*} [CommRing R] (n p q alpha beta t : R) :
    (primitiveBinomialHessianPencil n p q alpha beta t).det =
      -(t^2) *
        (primitiveBinomialDetCoeff0 n p q alpha beta +
          primitiveBinomialDetCoeff1 n p q alpha beta * t +
          primitiveBinomialDetCoeff2 n p q alpha beta * t^2) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [primitiveBinomialHessianPencil, scalarExponentHessianCore,
    primitiveBinomialBaseExponent, primitiveBinomialFarExponent,
    primitiveBinomialDetCoeff0, primitiveBinomialDetCoeff1,
    primitiveBinomialDetCoeff2, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- On the `p = alpha` boundary, the middle determinant coefficient has a
four-factor form. -/
theorem primitiveBinomialDetCoeff1_of_p_eq_alpha
    {R : Type*} [CommRing R] (n q alpha beta : R) :
    primitiveBinomialDetCoeff1 n alpha q alpha beta =
      -alpha * (alpha - 1) * (q - beta) * (n - 1) *
        (n + q - beta - 1) := by
  simp [primitiveBinomialDetCoeff1]
  ring

/-- Symmetric middle-coefficient factorisation on `q = beta`. -/
theorem primitiveBinomialDetCoeff1_of_q_eq_beta
    {R : Type*} [CommRing R] (n p alpha beta : R) :
    primitiveBinomialDetCoeff1 n p beta alpha beta =
      -beta * (p - alpha) * (beta - 1) * (n - 1) *
        (n + p - alpha - 1) := by
  simp [primitiveBinomialDetCoeff1]
  ring

/-- If both far transverse coordinates vanish, the constant coefficient is
already nonzero in the positive integral range. -/
theorem primitiveBinomialDetCoeff0_of_both_boundary
    {R : Type*} [CommRing R] (n alpha beta : R) :
    primitiveBinomialDetCoeff0 n alpha beta alpha beta =
      -alpha * beta * (n - 1)^2 * (alpha + beta - 1) := by
  simp [primitiveBinomialDetCoeff0]
  ring

/-- After `p = alpha` and `alpha = 1`, the constant coefficient is the
negative square measuring the remaining endpoint mismatch. -/
theorem primitiveBinomialDetCoeff0_of_p_boundary_alpha_one
    {R : Type*} [CommRing R] (n q beta : R) :
    primitiveBinomialDetCoeff0 n 1 q 1 beta =
      -(q - beta * n)^2 := by
  simp [primitiveBinomialDetCoeff0]
  ring

/-- Symmetric negative-square identity. -/
theorem primitiveBinomialDetCoeff0_of_q_boundary_beta_one
    {R : Type*} [CommRing R] (n p alpha : R) :
    primitiveBinomialDetCoeff0 n p 1 alpha 1 =
      -(p - alpha * n)^2 := by
  simp [primitiveBinomialDetCoeff0]
  ring

/-- **Primitive binomial endpoint orientation.**

For integral nonnegative exponents, vanishing of the three determinant
coefficients leaves exactly the two source-honest orientations. -/
theorem primitiveBinomial_endpoint_orientation_of_coefficients_zero
    {K : Type*} [Field K] [CharZero K]
    {n p q alpha beta : ℕ}
    (hn : 2 ≤ n) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hpa : alpha ≤ p) (hbq : beta ≤ q)
    (h0 : primitiveBinomialDetCoeff0
      (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0)
    (h1 : primitiveBinomialDetCoeff1
      (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0)
    (h2 : primitiveBinomialDetCoeff2
      (n : K) (p : K) (q : K) (alpha : K) (beta : K) = 0) :
    (p = alpha ∧ alpha = 1 ∧ q = beta * n) ∨
      (q = beta ∧ beta = 1 ∧ p = alpha * n) := by
  have hn1 : (n : K) - 1 ≠ 0 := by
    intro hz
    have hk : (n : K) = 1 := sub_eq_zero.mp hz
    have hnat : n = 1 := by exact_mod_cast hk
    omega
  have hsum :
      (n : K) + (p : K) + (q : K) - (alpha : K) - (beta : K) - 1 ≠ 0 := by
    intro hz
    have hk : (n : K) + (p : K) + (q : K) =
        (alpha : K) + (beta : K) + 1 := by
      linear_combination hz
    have hnat : n + p + q = alpha + beta + 1 := by
      exact_mod_cast hk
    omega
  have hboundary : p = alpha ∨ q = beta := by
    simp only [primitiveBinomialDetCoeff2] at h2
    rcases mul_eq_zero.mp h2 with hpaK | hrest
    · left
      have hk : (p : K) = (alpha : K) := sub_eq_zero.mp hpaK
      exact_mod_cast hk
    · rcases mul_eq_zero.mp hrest with hqbK | hrest
      · right
        have hk : (q : K) = (beta : K) := sub_eq_zero.mp hqbK
        exact_mod_cast hk
      · rcases mul_eq_zero.mp hrest with hnK | hsumK
        · exact (hn1 hnK).elim
        · exact (hsum hsumK).elim
  rcases hboundary with hp | hq
  · subst p
    by_cases hqb : q = beta
    · subst q
      rw [primitiveBinomialDetCoeff0_of_both_boundary] at h0
      have ha0 : (alpha : K) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt halpha
      have hb0 : (beta : K) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hbeta
      have hab1 : (alpha : K) + (beta : K) - 1 ≠ 0 := by
        intro hz
        have hk : (alpha : K) + (beta : K) = 1 := sub_eq_zero.mp hz
        have hnat : alpha + beta = 1 := by exact_mod_cast hk
        omega
      have hprod :
          -(alpha : K) * (beta : K) * ((n : K) - 1)^2 *
              ((alpha : K) + (beta : K) - 1) ≠ 0 := by
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0) hb0)
            (pow_ne_zero 2 hn1)) hab1
      exact (hprod h0).elim
    · have hqbPos : beta < q := lt_of_le_of_ne hbq (Ne.symm hqb)
      rw [primitiveBinomialDetCoeff1_of_p_eq_alpha] at h1
      have ha0 : (alpha : K) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt halpha
      have hqbeta : (q : K) - (beta : K) ≠ 0 := by
        intro hz
        have hk : (q : K) = (beta : K) := sub_eq_zero.mp hz
        have hnat : q = beta := by exact_mod_cast hk
        exact hqb hnat
      have htail : (n : K) + (q : K) - (beta : K) - 1 ≠ 0 := by
        intro hz
        have hk : (n : K) + (q : K) = (beta : K) + 1 := by
          linear_combination hz
        have hnat : n + q = beta + 1 := by exact_mod_cast hk
        omega
      have ha1 : alpha = 1 := by
        by_contra hne
        have ha1K : (alpha : K) - 1 ≠ 0 := by
          intro hz
          have hk : (alpha : K) = 1 := sub_eq_zero.mp hz
          have hnat : alpha = 1 := by exact_mod_cast hk
          exact hne hnat
        have hprod :
            -(alpha : K) * ((alpha : K) - 1) *
                ((q : K) - (beta : K)) * ((n : K) - 1) *
                ((n : K) + (q : K) - (beta : K) - 1) ≠ 0 := by
          exact mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (mul_ne_zero (neg_ne_zero.mpr ha0) ha1K) hqbeta) hn1) htail
        exact (hprod h1).elim
      rw [ha1, primitiveBinomialDetCoeff0_of_p_boundary_alpha_one] at h0
      have hsquare : ((q : K) - (beta : K) * (n : K))^2 = 0 := by
        exact neg_eq_zero.mp h0
      have hlin : (q : K) - (beta : K) * (n : K) = 0 :=
        (sq_eq_zero_iff).mp hsquare
      have hk : (q : K) = (beta : K) * (n : K) := sub_eq_zero.mp hlin
      have hqn : q = beta * n := by exact_mod_cast hk
      exact Or.inl ⟨rfl, ha1, hqn⟩
  · subst q
    by_cases hpaEq : p = alpha
    · subst p
      rw [primitiveBinomialDetCoeff0_of_both_boundary] at h0
      have ha0 : (alpha : K) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt halpha
      have hb0 : (beta : K) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hbeta
      have hab1 : (alpha : K) + (beta : K) - 1 ≠ 0 := by
        intro hz
        have hk : (alpha : K) + (beta : K) = 1 := sub_eq_zero.mp hz
        have hnat : alpha + beta = 1 := by exact_mod_cast hk
        omega
      have hprod :
          -(alpha : K) * (beta : K) * ((n : K) - 1)^2 *
              ((alpha : K) + (beta : K) - 1) ≠ 0 := by
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0) hb0)
            (pow_ne_zero 2 hn1)) hab1
      exact (hprod h0).elim
    · have hpaPos : alpha < p := lt_of_le_of_ne hpa (Ne.symm hpaEq)
      rw [primitiveBinomialDetCoeff1_of_q_eq_beta] at h1
      have hb0 : (beta : K) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hbeta
      have hpalpha : (p : K) - (alpha : K) ≠ 0 := by
        intro hz
        have hk : (p : K) = (alpha : K) := sub_eq_zero.mp hz
        have hnat : p = alpha := by exact_mod_cast hk
        exact hpaEq hnat
      have htail : (n : K) + (p : K) - (alpha : K) - 1 ≠ 0 := by
        intro hz
        have hk : (n : K) + (p : K) = (alpha : K) + 1 := by
          linear_combination hz
        have hnat : n + p = alpha + 1 := by exact_mod_cast hk
        omega
      have hb1 : beta = 1 := by
        by_contra hne
        have hb1K : (beta : K) - 1 ≠ 0 := by
          intro hz
          have hk : (beta : K) = 1 := sub_eq_zero.mp hz
          have hnat : beta = 1 := by exact_mod_cast hk
          exact hne hnat
        have hprod :
            -(beta : K) * ((p : K) - (alpha : K)) *
                ((beta : K) - 1) * ((n : K) - 1) *
                ((n : K) + (p : K) - (alpha : K) - 1) ≠ 0 := by
          exact mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (mul_ne_zero (neg_ne_zero.mpr hb0) hpalpha) hb1K) hn1) htail
        exact (hprod h1).elim
      rw [hb1, primitiveBinomialDetCoeff0_of_q_boundary_beta_one] at h0
      have hsquare : ((p : K) - (alpha : K) * (n : K))^2 = 0 := by
        exact neg_eq_zero.mp h0
      have hlin : (p : K) - (alpha : K) * (n : K) = 0 :=
        (sq_eq_zero_iff).mp hsquare
      have hk : (p : K) = (alpha : K) * (n : K) := sub_eq_zero.mp hlin
      have hpn : p = alpha * n := by exact_mod_cast hk
      exact Or.inr ⟨rfl, hb1, hpn⟩

end

end HC4.Polynomial
