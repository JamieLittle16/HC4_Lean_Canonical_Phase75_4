import HC4.Polynomial.RankThreePencils
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Linear coefficient of a rank-three binomial pencil

This file formalises the generic coefficient calculation used immediately
before the terminal rank-three pencil cases in the symmetric-grading proof.

For

* `v = (0,A,B,C)`, with `A,B,C > 0`, and
* `u = (P,Q,R,S)`, with the other endpoint introducing the omitted
  coordinate (`P > 0`),

the coefficient of `t` in

    det (M(v) + t M(u)),    M(z) = z zᵀ - diag(z),

is

    A B C P (P - 1) (A + B + C - 1).

We encode the pencil over the polynomial ring `K[X]`.  The coefficient of
`X` is computed as the formal derivative evaluated at `X = 0`; this avoids
expanding or naming the irrelevant quadratic, cubic and quartic terms.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- The fully generic rank-three pencil, encoded over `K[X]`, with
`v=(0,A,B,C)` and `u=(P,Q,R,S)`. -/
def rankThreePencilPolynomial {K : Type*} [CommRing K]
    (A B C P Q R S : K) : Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  !![Polynomial.X * Polynomial.C (P^2 - P),
      Polynomial.X * Polynomial.C (P * Q),
      Polynomial.X * Polynomial.C (P * R),
      Polynomial.X * Polynomial.C (P * S);
     Polynomial.X * Polynomial.C (P * Q),
      Polynomial.C (A^2 - A) + Polynomial.X * Polynomial.C (Q^2 - Q),
      Polynomial.C (A * B) + Polynomial.X * Polynomial.C (Q * R),
      Polynomial.C (A * C) + Polynomial.X * Polynomial.C (Q * S);
     Polynomial.X * Polynomial.C (P * R),
      Polynomial.C (A * B) + Polynomial.X * Polynomial.C (Q * R),
      Polynomial.C (B^2 - B) + Polynomial.X * Polynomial.C (R^2 - R),
      Polynomial.C (B * C) + Polynomial.X * Polynomial.C (R * S);
     Polynomial.X * Polynomial.C (P * S),
      Polynomial.C (A * C) + Polynomial.X * Polynomial.C (Q * S),
      Polynomial.C (B * C) + Polynomial.X * Polynomial.C (R * S),
      Polynomial.C (C^2 - C) + Polynomial.X * Polynomial.C (S^2 - S)]

set_option maxHeartbeats 2000000

/-- The explicit polynomial matrix is exactly the coefficientwise lift of
`M(v) + X M(u)` to `K[X]`.

Writing the bridge entrywise fixes the base coefficient ring before applying
`Polynomial.C`, avoiding any ambiguous `Semiring`/scalar-action metavariable. -/
theorem rankThreePencilPolynomial_eq_core {K : Type*} [CommRing K]
    (A B C P Q R S : K) :
    rankThreePencilPolynomial A B C P Q R S =
      Matrix.of (fun i j =>
        Polynomial.C
            (vectorHessianCore (K := K) ![0, A, B, C] i j) +
          (Polynomial.X : Polynomial K) *
            Polynomial.C
              (vectorHessianCore (K := K) ![P, Q, R, S] i j)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankThreePencilPolynomial, vectorHessianCore, pow_two] <;> ring

/-- Formal-derivative form of the manuscript's generic coefficient-of-`t`
calculation.  The variables `Q,R,S` cancel from the linear term.

The determinant/derivative normalisation is another fixed finite symbolic
calculation, so it receives the same local elaboration budget. -/
theorem derivative_det_rankThreePencilPolynomial_eval_zero
    {K : Type*} [CommRing K]
    (A B C P Q R S : K) :
    Polynomial.eval 0
        (Polynomial.derivative
          (rankThreePencilPolynomial A B C P Q R S).det) =
      A * B * C * P * (P - 1) * (A + B + C - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [rankThreePencilPolynomial, Matrix.det_fin_three, Fin.succAbove,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul]
  ring

/-- Literal coefficient-of-`X` version of the same identity. -/
theorem coeff_one_det_rankThreePencilPolynomial
    {K : Type*} [CommRing K]
    (A B C P Q R S : K) :
    ((rankThreePencilPolynomial A B C P Q R S).det).coeff 1 =
      A * B * C * P * (P - 1) * (A + B + C - 1) := by
  have h := derivative_det_rankThreePencilPolynomial_eval_zero
    (K := K) A B C P Q R S
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h
  simpa [Polynomial.coeff_derivative] using h

/-- If the rank-three pencil determinant is the zero polynomial, positivity
of the three rank-three exponents and of the introduced exponent forces the
introduced exponent to be exactly one.  This is the manuscript step
`u₁ > 0` and vanishing linear coefficient `⇒ u₁ = 1`. -/
theorem introduced_exponent_eq_one_of_rankThree_pencil_singular
    {K : Type*} [Field K] [CharZero K]
    {A B C P Q R S : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hsing :
      (rankThreePencilPolynomial (K := K)
        A B C P Q R S).det = 0) :
    P = 1 := by
  have hcoeff :
      (A : K) * (B : K) * (C : K) * (P : K) * ((P : K) - 1) *
          ((A : K) + (B : K) + (C : K) - 1) = 0 := by
    calc
      (A : K) * (B : K) * (C : K) * (P : K) * ((P : K) - 1) *
            ((A : K) + (B : K) + (C : K) - 1) =
          ((rankThreePencilPolynomial (K := K)
            A B C P Q R S).det).coeff 1 := by
              symm
              exact coeff_one_det_rankThreePencilPolynomial
                (K := K) A B C P Q R S
      _ = 0 := by rw [hsing]; simp

  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hP0 : (P : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hprefix : (A : K) * (B : K) * (C : K) * (P : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 hB0) hC0) hP0

  have hsumNat : 0 < A + B + C - 1 := by omega
  have hsumNat0 : A + B + C - 1 ≠ 0 := Nat.ne_of_gt hsumNat
  have hsumCast0 : (((A + B + C - 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast hsumNat0
  have hNat : A + B + C = (A + B + C - 1) + 1 := by omega
  have hCast : (A : K) + (B : K) + (C : K) =
      ((A + B + C - 1 : ℕ) : K) + 1 := by
    exact_mod_cast hNat
  have hsumEq :
      (A : K) + (B : K) + (C : K) - 1 =
        ((A + B + C - 1 : ℕ) : K) := by
    linear_combination hCast
  have hsum0 : (A : K) + (B : K) + (C : K) - 1 ≠ 0 := by
    rw [hsumEq]
    exact hsumCast0

  have hmiddle :
      ((A : K) * (B : K) * (C : K) * (P : K)) * ((P : K) - 1) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_right hsum0
  have hPsub : (P : K) - 1 = 0 :=
    (mul_eq_zero.mp hmiddle).resolve_left hprefix
  have hPcast : (P : K) = 1 := sub_eq_zero.mp hPsub
  exact_mod_cast hPcast

end

end HC4.Polynomial
