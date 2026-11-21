import HC4.Polynomial.RankThreeLogHessian
import HC4.Polynomial.ComplementaryMvSubstitution
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# A18.5.4: an honest MvPolynomial model of a rank-three exponent line

The scalar rank-three logarithmic-Hessian stack is already complete, but until
now the repository had no analogue of `ComplementaryMvSubstitution` connecting
it to an actual multivariate polynomial.

We avoid Laurent exponents by describing a finite line segment between two
nonnegative endpoint exponent vectors.  The first endpoint is rank three:

    v = (0, v2, v3, v4),

and the second is

    u = (u1, u2, u3, u4).

For `0 <= j <= M` the honest exponent is

    e_j = (M-j) v + j u.

Thus every coordinate is a natural number.  After casting into the coefficient
field,

    e_j = M v + j (u-v),

which is exactly the affine exponent used by `RankThreeLogHessian` with base
`(0,M*v2,M*v3,M*v4)` and direction
`(u1,u2-v2,u3-v3,u4-v4)`.

The one-variable coefficient polynomial `phi` is realised by summing these
honest monomials.  Specialising `x0 = X` and the other source variables to one
recovers `phi.comp (X ^ u1)`.  Hence, when `u1 > 0`, this specialisation retains
all one-variable coefficient information.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- The `j`th honest exponent on the rank-three line segment. -/
def rankThreeLineExponentFinsupp
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) (j * u1) +
    Finsupp.single (1 : Fin 4) ((M - j) * v2 + j * u2) +
    Finsupp.single (2 : Fin 4) ((M - j) * v3 + j * u3) +
    Finsupp.single (3 : Fin 4) ((M - j) * v4 + j * u4)

@[simp] theorem rankThreeLineExponentFinsupp_apply
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ) (i : Fin 4) :
    rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M j i =
      ![j * u1,
        (M - j) * v2 + j * u2,
        (M - j) * v3 + j * u3,
        (M - j) * v4 + j * u4] i := by
  fin_cases i <;>
    simp [rankThreeLineExponentFinsupp, add_assoc]

/-- Scalar rank-three base exponent corresponding to the `j=0` endpoint. -/
def rankThreeIntegralLineBaseExponent
    {K : Type*} [Field K]
    (v2 v3 v4 M : ℕ) : Fin 4 → K :=
  rankThreeLogBaseExponent
    ((M * v2 : ℕ) : K)
    ((M * v3 : ℕ) : K)
    ((M * v4 : ℕ) : K)

/-- Scalar direction of the honest endpoint segment. -/
def rankThreeIntegralLineDirection
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 : ℕ) : Fin 4 → K :=
  rankThreeLogDirection
    (u1 : K)
    ((u2 : K) - (v2 : K))
    ((u3 : K) - (v3 : K))
    ((u4 : K) - (v4 : K))

/-- On the intended finite segment, casting the honest exponent gives exactly
the affine rank-three logarithmic exponent. -/
theorem rankThreeLineExponentFinsupp_cast_eq_affine
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ)
    (hj : j ≤ M) :
    (fun i : Fin 4 =>
      ((rankThreeLineExponentFinsupp
        v2 v3 v4 u1 u2 u3 u4 M j i : ℕ) : K)) =
      fun i =>
        rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
          (j : K) *
            rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i := by
  funext i
  fin_cases i <;>
    simp [rankThreeLineExponentFinsupp,
      rankThreeIntegralLineBaseExponent,
      rankThreeIntegralLineDirection,
      rankThreeLogBaseExponent, rankThreeLogDirection,
      Nat.cast_sub hj] <;>
    ring

/-- The honest multivariate monomial corresponding to one coefficient of the
one-variable line polynomial. -/
def rankThreeLineTerm
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ) (c : K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.C c *
    MvPolynomial.X (0 : Fin 4) ^ (j * u1) *
    MvPolynomial.X (1 : Fin 4) ^ ((M - j) * v2 + j * u2) *
    MvPolynomial.X (2 : Fin 4) ^ ((M - j) * v3 + j * u3) *
    MvPolynomial.X (3 : Fin 4) ^ ((M - j) * v4 + j * u4)

/-- The term presentation agrees with the literal monomial at the exponent
above. -/
theorem rankThreeLineTerm_eq_monomial
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ) (c : K) :
    rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c =
      MvPolynomial.monomial
        (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M j) c := by
  simp only [rankThreeLineTerm, MvPolynomial.X_pow_eq_monomial]
  rw [MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  simp only [mul_one]
  apply congrArg (fun d => MvPolynomial.monomial d c)
  ext i
  fin_cases i <;>
    simp [rankThreeLineExponentFinsupp, add_assoc]

/-- Honest multivariate polynomial supported on the finite rank-three line. -/
def rankThreeLinePolynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) : MvPolynomial (Fin 4) K :=
  phi.sum fun j c =>
    rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c

/-- Specialisation selecting the omitted-coordinate direction of the
rank-three endpoint. -/
def rankThreeLineSpecialisation
    {K : Type*} [CommSemiring K] :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X, (1 : Polynomial K), 1, 1]

/-- One honest rank-three line term specialises to the corresponding
`X^(j*u1)` term. -/
theorem rankThreeLineSpecialisation_term
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ) (c : K) :
    rankThreeLineSpecialisation
        (rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c) =
      Polynomial.C c * Polynomial.X ^ (j * u1) := by
  simp [rankThreeLineSpecialisation, rankThreeLineTerm]

/-- The entire honest rank-three line recovers the one-variable coefficient
polynomial after composition by `X^u1`. -/
theorem rankThreeLineSpecialisation_polynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) :
    rankThreeLineSpecialisation
        (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi) =
      phi.comp (Polynomial.X ^ u1) := by
  rw [Polynomial.comp_eq_sum_left]
  simp only [rankThreeLinePolynomial, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rankThreeLineSpecialisation_term]
  rw [← pow_mul]
  simp [Nat.mul_comm]

/-- If the second endpoint genuinely leaves the omitted coordinate, the
specialisation of the rank-three line is injective in its coefficient
polynomial. -/
theorem rankThreeLineSpecialisation_injective_of_u1_pos
    {K : Type*} [Field K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    (hu1 : 0 < u1) :
    Function.Injective
      (fun phi : Polynomial K =>
        rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi) := by
  intro phi psi hline
  have hspec := congrArg rankThreeLineSpecialisation hline
  rw [rankThreeLineSpecialisation_polynomial,
    rankThreeLineSpecialisation_polynomial] at hspec
  exact comp_X_pow_injective (K := K) hu1 hspec

end

end HC4.Polynomial