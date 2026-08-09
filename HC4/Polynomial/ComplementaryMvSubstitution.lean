import HC4.Polynomial.LogHessianMoments
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# The polynomial substitution bridge for complementary edges

This file begins the final upstream bridge in the complementary-edge theorem.
It avoids Laurent polynomials entirely.

For positive integer parameters, the manuscript expression

    V^(kM) * phi(U^h / V^k)

is represented directly as the honest finite multivariate polynomial

    sum_j c_j * x₁^(h*a₁*j) * x₂^(h*a₂*j)
              * x₃^(k*b₁*(M-j)) * x₄^(k*b₂*(M-j)).

The one-variable specialisation

    x₁ = X,  x₂ = x₃ = x₄ = 1

then sends it exactly to `phi.comp (X ^ (h*a₁))`.

The second ingredient is an Euler-scaled Hessian.  If
`Dᵢ = Xᵢ ∂ᵢ`, then

    Dᵢ Dⱼ F - deltaᵢⱼ Dᵢ F = Xᵢ Xⱼ ∂ᵢ∂ⱼ F.

Thus row/column multiplication by the variables can be handled inside the
ordinary polynomial ring, with no inverse variables.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- The honest `MvPolynomial` term corresponding to the `j`th coefficient on
one complementary exponent line.  The subtraction `M-j` is harmless because
coefficients with `j>M` will later be excluded by the degree bound. -/
def complementaryLineTerm
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M j : ℕ) (c : K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C c *
    MvPolynomial.X (0 : Fin 4) ^ (h * a1 * j) *
    MvPolynomial.X (1 : Fin 4) ^ (h * a2 * j) *
    MvPolynomial.X (2 : Fin 4) ^ (k * b1 * (M - j)) *
    MvPolynomial.X (3 : Fin 4) ^ (k * b2 * (M - j))

/-- The honest polynomial model of a complementary line.  For the intended
application one assumes `phi.natDegree ≤ M`; then this is precisely the
polynomial expansion of `V^(kM) phi(U^h/V^k)`. -/
def complementaryLinePolynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K) :
    MvPolynomial (Fin 4) K :=
  phi.sum fun j c => complementaryLineTerm a1 a2 b1 b2 h k M j c

/-- The specialisation `x₁=X`, `x₂=x₃=x₄=1`. -/
def complementaryLineSpecialisation
    {K : Type*} [CommSemiring K] :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X, (1 : Polynomial K), 1, 1]

/-- A single line term specialises to its coefficient times the expected
power of `X`. -/
theorem complementaryLineSpecialisation_term
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M j : ℕ) (c : K) :
    complementaryLineSpecialisation
        (complementaryLineTerm a1 a2 b1 b2 h k M j c) =
      Polynomial.C c * Polynomial.X ^ (h * a1 * j) := by
  simp [complementaryLineSpecialisation, complementaryLineTerm]

/-- The entire complementary line specialises exactly by polynomial
composition with `X^(h*a₁)`. -/
theorem complementaryLineSpecialisation_polynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K) :
    complementaryLineSpecialisation
        (complementaryLinePolynomial a1 a2 b1 b2 h k M phi) =
      phi.comp (Polynomial.X ^ (h * a1)) := by
  rw [Polynomial.comp_eq_sum_left]
  simp only [complementaryLinePolynomial, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [complementaryLineSpecialisation_term]
  simp [pow_mul]

/-- Composition with a positive power of `X` cannot kill a nonzero
polynomial. -/
theorem comp_X_pow_eq_zero_of_pos
    {K : Type*} [Field K]
    {p : Polynomial K} {n : ℕ} (hn : 0 < n)
    (hzero : p.comp (Polynomial.X ^ n) = 0) :
    p = 0 := by
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with hp | ⟨_heval, hconst⟩
  · exact hp
  · exfalso
    have h0n : 0 ≠ n := Nat.ne_of_lt hn
    have hcoeff0 : (Polynomial.X ^ n : Polynomial K).coeff 0 = 0 := by
      simp [h0n]
    have hpowzero : (Polynomial.X ^ n : Polynomial K) = 0 := by
      calc
        (Polynomial.X ^ n : Polynomial K) =
            Polynomial.C ((Polynomial.X ^ n : Polynomial K).coeff 0) := hconst
        _ = 0 := by rw [hcoeff0]; simp
    exact (pow_ne_zero n Polynomial.X_ne_zero) hpowzero

/-- Therefore the substitution `p ↦ p(X^n)` is injective for `n>0`. -/
theorem comp_X_pow_injective
    {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun p : Polynomial K =>
      p.comp (Polynomial.X ^ n)) := by
  intro p q hpq
  change p.comp (Polynomial.X ^ n) = q.comp (Polynomial.X ^ n) at hpq
  have hz : (p - q).comp (Polynomial.X ^ n) = 0 := by
    rw [Polynomial.sub_comp, hpq, sub_self]
  have hpq0 := comp_X_pow_eq_zero_of_pos (K := K) hn hz
  exact sub_eq_zero.mp hpq0

/-- The Euler operator `Dᵢ = Xᵢ ∂ᵢ` on multivariate polynomials. -/
def mvEuler
    {K : Type*} [CommSemiring K]
    (i : Fin 4) (p : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.X i * MvPolynomial.pderiv i p

/-- The Hessian after multiplying row `i` and column `j` by the corresponding
variables, written entirely in terms of Euler operators. -/
def eulerScaledHessian
    {K : Type*} [CommRing K]
    (p : MvPolynomial (Fin 4) K) : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K) :=
  Matrix.of fun i j =>
    mvEuler i (mvEuler j p) - if i = j then mvEuler i p else 0

/-- The elementary identity

`DᵢDⱼ p - δᵢⱼDᵢp = XᵢXⱼ ∂ᵢ∂ⱼp`.

This is precisely the row/column scaling that removes the apparent inverse
powers in the logarithmic-Hessian formula. -/
theorem eulerScaledHessian_apply
    {K : Type*} [CommRing K]
    (p : MvPolynomial (Fin 4) K) (i j : Fin 4) :
    eulerScaledHessian p i j =
      MvPolynomial.X i * MvPolynomial.X j *
        MvPolynomial.pderiv i (MvPolynomial.pderiv j p) := by
  by_cases hij : i = j
  · subst j
    simp [eulerScaledHessian, mvEuler, MvPolynomial.pderiv_mul]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [eulerScaledHessian, mvEuler, MvPolynomial.pderiv_mul, hij, hji]
    ring

/-- Matrix form of `eulerScaledHessian_apply`. -/
theorem eulerScaledHessian_eq
    {K : Type*} [CommRing K]
    (p : MvPolynomial (Fin 4) K) :
    eulerScaledHessian p =
      Matrix.of (fun i j =>
        MvPolynomial.X i * MvPolynomial.X j *
          MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) := by
  apply Matrix.ext
  intro i j
  exact eulerScaledHessian_apply p i j

end

end HC4.Polynomial
