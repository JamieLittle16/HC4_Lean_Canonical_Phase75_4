import HC4.Valuation.QuadraticTransverseCapSourceSingularClosure
import Mathlib.Tactic

/-!
# Polynomial affine-inverse and derivative algebra for quadratic transverse rank three

The generically invertible transverse 3x3 block C(x) is intended to
satisfy the Riccati identity C'' = 2 C' C⁻¹ C'.
Over K(x) this gives (C⁻¹)'' = 0. The exact affine-inverse consequence
will subsequently be transported to the original represented source.

This file first proves the characteristic-zero *polynomial* step:
a scalar polynomial with zero second derivative is affine. Entrywise,
a 3x3 polynomial matrix with zero second derivative has the explicit
form A + X B, with A and B genuine constant K-matrices.

No extra Hessian endpoint hypothesis is attached to the source here.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A polynomial with identically vanishing second derivative is
exactly affine in the actual polynomial variable X, with
coefficients in the ground field. -/
theorem quadraticTransverse_polynomial_secondDerivative_zero_affine
    (p : Polynomial K)
    (hsecond :
      Polynomial.derivative (Polynomial.derivative p) = 0) :
    ∃ a b : K, p = Polynomial.C a +
      Polynomial.C b * Polynomial.X := by
  let b : K := (Polynomial.derivative p).coeff 0
  have hfirst : Polynomial.derivative p = Polynomial.C b :=
    Polynomial.eq_C_of_derivative_eq_zero hsecond
  let q : Polynomial K := p - Polynomial.C b * Polynomial.X
  have hq : Polynomial.derivative q = 0 := by
    simp [q, hfirst]
  have hconst : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hq
  refine ⟨q.coeff 0, b, ?_⟩
  calc
    p = q + Polynomial.C b * Polynomial.X := by dsimp [q]; ring
    _ = Polynomial.C (q.coeff 0) +
        Polynomial.C b * Polynomial.X := by rw [hconst]

/-- Entrywise zero second derivative gives an affine polynomial
matrix. Both coefficient matrices A and B genuinely lie in K;
they are not assumed to be invertible or nilpotent. -/
theorem quadraticTransverse_polynomialMatrix_secondDerivative_zero_affine
    (M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hsecond : ∀ i j : Fin 3,
      Polynomial.derivative (Polynomial.derivative (M i j)) = 0) :
    ∃ A B : Matrix (Fin 3) (Fin 3) K,
      ∀ i j : Fin 3,
        M i j = Polynomial.C (A i j) +
          Polynomial.C (B i j) * Polynomial.X := by
  classical
  have hex : ∀ i j : Fin 3, ∃ a b : K,
      M i j = Polynomial.C a + Polynomial.C b * Polynomial.X := by
    intro i j
    exact quadraticTransverse_polynomial_secondDerivative_zero_affine
      (M i j) (hsecond i j)
  choose a b hab using hex
  refine ⟨(fun i j => a i j), (fun i j => b i j), ?_⟩
  intro i j
  exact hab i j

/-- Coefficientwise polynomial differentiation of an actual
3x3 polynomial matrix. -/
def quadraticTransverse_polynomialMatrixDerivative
    (M : Matrix (Fin 3) (Fin 3) (Polynomial K)) :
    Matrix (Fin 3) (Fin 3) (Polynomial K) :=
  fun i j => Polynomial.derivative (M i j)

/-- The polynomial-matrix formal derivative obeys the exact
noncommutative product rule, without any commuting-matrix
hypothesis. This is the bridge needed for differentiating
C C⁻¹ = I in the rank-three route. -/
theorem quadraticTransverse_polynomialMatrixDerivative_mul
    (M N : Matrix (Fin 3) (Fin 3) (Polynomial K)) :
    quadraticTransverse_polynomialMatrixDerivative (M * N) =
      quadraticTransverse_polynomialMatrixDerivative M * N +
        M * quadraticTransverse_polynomialMatrixDerivative N := by
  ext i j
  change
    Polynomial.derivative
        (∑ k : Fin 3, M i k * N k j) =
      (∑ k : Fin 3,
          Polynomial.derivative (M i k) * N k j) +
        (∑ k : Fin 3,
          M i k * Polynomial.derivative (N k j))
  rw [map_sum]
  simp_rw [Polynomial.derivative_mul]
  exact (Finset.sum_add_distrib).symm

/-- The derivative of a matrix with constant polynomial entries
is identically zero, as required for affine reciprocal matrices. -/
theorem quadraticTransverse_polynomialMatrixDerivative_mapC
    (A : Matrix (Fin 3) (Fin 3) K) :
    quadraticTransverse_polynomialMatrixDerivative (A.map Polynomial.C) = 0 := by
  ext i j
  simp [quadraticTransverse_polynomialMatrixDerivative]

end

end HC4.Valuation
