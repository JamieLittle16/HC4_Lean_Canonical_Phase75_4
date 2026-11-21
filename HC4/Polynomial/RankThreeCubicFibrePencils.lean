import HC4.Polynomial.RankTwoCubicFibrePencils
import Mathlib.RingTheory.Derivation.Basic

/-!
# Rank-three cubic fibre determinant coefficients

A moving full-rank transverse cubic has a fixed direction in which its
derivative is a scalar times a square. These determinant coefficients
apply to the original potential in that fibre direction.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix
open _root_.Polynomial

variable {R : Type*} [CommRing R]

/-- Partial Legendre Hessian in the fibre output. The transverse block
varies in one diagonal entry only, while the longitudinal diagonal
may have a quadratic term. -/
def squareFibreLegendrePencil
    (a b h p q u v c j d e t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a + b * t + h * t ^ 2, p + u * t, q + v * t;
     p + u * t, c + j * t, d;
     q + v * t, d, e]

/-- The cubic coefficient isolates the longitudinal second derivative
of the reciprocal pivot from the mixed square in the other direction. -/
theorem squareFibreLegendre_coeff_three
    (a b h p q u v c j d e : R) :
    (squareFibreLegendrePencil (C a) (C b) (C h) (C p) (C q)
      (C u) (C v) (C c) (C j) (C d) (C e) X).det.coeff 3 =
        j * (h * e - v ^ 2) := by
  let k₀ := a * (c * e - d ^ 2) - p ^ 2 * e + 2 * p * q * d - q ^ 2 * c
  let k₁ := b * (c * e - d ^ 2) + a * j * e - 2 * p * u * e +
    2 * (p * v + u * q) * d - 2 * q * v * c - q ^ 2 * j
  let k₂ := h * (c * e - d ^ 2) + b * j * e - u ^ 2 * e +
    2 * u * v * d - v ^ 2 * c - 2 * q * v * j
  have hexpand :
      (squareFibreLegendrePencil (C a) (C b) (C h) (C p) (C q)
        (C u) (C v) (C c) (C j) (C d) (C e) X).det =
      C k₀ + C k₁ * X + C k₂ * X ^ 2 + C (j * (h * e - v ^ 2)) * X ^ 3 := by
    have htwo : C (2 : R) = (2 : Polynomial R) := by
      rw [show (2 : R) = 1 + 1 by norm_num, map_add, map_one]
      norm_num
    simp [squareFibreLegendrePencil, Matrix.det_fin_three, k₀, k₁, k₂, htwo]
    ring
  rw [hexpand]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

/-- Hessian with an affine fibre and an at-most-quadratic fibre
derivative. Row order is the fibre, longitudinal, square, other. -/
def squareFibreAffinePencil
    (p q r a b c d e f A B C D t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, p, q, r;
     p, a + A * t, b + B * t, c + C * t;
     q, b + B * t, d + D * t, e;
     r, c + C * t, e, f]

private theorem det_squareFibreAffinePencil
    (p q r a b c d e f A B C D t : R) :
    (squareFibreAffinePencil p q r a b c d e f A B C D t).det =
      -(p ^ 2 * ((d + D * t) * f - e ^ 2)
        + q ^ 2 * ((a + A * t) * f - (c + C * t) ^ 2)
        + r ^ 2 * ((a + A * t) * (d + D * t) - (b + B * t) ^ 2)
        + 2 * p * q * ((c + C * t) * e - (b + B * t) * f)
        + 2 * p * r * ((b + B * t) * e - (c + C * t) * (d + D * t))
        + 2 * q * r * ((b + B * t) * (c + C * t) - (a + A * t) * e)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, squareFibreAffinePencil, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Extract the quadratic fibre term without divisions. -/
theorem squareFibreAffine_secondDifference (p q r a b c d e f A B C D : R) :
    (squareFibreAffinePencil p q r a b c d e f A B C D 1).det +
      (squareFibreAffinePencil p q r a b c d e f A B C D (-1)).det -
      2 * (squareFibreAffinePencil p q r a b c d e f A B C D 0).det =
        2 * (-(A * D * r ^ 2) + (B * r - C * q) ^ 2 + 2 * C * D * p * r) := by
  simp only [det_squareFibreAffinePencil]
  ring

/-- With no other transverse derivative in the affine fibre, its
linear determinant term is the bordered two-variable curvature times
the Hessian entry of the remaining direction. -/
theorem squareFibreAffine_firstDifference_zeroOther
    (p q a b c d e f A B D : R) :
    (squareFibreAffinePencil p q 0 a b c d e f A B 0 D 1).det -
      (squareFibreAffinePencil p q 0 a b c d e f A B 0 D 0).det =
        -(f * (D * p ^ 2 - 2 * B * p * q + A * q ^ 2)) := by
  simp only [det_squareFibreAffinePencil]
  ring

/-- An affine characteristic substitution with a polynomial
longitudinal slice cannot absorb a nonconstant determinant factor. -/
theorem polynomial_factor_eq_one {K : Type*} [CommRing K] [IsDomain K]
    {p q : Polynomial K} {c : K}
    (hc : c ≠ 0) (hmul : p * q = C c) (hq : q.coeff 0 = 1) :
    q = 1 := by
  have hprod : p * q ≠ 0 := by simpa [hmul] using hc
  have hp : p ≠ 0 := left_ne_zero_of_mul hprod
  have hq' : q ≠ 0 := right_ne_zero_of_mul hprod
  have hdeg := natDegree_mul hp hq'
  rw [hmul, natDegree_C] at hdeg
  have hzero : q.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hzero, hq, map_one]

open scoped BigOperators

/-- For a symmetric Hessian kernel, its acceleration along itself is
in the same kernel. The third derivative hypothesis is the single
index swap used in the straight characteristic argument. -/
theorem hessianKernel_acceleration {ι S A : Type*} [Fintype ι]
    [CommSemiring S] [CommRing A] [Algebra S A]
    (d : ι → Derivation S A A) (H : Matrix ι ι A) (V : ι → A)
    (hsym : ∀ i j, H i j = H j i)
    (hthird : ∀ i j k, d k (H i j) = d i (H k j))
    (hker : ∀ i, ∑ j, H i j * V j = 0) (i : ι) :
    ∑ j, H i j * (∑ k, V k * d k (V j)) = 0 := by
  have hdiff (k i : ι) :
      (∑ j, d k (H i j) * V j) + (∑ j, H i j * d k (V j)) = 0 := by
    have h := congrArg (d k) (hker i)
    simpa only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul,
      mul_comm, Finset.sum_add_distrib, add_comm] using h
  have hleft (j : ι) : ∑ k, V k * H k j = 0 := by
    simpa only [mul_comm, hsym] using hker j
  have hcancel : ∑ k, V k * (∑ j, H k j * d i (V j)) = 0 := by
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hleft, zero_mul, Finset.sum_const_zero]
  have htcancel : ∑ k, V k * (∑ j, d i (H k j) * V j) = 0 := by
    calc
      _ = ∑ k, V k * (-(∑ j, H k j * d i (V j))) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [eq_neg_of_add_eq_zero_left (hdiff i k)]
      _ = 0 := by simp only [mul_neg, Finset.sum_neg_distrib, hcancel, neg_zero]
  calc
    _ = ∑ k, V k * (∑ j, H i j * d k (V j)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -∑ k, V k * (∑ j, d k (H i j) * V j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← mul_neg, eq_neg_of_add_eq_zero_right (hdiff k i)]
    _ = 0 := by simp only [hthird, htcancel, neg_zero]

end HC4.Polynomial.RankThreeCubic
