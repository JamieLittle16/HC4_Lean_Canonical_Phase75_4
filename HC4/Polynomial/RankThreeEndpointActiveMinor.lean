import HC4.Polynomial.RankThreeBinomialPencilBridge
import Mathlib.Tactic

/-!
# Active two-by-two minors of a degree-one rank-three endpoint pencil

For the three other-facet branches used in A19, two coordinates of the outside
rank-three endpoint remain strictly positive.  The corresponding `2 x 2`
Hessian block is the natural active Schur pivot.

The endpoint moment matrix is a polynomial pencil

    c0 M(v) + c1 X M(u).

Its active minor has degree at most two.  The coefficient of `X^2` sees only
the outside endpoint and is

    c1^2 * u_i * u_j * (1 - u_i - u_j).

Thus if both active outside exponents are positive and the outside endpoint
coefficient is nonzero, the active minor is a nonzero polynomial.  The three
cyclic forms below are exactly the `.pr`, `.sp`, and `.rq` pivots used by the
remaining first-nonfacet Schur adapter.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Principal two-coordinate minor of the weighted endpoint pencil. -/
def weightedRankThreeEndpointActiveMinor
    (A B C P Q R S c0 c1 : K)
    (i j : Fin 4) : Polynomial K :=
  let M := weightedRankThreeEndpointPencil A B C P Q R S c0 c1
  M i i * M j j - M i j * M j i

/-- Degree two of a product of two linear polynomials is the product of their
linear coefficients.  Keeping this finite convolution separate prevents the
endpoint-minor proofs below from expanding nested `coeff_mul` antidiagonals. -/
private theorem coeff_two_mul_linear
    (a0 a1 b0 b1 : K) :
    ((Polynomial.C a0 + Polynomial.X * Polynomial.C a1) *
      (Polynomial.C b0 + Polynomial.X * Polynomial.C b1)).coeff 2 =
      a1 * b1 := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  norm_num [Finset.sum_range_succ]

/-- The quadratic coefficient of a symmetric linear `2 x 2` pencil depends
only on the linear coefficient matrix. -/
theorem coeff_two_symmetricLinearMinor
    (a00 a01 a11 b00 b01 b11 : K) :
    ((Polynomial.C a00 + Polynomial.X * Polynomial.C b00) *
          (Polynomial.C a11 + Polynomial.X * Polynomial.C b11) -
        (Polynomial.C a01 + Polynomial.X * Polynomial.C b01) *
          (Polynomial.C a01 + Polynomial.X * Polynomial.C b01)).coeff 2 =
      b00 * b11 - b01 * b01 := by
  rw [Polynomial.coeff_sub,
    coeff_two_mul_linear, coeff_two_mul_linear]

/-- `.pr` active pair `(2,3)`: exact quadratic coefficient. -/
theorem coeff_two_weightedRankThreeEndpointActiveMinor_two_three
    (A B C P Q R S c0 c1 : K) :
    (weightedRankThreeEndpointActiveMinor
      A B C P Q R S c0 c1 (2 : Fin 4) 3).coeff 2 =
      c1 ^ 2 * R * S * (1 - R - S) := by
  have h := coeff_two_symmetricLinearMinor (K := K)
    (c0 * (B * B - B)) (c0 * (B * C)) (c0 * (C * C - C))
    (c1 * (R * R - R)) (c1 * (R * S)) (c1 * (S * S - S))
  calc
    (weightedRankThreeEndpointActiveMinor
        A B C P Q R S c0 c1 (2 : Fin 4) 3).coeff 2 =
        (c1 * (R * R - R)) * (c1 * (S * S - S)) -
          (c1 * (R * S)) * (c1 * (R * S)) := by
      simpa [weightedRankThreeEndpointActiveMinor,
        weightedRankThreeEndpointPencil, vectorHessianCore,
        map_mul, mul_assoc] using h
    _ = c1 ^ 2 * R * S * (1 - R - S) := by ring

/-- `.sp` active pair `(1,3)`: exact quadratic coefficient. -/
theorem coeff_two_weightedRankThreeEndpointActiveMinor_one_three
    (A B C P Q R S c0 c1 : K) :
    (weightedRankThreeEndpointActiveMinor
      A B C P Q R S c0 c1 (1 : Fin 4) 3).coeff 2 =
      c1 ^ 2 * Q * S * (1 - Q - S) := by
  have h := coeff_two_symmetricLinearMinor (K := K)
    (c0 * (A * A - A)) (c0 * (A * C)) (c0 * (C * C - C))
    (c1 * (Q * Q - Q)) (c1 * (Q * S)) (c1 * (S * S - S))
  calc
    (weightedRankThreeEndpointActiveMinor
        A B C P Q R S c0 c1 (1 : Fin 4) 3).coeff 2 =
        (c1 * (Q * Q - Q)) * (c1 * (S * S - S)) -
          (c1 * (Q * S)) * (c1 * (Q * S)) := by
      simpa [weightedRankThreeEndpointActiveMinor,
        weightedRankThreeEndpointPencil, vectorHessianCore,
        map_mul, mul_assoc] using h
    _ = c1 ^ 2 * Q * S * (1 - Q - S) := by ring

/-- `.rq` active pair `(1,2)`: exact quadratic coefficient. -/
theorem coeff_two_weightedRankThreeEndpointActiveMinor_one_two
    (A B C P Q R S c0 c1 : K) :
    (weightedRankThreeEndpointActiveMinor
      A B C P Q R S c0 c1 (1 : Fin 4) 2).coeff 2 =
      c1 ^ 2 * Q * R * (1 - Q - R) := by
  have h := coeff_two_symmetricLinearMinor (K := K)
    (c0 * (A * A - A)) (c0 * (A * B)) (c0 * (B * B - B))
    (c1 * (Q * Q - Q)) (c1 * (Q * R)) (c1 * (R * R - R))
  calc
    (weightedRankThreeEndpointActiveMinor
        A B C P Q R S c0 c1 (1 : Fin 4) 2).coeff 2 =
        (c1 * (Q * Q - Q)) * (c1 * (R * R - R)) -
          (c1 * (Q * R)) * (c1 * (Q * R)) := by
      simpa [weightedRankThreeEndpointActiveMinor,
        weightedRankThreeEndpointPencil, vectorHessianCore,
        map_mul, mul_assoc] using h
    _ = c1 ^ 2 * Q * R * (1 - Q - R) := by ring

private theorem positive_pair_core_ne_zero
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((a : K) * (b : K) * (1 - (a : K) - (b : K))) ≠ 0 := by
  have ha0 : (a : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb0 : (b : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hab : 2 ≤ a + b := by omega
  have hlast : (1 : K) - (a : K) - (b : K) ≠ 0 := by
    intro hz
    have heq : (a : K) + (b : K) = 1 := by
      linear_combination -hz
    have heqNat : a + b = 1 := by exact_mod_cast heq
    omega
  exact mul_ne_zero (mul_ne_zero ha0 hb0) hlast

/-- Positive outside coordinates `(2,3)` make the quadratic endpoint-pivot
coefficient itself nonzero. -/
theorem coeff_two_weightedRankThreeEndpointActiveMinor_two_three_ne_zero
    (A B C P Q : K) {R S : ℕ} (c0 c1 : K)
    (hR : 0 < R) (hS : 0 < S) (hc1 : c1 ≠ 0) :
    (weightedRankThreeEndpointActiveMinor
      A B C P Q (R : K) (S : K) c0 c1 (2 : Fin 4) 3).coeff 2 ≠ 0 := by
  rw [coeff_two_weightedRankThreeEndpointActiveMinor_two_three]
  simpa [mul_assoc] using
    mul_ne_zero (pow_ne_zero 2 hc1)
      (positive_pair_core_ne_zero (K := K) hR hS)

/-- Positive outside coordinates `(1,3)` make the quadratic endpoint-pivot
coefficient itself nonzero. -/
theorem coeff_two_weightedRankThreeEndpointActiveMinor_one_three_ne_zero
    (A B C P R : K) {Q S : ℕ} (c0 c1 : K)
    (hQ : 0 < Q) (hS : 0 < S) (hc1 : c1 ≠ 0) :
    (weightedRankThreeEndpointActiveMinor
      A B C P (Q : K) R (S : K) c0 c1 (1 : Fin 4) 3).coeff 2 ≠ 0 := by
  rw [coeff_two_weightedRankThreeEndpointActiveMinor_one_three]
  simpa [mul_assoc] using
    mul_ne_zero (pow_ne_zero 2 hc1)
      (positive_pair_core_ne_zero (K := K) hQ hS)

/-- Positive outside coordinates `(1,2)` make the quadratic endpoint-pivot
coefficient itself nonzero. -/
theorem coeff_two_weightedRankThreeEndpointActiveMinor_one_two_ne_zero
    (A B C P S : K) {Q R : ℕ} (c0 c1 : K)
    (hQ : 0 < Q) (hR : 0 < R) (hc1 : c1 ≠ 0) :
    (weightedRankThreeEndpointActiveMinor
      A B C P (Q : K) (R : K) S c0 c1 (1 : Fin 4) 2).coeff 2 ≠ 0 := by
  rw [coeff_two_weightedRankThreeEndpointActiveMinor_one_two]
  simpa [mul_assoc] using
    mul_ne_zero (pow_ne_zero 2 hc1)
      (positive_pair_core_ne_zero (K := K) hQ hR)

/-- Positive outside coordinates `(2,3)` give a genuine active pivot. -/
theorem weightedRankThreeEndpointActiveMinor_two_three_ne_zero
    (A B C P Q : K) {R S : ℕ} (c0 c1 : K)
    (hR : 0 < R) (hS : 0 < S) (hc1 : c1 ≠ 0) :
    weightedRankThreeEndpointActiveMinor
      A B C P Q (R : K) (S : K) c0 c1 (2 : Fin 4) 3 ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 2) hz
  simp only [Polynomial.coeff_zero] at hcoeff
  exact (coeff_two_weightedRankThreeEndpointActiveMinor_two_three_ne_zero
    A B C P Q c0 c1 hR hS hc1) (by simpa using hcoeff)

/-- Positive outside coordinates `(1,3)` give a genuine active pivot. -/
theorem weightedRankThreeEndpointActiveMinor_one_three_ne_zero
    (A B C P R : K) {Q S : ℕ} (c0 c1 : K)
    (hQ : 0 < Q) (hS : 0 < S) (hc1 : c1 ≠ 0) :
    weightedRankThreeEndpointActiveMinor
      A B C P (Q : K) R (S : K) c0 c1 (1 : Fin 4) 3 ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 2) hz
  simp only [Polynomial.coeff_zero] at hcoeff
  exact (coeff_two_weightedRankThreeEndpointActiveMinor_one_three_ne_zero
    A B C P R c0 c1 hQ hS hc1) (by simpa using hcoeff)

/-- Positive outside coordinates `(1,2)` give a genuine active pivot. -/
theorem weightedRankThreeEndpointActiveMinor_one_two_ne_zero
    (A B C P S : K) {Q R : ℕ} (c0 c1 : K)
    (hQ : 0 < Q) (hR : 0 < R) (hc1 : c1 ≠ 0) :
    weightedRankThreeEndpointActiveMinor
      A B C P (Q : K) (R : K) S c0 c1 (1 : Fin 4) 2 ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 2) hz
  simp only [Polynomial.coeff_zero] at hcoeff
  exact (coeff_two_weightedRankThreeEndpointActiveMinor_one_two_ne_zero
    A B C P S c0 c1 hQ hR hc1) (by simpa using hcoeff)

end

end HC4.Polynomial