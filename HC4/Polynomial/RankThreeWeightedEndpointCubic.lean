import HC4.Polynomial.RankThreeBinomialPencilBridge
import Mathlib.Tactic

/-!
# Cubic coefficient of a weighted rank-three endpoint pencil

For a degree-one affine rank-three slice the Euler-moment matrix is the
weighted endpoint pencil

    c0 M(v) + X c1 M(u).

The linear coefficient sees the coordinate introduced at `v -> u`.  Dually,
when the far endpoint `u` lies on a different coordinate hyperplane, the
*cubic* coefficient sees the coordinate introduced when the pencil is read
backwards from `u` to `v`.

The two formulas below are precisely the cases needed by the `.pr` highest
slice.  They show that if the far endpoint vanishes in coordinate `2` or `3`,
singularity forces the corresponding positive base exponent to be `1`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

set_option maxHeartbeats 2000000

/-- Far endpoint `u=(1,Q,0,S)`: the cubic determinant coefficient sees the
base coordinate `B`. -/
theorem coeff_three_weightedRankThreeEndpointPencil_two_zero
    {K : Type*} [CommRing K]
    (A B C Q S c0 c1 : K) :
    ((weightedRankThreeEndpointPencil
      A B C 1 Q 0 S c0 c1).det).coeff 3 =
      B * Q * S * c0 * c1 ^ 3 * (B - 1) * (Q + S) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_mul, Polynomial.coeff_C,
    Polynomial.coeff_X]
  ring

/-- Far endpoint `u=(1,Q,R,0)`: the cubic determinant coefficient sees the
base coordinate `C`. -/
theorem coeff_three_weightedRankThreeEndpointPencil_three_zero
    {K : Type*} [CommRing K]
    (A B C Q R c0 c1 : K) :
    ((weightedRankThreeEndpointPencil
      A B C 1 Q R 0 c0 c1).det).coeff 3 =
      C * Q * R * c0 * c1 ^ 3 * (C - 1) * (Q + R) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_mul, Polynomial.coeff_C,
    Polynomial.coeff_X]
  ring

/-- In characteristic zero, an identically singular weighted endpoint pencil
with far endpoint `(1,Q,0,S)` and positive remaining far coordinates forces
the positive base coordinate `B` to equal one. -/
theorem base_two_eq_one_of_weighted_endpoint_pencil_singular
    {K : Type*} [Field K] [CharZero K]
    {A B C Q S : ℕ} {c0 c1 : K}
    (hB : 0 < B) (hQ : 0 < Q) (hS : 0 < S)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hsing :
      (weightedRankThreeEndpointPencil
        (A : K) (B : K) (C : K) 1 (Q : K) 0 (S : K) c0 c1).det = 0) :
    B = 1 := by
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 3) hsing
  rw [coeff_three_weightedRankThreeEndpointPencil_two_zero] at hcoeff
  simp only [Polynomial.coeff_zero] at hcoeff
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hQ0 : (Q : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hS0 : (S : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  have hQS : (Q : K) + (S : K) ≠ 0 := by
    have hnat : Q + S ≠ 0 := by omega
    have hcast : ((Q + S : ℕ) : K) ≠ 0 := by exact_mod_cast hnat
    simpa [Nat.cast_add] using hcast
  have hprefix :
      (B : K) * (Q : K) * (S : K) * c0 * c1 ^ 3 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hB0 hQ0) hS0) hc0)
      (pow_ne_zero 3 hc1)
  have hmiddle :
      ((B : K) * (Q : K) * (S : K) * c0 * c1 ^ 3) *
        ((B : K) - 1) = 0 :=
    (mul_eq_zero.mp (by simpa [mul_assoc] using hcoeff)).resolve_right hQS
  have hsub : (B : K) - 1 = 0 :=
    (mul_eq_zero.mp hmiddle).resolve_left hprefix
  have hcast : (B : K) = 1 := sub_eq_zero.mp hsub
  exact_mod_cast hcast

/-- Symmetric coordinate-`3` version. -/
theorem base_three_eq_one_of_weighted_endpoint_pencil_singular
    {K : Type*} [Field K] [CharZero K]
    {A B C Q R : ℕ} {c0 c1 : K}
    (hC : 0 < C) (hQ : 0 < Q) (hR : 0 < R)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hsing :
      (weightedRankThreeEndpointPencil
        (A : K) (B : K) (C : K) 1 (Q : K) (R : K) 0 c0 c1).det = 0) :
    C = 1 := by
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 3) hsing
  rw [coeff_three_weightedRankThreeEndpointPencil_three_zero] at hcoeff
  simp only [Polynomial.coeff_zero] at hcoeff
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hQ0 : (Q : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hR0 : (R : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hQR : (Q : K) + (R : K) ≠ 0 := by
    have hnat : Q + R ≠ 0 := by omega
    have hcast : ((Q + R : ℕ) : K) ≠ 0 := by exact_mod_cast hnat
    simpa [Nat.cast_add] using hcast
  have hprefix :
      (C : K) * (Q : K) * (R : K) * c0 * c1 ^ 3 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hC0 hQ0) hR0) hc0)
      (pow_ne_zero 3 hc1)
  have hmiddle :
      ((C : K) * (Q : K) * (R : K) * c0 * c1 ^ 3) *
        ((C : K) - 1) = 0 :=
    (mul_eq_zero.mp (by simpa [mul_assoc] using hcoeff)).resolve_right hQR
  have hsub : (C : K) - 1 = 0 :=
    (mul_eq_zero.mp hmiddle).resolve_left hprefix
  have hcast : (C : K) = 1 := sub_eq_zero.mp hsub
  exact_mod_cast hcast

end

end HC4.Polynomial
