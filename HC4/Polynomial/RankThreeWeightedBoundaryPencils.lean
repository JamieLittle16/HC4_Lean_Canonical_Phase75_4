import HC4.Polynomial.RankThreeWeightedPencils
import Mathlib.Tactic

/-!
# A18.5.49: primitive boundary pencil coefficients

After A18.5.44 a balanced primitive far endpoint has one of four shapes.  Two
of them are already the sparse two-zero pencil.  The remaining one-zero
orientations are

    v=(0,A,B,C), u=(1,Q,0,S)
    v=(0,A,B,C), u=(1,Q,R,0).

For their coefficient-weighted endpoint pencils the cubic determinant
coefficient has a decisive factor `(B-1)` or `(C-1)` respectively.  Hence
singularity with positive endpoint data forces the corresponding base exponent
to be exactly one.  The quadratic coefficient then reduces to the square of
the endpoint cross product.

We also record the other two-zero primitive endpoint `u=(1,0,0,1)` directly.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

set_option maxHeartbeats 6000000

/-- Weighted determinant for the primitive `p`-ray endpoint. -/
theorem det_weightedPTransitionRankThreeEndpointPencil
    {K : Type*} [Field K]
    (A B C c0 c1 : K) :
    (weightedRankThreeEndpointPencil
      A B C 1 0 0 1 c0 c1).det =
      Polynomial.C
        (c0^2 * c1^2 * A * B * (A + B - 1)) * Polynomial.X ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Weighted determinant when the far endpoint omits the third coordinate. -/
theorem det_weightedThirdZeroRankThreeEndpointPencil
    {K : Type*} [Field K]
    (A B C Q S c0 c1 : K) :
    (weightedRankThreeEndpointPencil
      A B C 1 Q 0 S c0 c1).det =
      Polynomial.C
          (c0^2 * c1^2 * B *
            ((A * S - C * Q)^2 +
              (B - 1) * (A * S^2 + C * Q^2))) * Polynomial.X ^ 2 +
        Polynomial.C
          ((c0 * c1^3 * B * Q * S * (Q + S)) * (B - 1)) *
          Polynomial.X ^ 3 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Weighted determinant when the far endpoint omits the fourth coordinate. -/
theorem det_weightedFourthZeroRankThreeEndpointPencil
    {K : Type*} [Field K]
    (A B C Q R c0 c1 : K) :
    (weightedRankThreeEndpointPencil
      A B C 1 Q R 0 c0 c1).det =
      Polynomial.C
          (c0^2 * c1^2 * C *
            ((A * R - B * Q)^2 +
              (C - 1) * (A * R^2 + B * Q^2))) * Polynomial.X ^ 2 +
        Polynomial.C
          ((c0 * c1^3 * C * Q * R * (Q + R)) * (C - 1)) *
          Polynomial.X ^ 3 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The primitive `p`-ray endpoint cannot occur in a singular weighted pencil
when the relevant base exponents and endpoint coefficients are nonzero. -/
theorem weightedPTransitionRankThreeEndpointPencil_det_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {A B C : ℕ} {c0 c1 : K}
    (hA : 0 < A) (hB : 0 < B)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) :
    (weightedRankThreeEndpointPencil
      (K := K) A B C 1 0 0 1 c0 c1).det ≠ 0 := by
  rw [det_weightedPTransitionRankThreeEndpointPencil]
  apply mul_ne_zero
  · apply Polynomial.C_ne_zero.mpr
    have hAB : 0 < A + B - 1 := by omega
    have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
    have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
    have hAB0 : ((A + B - 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hAB)
    have hNat : A + B = (A + B - 1) + 1 := by omega
    have hCast : (A : K) + (B : K) = ((A + B - 1 : ℕ) : K) + 1 := by
      exact_mod_cast hNat
    have hFactor : (A : K) + (B : K) - 1 = ((A + B - 1 : ℕ) : K) :=
      (sub_eq_iff_eq_add).2 hCast
    rw [hFactor]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hc1)) hA0)
        hB0)
      hAB0
  · exact pow_ne_zero 2 Polynomial.X_ne_zero

/-- A singular positive third-zero weighted pencil forces the base exponent
`B=1` and the endpoint cross relation `A*S=C*Q`. -/
theorem thirdZero_weightedPencil_base_eq_one_and_cross
    {K : Type*} [Field K] [CharZero K]
    {A B C Q S : ℕ} {c0 c1 : K}
    (hB : 0 < B) (hQ : 0 < Q) (hS : 0 < S)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hzero :
      (weightedRankThreeEndpointPencil
        (K := K) A B C 1 Q 0 S c0 c1).det = 0) :
    B = 1 ∧ A * S = C * Q := by
  rw [det_weightedThirdZeroRankThreeEndpointPencil] at hzero
  have h3 := congrArg (fun p : Polynomial K => p.coeff 3) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_neg (by omega : (3 : ℕ) ≠ 2),
    if_pos, mul_zero, zero_add, mul_one, Polynomial.coeff_zero] at h3
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hQ0 : (Q : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hS0 : (S : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  have hQS : 0 < Q + S := Nat.add_pos_left hQ S
  have hQS0 : ((Q + S : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hQS)
  have hsumCast : (Q : K) + (S : K) = ((Q + S : ℕ) : K) := by
    exact_mod_cast rfl
  have hprefix :
      c0 * c1^3 * (B : K) * (Q : K) * (S : K) *
          ((Q : K) + (S : K)) ≠ 0 := by
    rw [hsumCast]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero hc0 (pow_ne_zero 3 hc1)) hB0) hQ0) hS0) hQS0
  have hBsub : (B : K) - 1 = 0 :=
    (mul_eq_zero.mp h3).resolve_left hprefix
  have hBcast : (B : K) = 1 := sub_eq_zero.mp hBsub
  have hBone : B = 1 := by exact_mod_cast hBcast

  have h2 := congrArg (fun p : Polynomial K => p.coeff 2) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_pos,
    if_neg (by omega : (2 : ℕ) ≠ 3), mul_one, mul_zero,
    add_zero, Polynomial.coeff_zero] at h2
  rw [hBcast] at h2
  simp only [one_sub_one, zero_mul, add_zero, mul_one] at h2
  have hpref2 : c0^2 * c1^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hc1)
  have hsq : ((A : K) * (S : K) - (C : K) * (Q : K))^2 = 0 :=
    (mul_eq_zero.mp h2).resolve_left hpref2
  have hmul :
      ((A : K) * (S : K) - (C : K) * (Q : K)) *
        ((A : K) * (S : K) - (C : K) * (Q : K)) = 0 := by
    simpa [pow_two] using hsq
  have hcrossK : (A : K) * (S : K) = (C : K) * (Q : K) :=
    sub_eq_zero.mp (mul_self_eq_zero.mp hmul)
  have hcross : A * S = C * Q := by exact_mod_cast hcrossK
  exact ⟨hBone, hcross⟩

/-- A singular positive fourth-zero weighted pencil forces the base exponent
`C=1` and the endpoint cross relation `A*R=B*Q`. -/
theorem fourthZero_weightedPencil_base_eq_one_and_cross
    {K : Type*} [Field K] [CharZero K]
    {A B C Q R : ℕ} {c0 c1 : K}
    (hC : 0 < C) (hQ : 0 < Q) (hR : 0 < R)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hzero :
      (weightedRankThreeEndpointPencil
        (K := K) A B C 1 Q R 0 c0 c1).det = 0) :
    C = 1 ∧ A * R = B * Q := by
  rw [det_weightedFourthZeroRankThreeEndpointPencil] at hzero
  have h3 := congrArg (fun p : Polynomial K => p.coeff 3) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_neg (by omega : (3 : ℕ) ≠ 2),
    if_pos, mul_zero, zero_add, mul_one, Polynomial.coeff_zero] at h3
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hQ0 : (Q : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hR0 : (R : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hQR : 0 < Q + R := Nat.add_pos_left hQ R
  have hQR0 : ((Q + R : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hQR)
  have hsumCast : (Q : K) + (R : K) = ((Q + R : ℕ) : K) := by
    exact_mod_cast rfl
  have hprefix :
      c0 * c1^3 * (C : K) * (Q : K) * (R : K) *
          ((Q : K) + (R : K)) ≠ 0 := by
    rw [hsumCast]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero hc0 (pow_ne_zero 3 hc1)) hC0) hQ0) hR0) hQR0
  have hCsub : (C : K) - 1 = 0 :=
    (mul_eq_zero.mp h3).resolve_left hprefix
  have hCcast : (C : K) = 1 := sub_eq_zero.mp hCsub
  have hCone : C = 1 := by exact_mod_cast hCcast

  have h2 := congrArg (fun p : Polynomial K => p.coeff 2) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_pos,
    if_neg (by omega : (2 : ℕ) ≠ 3), mul_one, mul_zero,
    add_zero, Polynomial.coeff_zero] at h2
  rw [hCcast] at h2
  simp only [one_sub_one, zero_mul, add_zero, mul_one] at h2
  have hpref2 : c0^2 * c1^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hc1)
  have hsq : ((A : K) * (R : K) - (B : K) * (Q : K))^2 = 0 :=
    (mul_eq_zero.mp h2).resolve_left hpref2
  have hmul :
      ((A : K) * (R : K) - (B : K) * (Q : K)) *
        ((A : K) * (R : K) - (B : K) * (Q : K)) = 0 := by
    simpa [pow_two] using hsq
  have hcrossK : (A : K) * (R : K) = (B : K) * (Q : K) :=
    sub_eq_zero.mp (mul_self_eq_zero.mp hmul)
  have hcross : A * R = B * Q := by exact_mod_cast hcrossK
  exact ⟨hCone, hcross⟩

end

end HC4.Polynomial
