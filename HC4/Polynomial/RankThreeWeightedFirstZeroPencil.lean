import HC4.Polynomial.RankThreeWeightedBoundaryPencils
import Mathlib.Tactic

/-!
# Cyclic first-zero weighted rank-three endpoint pencil

`RankThreeWeightedBoundaryPencils` records the two one-zero endpoint
orientations in which the far exponent omits coordinate `2` or `3`.  The
balance-free A19 lower first-contact route also needs the cyclic companion in
which the far endpoint omits coordinate `1`:

    v = (0,A,B,C),   u = (1,0,V,W).

The determinant has the same shape.  Its cubic coefficient has the decisive
factor `(A-1)`, so singularity with positive endpoint coordinates forces
`A=1`.  The quadratic coefficient then becomes the square of the cross
product `B*W-C*V`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

set_option maxHeartbeats 6000000

/-- Weighted determinant when the far endpoint omits the first transverse
coordinate.  This is the cyclic companion of the third/fourth-zero formulas. -/
theorem det_weightedFirstZeroRankThreeEndpointPencil
    {K : Type*} [Field K]
    (A B C V W c0 c1 : K) :
    (weightedRankThreeEndpointPencil
      A B C 1 0 V W c0 c1).det =
      Polynomial.C
          (c0^2 * c1^2 * A *
            ((B * W - C * V)^2 +
              (A - 1) * (B * W^2 + C * V^2))) * Polynomial.X ^ 2 +
        Polynomial.C
          ((c0 * c1^3 * A * V * W * (V + W)) * (A - 1)) *
          Polynomial.X ^ 3 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- A singular positive first-transverse-zero weighted pencil forces the base
exponent `A=1` and the endpoint cross relation `B*W=C*V`. -/
theorem firstZero_weightedPencil_base_eq_one_and_cross
    {K : Type*} [Field K] [CharZero K]
    {A B C V W : ℕ} {c0 c1 : K}
    (hA : 0 < A) (hV : 0 < V) (hW : 0 < W)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hzero :
      (weightedRankThreeEndpointPencil
        (K := K) A B C 1 0 V W c0 c1).det = 0) :
    A = 1 ∧ B * W = C * V := by
  rw [det_weightedFirstZeroRankThreeEndpointPencil] at hzero
  have h3 := congrArg (fun p : Polynomial K => p.coeff 3) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_neg (by omega : (3 : ℕ) ≠ 2),
    if_pos, mul_zero, zero_add, mul_one, Polynomial.coeff_zero] at h3
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hV0 : (V : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hV)
  have hW0 : (W : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
  have hVW : 0 < V + W := Nat.add_pos_left hV W
  have hVW0 : ((V + W : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hVW)
  have hsumCast : (V : K) + (W : K) = ((V + W : ℕ) : K) := by
    exact_mod_cast rfl
  have hprefix :
      c0 * c1^3 * (A : K) * (V : K) * (W : K) *
          ((V : K) + (W : K)) ≠ 0 := by
    rw [hsumCast]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero hc0 (pow_ne_zero 3 hc1)) hA0) hV0) hW0) hVW0
  have hAsub : (A : K) - 1 = 0 :=
    (mul_eq_zero.mp h3).resolve_left hprefix
  have hAcast : (A : K) = 1 := sub_eq_zero.mp hAsub
  have hAone : A = 1 := by exact_mod_cast hAcast

  have h2 := congrArg (fun p : Polynomial K => p.coeff 2) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_pos,
    if_neg (by omega : (2 : ℕ) ≠ 3), mul_one, mul_zero,
    add_zero, Polynomial.coeff_zero] at h2
  rw [hAcast] at h2
  simp only [sub_self, zero_mul, add_zero, mul_one] at h2
  have hpref2 : c0^2 * c1^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hc1)
  have hsq : ((B : K) * (W : K) - (C : K) * (V : K))^2 = 0 :=
    (mul_eq_zero.mp h2).resolve_left hpref2
  have hmul :
      ((B : K) * (W : K) - (C : K) * (V : K)) *
        ((B : K) * (W : K) - (C : K) * (V : K)) = 0 := by
    simpa [pow_two] using hsq
  have hcrossK : (B : K) * (W : K) = (C : K) * (V : K) :=
    sub_eq_zero.mp (mul_self_eq_zero.mp hmul)
  have hcross : B * W = C * V := by exact_mod_cast hcrossK
  exact ⟨hAone, hcross⟩

end

end HC4.Polynomial
