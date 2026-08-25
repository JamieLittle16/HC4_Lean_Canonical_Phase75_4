import HC4.Polynomial.RankThreeBinomialPencilBridge
import Mathlib.Tactic

/-!
# A18.5.47: coefficient-weighted terminal pencil determinants

An actual degree-one Newton edge has nonzero endpoint coefficients `c0,c1`,
so its logarithmic Hessian pencil is

    c0 M(v) + c1 X M(u)

rather than the normalised `M(v)+X M(u)` used in the original terminal pencil
file.  Determinant homogeneity shows that the old identities acquire exactly
the harmless factor `c0^2 c1^2`.

We record the two terminal cases directly over `Polynomial K` so the Newton
caller never has to divide by endpoint coefficients.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

set_option maxHeartbeats 4000000

/-- Weighted sparse two-zero terminal pencil. -/
theorem det_weightedSparseRankThreeEndpointPencil
    {K : Type*} [Field K] [CharZero K]
    (C D E F c0 c1 : K) :
    (weightedRankThreeEndpointPencil
      C D E 1 0 F 0 c0 c1).det =
      Polynomial.C
        (c0^2 * c1^2 * C * E * F^2 * (C + E - 1)) *
        Polynomial.X ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Weighted one-zero terminal pencil. -/
theorem det_weightedOneZeroRankThreeEndpointPencil
    {K : Type*} [Field K] [CharZero K]
    (C D E F c0 c1 : K) :
    (weightedRankThreeEndpointPencil
      1 C D 1 0 E F c0 c1).det =
      Polynomial.C
        (c0^2 * c1^2 * (E * D - C * F)^2) *
        Polynomial.X ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The weighted sparse pencil is never singular for positive natural
rank-three data and nonzero endpoint coefficients. -/
theorem weightedSparseRankThreeEndpointPencil_det_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {C D E F : ℕ} {c0 c1 : K}
    (hC : 0 < C) (hE : 0 < E) (hF : 0 < F)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) :
    (weightedRankThreeEndpointPencil
      (K := K) C D E 1 0 F 0 c0 c1).det ≠ 0 := by
  rw [det_weightedSparseRankThreeEndpointPencil]
  apply mul_ne_zero
  · apply Polynomial.C_ne_zero.mpr
    have hCE : 0 < C + E - 1 := by omega
    have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
    have hE0 : (E : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE)
    have hF0 : (F : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hF)
    have hCE0 : ((C + E - 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hCE)
    have hNat : C + E = (C + E - 1) + 1 := by omega
    have hCast : (C : K) + (E : K) = ((C + E - 1 : ℕ) : K) + 1 := by
      exact_mod_cast hNat
    have hFactor : (C : K) + (E : K) - 1 = ((C + E - 1 : ℕ) : K) :=
      (sub_eq_iff_eq_add).2 hCast
    rw [hFactor]
    have hc01 : c0^2 * c1^2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hc1)
    have hrest :
        (C : K) * (E : K) * (F : K)^2 * ((C + E - 1 : ℕ) : K) ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero hC0 hE0)
          (pow_ne_zero 2 hF0))
        hCE0
    simpa [mul_assoc] using mul_ne_zero hc01 hrest
  · exact pow_ne_zero 2 Polynomial.X_ne_zero

/-- Singular weighted one-zero pencil forces the same endpoint cross relation
as the normalised pencil, provided both endpoint coefficients are nonzero. -/
theorem cross_relation_of_weightedOneZero_pencil_singular
    {K : Type*} [Field K] [CharZero K]
    {C D E F c0 c1 : K}
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hzero :
      (weightedRankThreeEndpointPencil
        1 C D 1 0 E F c0 c1).det = 0) :
    E * D = C * F := by
  rw [det_weightedOneZeroRankThreeEndpointPencil] at hzero
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 2) hzero
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_pos, mul_one, Polynomial.coeff_zero] at hcoeff
  have hpref : c0^2 * c1^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hc1)
  have hsq : (E * D - C * F)^2 = 0 := by
    exact (mul_eq_zero.mp hcoeff).resolve_left hpref
  have hsub : E * D - C * F = 0 := by
    exact pow_eq_zero hsq
  exact sub_eq_zero.mp hsub

end

end HC4.Polynomial
