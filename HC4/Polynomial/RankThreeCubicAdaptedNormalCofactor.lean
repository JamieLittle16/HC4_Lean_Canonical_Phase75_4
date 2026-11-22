import HC4.Polynomial.RankThreeCubicCoordinatePlaneBinary
import HC4.Polynomial.RankThreeCubicLinearPoleFrame
import Mathlib.Tactic

/-!
# Intrinsic normal cofactor and an adapted transverse frame

Let ell be a nonzero linear functional on K³ and M invertible
with its last two columns annihilated by ell. The first row of
adj(M) is a nonzero scalar multiple of ell. Therefore if
ell*adj(H)=0, then the 00 entry of adj(Mᵀ H M) is zero.

This is the exact change-of-coordinates identity needed to
transfer the source double-pole adjugate condition to the
binary tangential Hessian in the adapted frame.
No zero-rank or constant-kernel hypotheses enter.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- The pole normal is proportional to the first adjugate row
of any frame whose second and third columns are tangent.
This identity remains valid even for a singular frame. -/
theorem tangentFrame_normal_adjugate_row
    {K : Type*} [Field K]
    (ell : Fin 3 → K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (j : Fin 3) :
    (∑ i : Fin 3, ell i * M i 0) * M.adjugate 0 j =
      M.det * ell j := by
  classical
  let t : K := ∑ i : Fin 3, ell i * M i 0
  have hrow : ell ᵥ* M = ![t, 0, 0] := by
    funext i
    fin_cases i
    · simp [t, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
    · simpa [Matrix.vecMul, dotProduct] using hM1
    · simpa [Matrix.vecMul, dotProduct] using hM2
  have hprod : (ell ᵥ* M) ᵥ* M.adjugate = M.det • ell := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate,
      Matrix.vecMul_smul, Matrix.vecMul_one]
  have hj := congrFun hprod j
  rw [hrow] at hj
  simpa [t, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using hj

/-- The first pole-normal component of an invertible adapted
frame is necessarily nonzero. -/
theorem tangentFrame_normal_first_ne_zero
    {K : Type*} [Field K]
    (ell : Fin 3 → K)
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0) :
    (∑ i : Fin 3, ell i * M i 0) ≠ 0 := by
  intro hz
  apply hell
  funext j
  have h := tangentFrame_normal_adjugate_row ell M hM1 hM2 j
  rw [hz, zero_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hM

/-- An intrinsic annihilation of all adjugate columns by the
pole normal implies that the *adapted* principal 00 cofactor
vanishes. This is the coordinate-change transfer for the
binary tangential Hessian. -/
theorem tangentFrame_normalAdjugate_principal_zero
    {K : Type*} [Field K]
    (H M : Matrix (Fin 3) (Fin 3) K)
    (ell : Fin 3 → K)
    (hell : ell ≠ 0)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (hnormal : ∀ j : Fin 3,
      (∑ i : Fin 3, ell i * H.adjugate i j) = 0) :
    (M.transpose * H * M).adjugate 0 0 = 0 := by
  classical
  let t : K := ∑ i : Fin 3, ell i * M i 0
  have ht : t ≠ 0 :=
    tangentFrame_normal_first_ne_zero ell hell M hM hM1 hM2
  have hrel (i : Fin 3) :
      t * M.adjugate 0 i = M.det * ell i :=
    tangentFrame_normal_adjugate_row ell M hM1 hM2 i
  have hrow (j : Fin 3) :
      (M.adjugate * H.adjugate) 0 j = 0 := by
    have hz : t * (M.adjugate * H.adjugate) 0 j = 0 := by
      calc
        t * (M.adjugate * H.adjugate) 0 j =
            ∑ i : Fin 3, (t * M.adjugate 0 i) *
              H.adjugate i j := by
                rw [Matrix.mul_apply, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ i : Fin 3,
              (M.det * ell i) * H.adjugate i j := by
                apply Finset.sum_congr rfl
                intro i _
                rw [hrel i]
        _ = M.det * (∑ i : Fin 3, ell i * H.adjugate i j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = 0 := by rw [hnormal j, mul_zero]
    exact (mul_eq_zero.mp hz).resolve_left ht
  have hadj :
      (M.transpose * H * M).adjugate =
        (M.adjugate * H.adjugate) * M.adjugate.transpose := by
    rw [Matrix.adjugate_mul_distrib,
      Matrix.adjugate_mul_distrib]
    rw [← Matrix.adjugate_transpose]
    rw [← Matrix.mul_assoc]
  rw [hadj]
  simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]

end
end HC4.Polynomial.RankThreeCubic
