import HC4.Polynomial.RankThreeCubicTensorLinearChange
import Mathlib.Tactic

/-!
# Rank-one cubic Hessian plane in an arbitrary linear frame

Let D be the symmetric third-derivative tensor of a ternary cubic,
and let M be an arbitrary 3x3 coordinate matrix. The two columns
M(-,1) and M(-,2) span the candidate rank-one plane.

If every 2x2 cofactor of the cubic Hessian vanishes at these
two directions and their sum, then the Hessian congruence
Mᵀ H_D(Mw) M has identically zero determinant for all w.

This proof does not use a coordinate-specific longitudinal source
or a hand-picked pole vector; the only geometric data is a matrix M
specifying the transverse frame. The final application requires a
frame with nonzero determinant whose two tangent columns lie on
the given prime linear pole.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-- Integrability excludes rank-one Hessian planes in any supplied
coordinate frame. This is the tensor-level coordinate-invariant
version of the coordinate-plane theorem. The matrix M need not
be invertible for the stated (congruent) determinant conclusion. -/
theorem cubicTensor_rankOnePlane_congruence_det_zero
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hA : (cubicTensorHessianAt D (fun t => M t 1)).adjugate = 0)
    (hB : (cubicTensorHessianAt D (fun t => M t 2)).adjugate = 0)
    (hAB : (cubicTensorHessianAt D
      (fun t => M t 1 + M t 2)).adjugate = 0)
    (w : Fin 3 → K) :
    (M.transpose * cubicTensorHessianAt D (M.mulVec w) * M).det = 0 := by
  classical
  let H : (Fin 3 → K) → Matrix (Fin 3) (Fin 3) K :=
    cubicTensorHessianAt D
  let C : Matrix (Fin 3) (Fin 3) K :=
    M.transpose * H (fun t => M t 0) * M
  let A : Matrix (Fin 3) (Fin 3) K :=
    M.transpose * H (fun t => M t 1) * M
  let B : Matrix (Fin 3) (Fin 3) K :=
    M.transpose * H (fun t => M t 2) * M
  have hAsymm : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change
      (M.transpose * cubicTensorHessianAt D (fun t => M t 1) * M) j i =
      (M.transpose * cubicTensorHessianAt D (fun t => M t 1) * M) i j
    rw [cubicTensorHessianAt_congruence_apply,
      cubicTensorHessianAt_congruence_apply]
    exact (cubicTensorTrilinear_swap23 D hswap₂
      (fun t => M t 1) (fun t => M t i) (fun t => M t j)).symm
  have hBsymm : B.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change
      (M.transpose * cubicTensorHessianAt D (fun t => M t 2) * M) j i =
      (M.transpose * cubicTensorHessianAt D (fun t => M t 2) * M) i j
    rw [cubicTensorHessianAt_congruence_apply,
      cubicTensorHessianAt_congruence_apply]
    exact (cubicTensorTrilinear_swap23 D hswap₂
      (fun t => M t 2) (fun t => M t i) (fun t => M t j)).symm
  have hABcompat (i : Fin 3) : A i 2 = B i 1 := by
    change
      (M.transpose * cubicTensorHessianAt D (fun t => M t 1) * M) i 2 =
      (M.transpose * cubicTensorHessianAt D (fun t => M t 2) * M) i 1
    rw [cubicTensorHessianAt_congruence_apply,
      cubicTensorHessianAt_congruence_apply]
    exact cubicTensorTrilinear_swap13 D hswap₁ hswap₂
      (fun t => M t 1) (fun t => M t i) (fun t => M t 2)
  have hCAcompat (i : Fin 3) : C i 1 = A i 0 := by
    change
      (M.transpose * cubicTensorHessianAt D (fun t => M t 0) * M) i 1 =
      (M.transpose * cubicTensorHessianAt D (fun t => M t 1) * M) i 0
    rw [cubicTensorHessianAt_congruence_apply,
      cubicTensorHessianAt_congruence_apply]
    exact cubicTensorTrilinear_swap13 D hswap₁ hswap₂
      (fun t => M t 0) (fun t => M t i) (fun t => M t 1)
  have hCBcompat (i : Fin 3) : C i 2 = B i 0 := by
    change
      (M.transpose * cubicTensorHessianAt D (fun t => M t 0) * M) i 2 =
      (M.transpose * cubicTensorHessianAt D (fun t => M t 2) * M) i 0
    rw [cubicTensorHessianAt_congruence_apply,
      cubicTensorHessianAt_congruence_apply]
    exact cubicTensorTrilinear_swap13 D hswap₁ hswap₂
      (fun t => M t 0) (fun t => M t i) (fun t => M t 2)
  have hABH :
      H (fun t => M t 1 + M t 2) =
        H (fun t => M t 1) + H (fun t => M t 2) := by
    ext i j
    change
      (∑ t : Fin 3, (M t 1 + M t 2) * D t i j) =
        (∑ t : Fin 3, M t 1 * D t i j) +
          (∑ t : Fin 3, M t 2 * D t i j)
    simp only [add_mul, Finset.sum_add_distrib]
  have hABeq :
      A + B = M.transpose * H (fun t => M t 1 + M t 2) * M := by
    rw [hABH]
    simp only [Matrix.mul_add, Matrix.add_mul]
    rfl
  have hAadj : A.adjugate = 0 :=
    adjugate_zero_of_matrix_congruence
      (H (fun t => M t 1)) M hA
  have hBadj : B.adjugate = 0 :=
    adjugate_zero_of_matrix_congruence
      (H (fun t => M t 2)) M hB
  have hABadj : (A + B).adjugate = 0 := by
    rw [hABeq]
    exact adjugate_zero_of_matrix_congruence
      (H (fun t => M t 1 + M t 2)) M hAB
  have hlinear (i j : Fin 3) :
      (M.transpose * H (M.mulVec w) * M) i j =
        w 0 * C i j + w 1 * A i j + w 2 * B i j := by
    dsimp [H, C, A, B]
    simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply,
      cubicTensorHessianAt, dotProduct, Fin.sum_univ_three]
    ring
  have hmatrix :
      M.transpose * H (M.mulVec w) * M =
        fun i j : Fin 3 =>
          w 0 * C i j + w 1 * A i j + w 2 * B i j := by
    ext i j
    exact hlinear i j
  change (M.transpose * H (M.mulVec w) * M).det = 0
  rw [hmatrix]
  exact integrable_ternaryHessian_det_zero_of_rankOne_plane
    C A B hAsymm hBsymm hABcompat hCAcompat hCBcompat
    (fun k i j => crossProducts_of_adjugate_eq_zero A hAadj k i j)
    (fun k i j => crossProducts_of_adjugate_eq_zero B hBadj k i j)
    (fun k i j => crossProducts_of_adjugate_eq_zero
      (A + B) hABadj k i j)
    (w 0) (w 1) (w 2)

/-- When the supplied frame is invertible, the rank-one plane
forces the *original* source tensor Hessian determinant to vanish
at every point of the form M w. -/
theorem cubicTensor_rankOnePlane_det_zero_on_frame
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hA : (cubicTensorHessianAt D (fun t => M t 1)).adjugate = 0)
    (hB : (cubicTensorHessianAt D (fun t => M t 2)).adjugate = 0)
    (hAB : (cubicTensorHessianAt D
      (fun t => M t 1 + M t 2)).adjugate = 0)
    (w : Fin 3 → K) :
    (cubicTensorHessianAt D (M.mulVec w)).det = 0 := by
  by_contra hn
  exact
    (det_ne_zero_of_matrix_congruence
      (cubicTensorHessianAt D (M.mulVec w)) M hn hM)
    (cubicTensor_rankOnePlane_congruence_det_zero
      D hswap₁ hswap₂ M hA hB hAB w)

end
end HC4.Polynomial.RankThreeCubic
