import HC4.Polynomial.RankThreeCubicTensorAdaptedFrame
import Mathlib.Tactic

/-!
# An explicit invertible transverse frame adapted to any linear pole

A nonzero linear functional ell on K³ has a two-dimensional
kernel. Over a field we construct a 3x3 matrix M with nonzero
determinant whose last two columns lie in that kernel.

The proof uses a concrete triangular matrix in each of the
three possible nonzero coefficient cases. This avoids a hidden
choice of an adapted Schur chart and will permit applying the
coordinate-invariant tensor obstruction to any genuine linear pole.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- Any nonzero linear functional on a 3-dimensional vector space
has an explicitly constructible invertible matrix whose columns
1 and 2 lie in its kernel. -/
theorem exists_invertible_frame_annihilating_linearFunctional
    {K : Type*} [Field K]
    (ell : Fin 3 → K)
    (hell : ell ≠ 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) K,
      M.det ≠ 0 ∧
      (∑ i : Fin 3, ell i * M i 1) = 0 ∧
      (∑ i : Fin 3, ell i * M i 2) = 0 := by
  classical
  by_cases h0 : ell 0 = 0
  · by_cases h1 : ell 1 = 0
    · have h2 : ell 2 ≠ 0 := by
        intro h2
        apply hell
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      let M : Matrix (Fin 3) (Fin 3) K :=
        ![![0, 1, 0],
          ![0, 0, 1],
          ![1, -(ell 0 / ell 2), -(ell 1 / ell 2)]]
      refine ⟨M, ?_, ?_, ?_⟩
      · have hd : M.det = 1 := by
          simp [M, Matrix.det_fin_three]
        rw [hd]
        exact one_ne_zero
      · simp [M, Fin.sum_univ_three, h0, h1] <;> field_simp [h2] <;> ring
      · simp [M, Fin.sum_univ_three, h0, h1] <;> field_simp [h2] <;> ring
    · let M : Matrix (Fin 3) (Fin 3) K :=
        ![![0, 1, 0],
          ![1, -(ell 0 / ell 1), -(ell 2 / ell 1)],
          ![0, 0, 1]]
      refine ⟨M, ?_, ?_, ?_⟩
      · have hd : M.det = -1 := by
          simp [M, Matrix.det_fin_three]
        rw [hd]
        exact neg_ne_zero.mpr one_ne_zero
      · simp [M, Fin.sum_univ_three, h0] <;> field_simp [h1] <;> ring
      · simp [M, Fin.sum_univ_three, h0] <;> field_simp [h1] <;> ring
  · let M : Matrix (Fin 3) (Fin 3) K :=
      ![![1, -(ell 1 / ell 0), -(ell 2 / ell 0)],
        ![0, 1, 0],
        ![0, 0, 1]]
    refine ⟨M, ?_, ?_, ?_⟩
    · have hd : M.det = 1 := by
        simp [M, Matrix.det_fin_three]
      rw [hd]
      exact one_ne_zero
    · simp [M, Fin.sum_univ_three] <;> field_simp [h0] <;> ring
    · simp [M, Fin.sum_univ_three] <;> field_simp [h0] <;> ring

end
end HC4.Polynomial.RankThreeCubic
