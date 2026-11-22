import HC4.Polynomial.RankThreeCubicDetOneSourceOriginSubTwoCoupling
import Mathlib.Tactic

/-!
# A one-dimensional symmetric kernel forces a principal 2x2 pivot

For a symmetric 3x3 matrix T over a field, if its kernel is
exactly the line K*w with w nonzero, then at any index k for
which w k != 0 the complementary principal 2x2 minor is nonzero.

If that minor vanished, it would have a nonzero two-dimensional
coordinate-plane kernel vector u. Inserting a zero at coordinate k
gives z supported off k. The two complementary rows of T kill z;
symmetry and T*w=0 then force the remaining row to kill z too.
But z lies in ker T and z k=0, contradicting ker T=K*w.

This gives a principal Schur chart in the ORIGINAL coordinates,
without a shear, algebraic closure, or a rank oracle.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

/-- A symmetric 3x3 kernel line admits a nonzero principal
two-by-two pivot complementary to any nonzero coordinate of w. -/
theorem symmetricThree_kernelLine_principalCofactor_at
    (T : Matrix (Fin 3) (Fin 3) K)
    (hSym : T.IsSymm)
    (w : Fin 3 → K)
    (hTw : T *ᵥ w = 0)
    (hline : ∀ z : Fin 3 → K, T *ᵥ z = 0 →
      ∃ c : K, ∀ j : Fin 3, z j = c * w j)
    (k : Fin 3)
    (hwk : w k ≠ 0) :
    T.adjugate k k ≠ 0 := by
  classical
  intro hcof
  let N : Matrix (Fin 2) (Fin 2) K :=
    T.submatrix k.succAbove k.succAbove
  have hNdet : N.det = 0 := by
    have hadj := Matrix.adjugate_fin_succ_eq_det_submatrix T k k
    have hprod : (-1 : K) ^ ((k : ℕ) + (k : ℕ)) * N.det = 0 := by
      rw [← hadj]
      exact hcof
    have hsign : (-1 : K) ^ ((k : ℕ) + (k : ℕ)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left hsign
  obtain ⟨u, hu, hNu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hNdet
  let z : Fin 3 → K := k.insertNth 0 u
  have hz0 : z k = 0 := by simp [z]
  have hzu (j : Fin 2) : z (k.succAbove j) = u j := by simp [z]
  have hother (i : Fin 2) :
      (∑ j : Fin 3, T (k.succAbove i) j * z j) = 0 := by
    rw [Fin.sum_univ_succAbove
      (fun j : Fin 3 => T (k.succAbove i) j * z j) k]
    simp only [hz0, hzu, mul_zero, zero_add]
    have hi := congrFun hNu i
    simpa only [N, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Pi.zero_apply] using hi
  have hWrows (i : Fin 3) :
      (∑ j : Fin 3, T i j * w j) = 0 := by
    have hi := congrFun hTw i
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hi
  have hdot :
      (∑ i : Fin 3, w i *
        (∑ j : Fin 3, T i j * z j)) = 0 := by
    calc
      _ = ∑ j : Fin 3,
          (∑ i : Fin 3, T j i * w i) * z j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          rw [hSym.apply i j]
          ring
      _ = 0 := by simp only [hWrows, zero_mul, Finset.sum_const_zero]
  have hrest :
      (∑ i : Fin 2, w (k.succAbove i) *
        (∑ j : Fin 3, T (k.succAbove i) j * z j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hother i, mul_zero]
  rw [Fin.sum_univ_succAbove
    (fun i : Fin 3 => w i * (∑ j : Fin 3, T i j * z j)) k] at hdot
  rw [hrest, add_zero] at hdot
  have hk :
      (∑ j : Fin 3, T k j * z j) = 0 :=
    (mul_eq_zero.mp hdot).resolve_left hwk
  have hall : ∀ i : Fin 3,
      (∑ j : Fin 3, T i j * z j) = 0 :=
    (Fin.forall_iff_succAbove k).2 ⟨hk, hother⟩
  have hTz : T *ᵥ z = 0 := by
    funext i
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hall i
  obtain ⟨c, hc⟩ := hline z hTz
  have hc0 : c = 0 := by
    have he := hc k
    rw [hz0] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hwk
  have hz : z = 0 := by
    funext j
    rw [hc j, hc0]
    simp
  apply hu
  funext j
  have hj := congrFun hz (k.succAbove j)
  simpa [z] using hj

/-- Without choosing a pivot index in advance, any nonzero
one-dimensional kernel of a symmetric 3x3 matrix provides a
nonzero principal cofactor in the original coordinate system. -/
theorem symmetricThree_kernelLine_exists_principalCofactor
    (T : Matrix (Fin 3) (Fin 3) K)
    (hSym : T.IsSymm)
    (w : Fin 3 → K)
    (hw : w ≠ 0)
    (hTw : T *ᵥ w = 0)
    (hline : ∀ z : Fin 3 → K, T *ᵥ z = 0 →
      ∃ c : K, ∀ j : Fin 3, z j = c * w j) :
    ∃ k : Fin 3, T.adjugate k k ≠ 0 := by
  classical
  have hwpos : ∃ k : Fin 3, w k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hwpos
  exact ⟨k, symmetricThree_kernelLine_principalCofactor_at
    T hSym w hTw hline k hk⟩

end
end HC4.Polynomial.RankThreeCubic
