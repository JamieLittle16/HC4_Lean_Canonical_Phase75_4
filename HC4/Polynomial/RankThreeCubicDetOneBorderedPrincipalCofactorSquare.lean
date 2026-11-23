import HC4.Polynomial.RankThreeCubicDetOnePrincipalSourceKernelPairing
import HC4.Polynomial.RankThreeCubicDetOneKernelLinePrincipalPivot
import HC4.Polynomial.RankThreeCubicDetOneBorderedKernelLine
import Mathlib.Tactic

/-!
# A determinant-one bordered Hessian fixes a transverse principal cofactor

Suppose B is a symmetric 4x4 matrix, indexed by Unit ⊕ Fin3,
with det(B)=1. If w != 0 is killed by its transverse 3x3 block
T, then B's mixed longitudinal row pairs nontrivially with w.
At any coordinate k with w[k] != 0, the transverse principal
cofactor is nonzero and satisfies

    adj(T)[k,k] * (sum_j B[x,j]*w[j])^2 = -w[k]^2.

Unlike the earlier source-origin theorem, this algebraic lemma
works at EVERY evaluation of B. We will use it at points on an
actual source pole plane and at scaled points on that plane.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

theorem detOne_borderedKernel_principalCofactor_couplingSquare
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K)
    (hSym : B.IsSymm)
    (hdet : B.det = 1)
    (w : Fin 3 → K) (hw : w ≠ 0)
    (hrows : ∀ i : Fin 3,
      (∑ j : Fin 3, B (.inr i) (.inr j) * w j) = 0)
    (k : Fin 3) (hwk : w k ≠ 0) :
    let T : Matrix (Fin 3) (Fin 3) K :=
      B.submatrix Sum.inr Sum.inr
    let g : K := ∑ j : Fin 3, B (.inl ()) (.inr j) * w j
    T.adjugate k k ≠ 0 ∧
      T.adjugate k k * g ^ 2 = -(w k ^ 2) := by
  classical
  let T : Matrix (Fin 3) (Fin 3) K :=
    B.submatrix Sum.inr Sum.inr
  let g : K := ∑ j : Fin 3, B (.inl ()) (.inr j) * w j
  let H := principalSourceFourBlock B k
  have hBne : B.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hTSym : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hSym.apply (.inr i) (.inr j)
  have hTker : T *ᵥ w = 0 := by
    funext i
    simpa only [T, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Matrix.submatrix_apply] using hrows i
  have hline : ∀ z : Fin 3 → K, T *ᵥ z = 0 →
      ∃ c : K, ∀ j : Fin 3, z j = c * w j := by
    intro z hz
    apply borderedInvertible_transverseKernel_isLine
      B hBne w hw hrows z
    intro i
    have hi := congrFun hz i
    simpa only [T, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Matrix.submatrix_apply] using hi
  have hk : T.adjugate k k ≠ 0 :=
    symmetricThree_kernelLine_principalCofactor_at
      T hTSym w hTker hline k hwk
  have hTdet : T.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, hTker⟩
  have hchart := principalSourceFourBlock_activeDet_and_schurC
    B hSym k
  have hactive : H.activeDet = T.adjugate k k := hchart.1
  have hC : H.schurC = 0 := by
    rw [hchart.2, hTdet]
  have hdetH : H.determinantCore = 1 := by
    rw [principalSourceFourBlock_determinantCore B hSym k, hdet]
  have hsq : H.schurB ^ 2 = -H.activeDet :=
    detOne_principalSchur_lastZero_couplingSquare H hdetH hC
  have hpair : H.activeDet * g = H.schurB * w k :=
    principalSourceFourBlock_schurB_kernelPairing B hSym w hrows k
  have hprod : H.activeDet ^ 2 * g ^ 2 =
      -H.activeDet * (w k) ^ 2 := by
    calc
      H.activeDet ^ 2 * g ^ 2 =
          (H.activeDet * g) ^ 2 := by ring
      _ = (H.schurB * w k) ^ 2 := by rw [hpair]
      _ = -H.activeDet * (w k) ^ 2 := by
        rw [mul_pow, hsq]
  have hδ : H.activeDet ≠ 0 := by rw [hactive]; exact hk
  have hcancel :
      H.activeDet * (H.activeDet * g ^ 2) =
        H.activeDet * (-(w k ^ 2)) := by
    calc
      _ = H.activeDet ^ 2 * g ^ 2 := by ring
      _ = -H.activeDet * (w k) ^ 2 := hprod
      _ = H.activeDet * (-(w k ^ 2)) := by ring
  have hresult : T.adjugate k k * g ^ 2 = -(w k ^ 2) := by
    rw [← hactive]
    exact mul_left_cancel₀ hδ hcancel
  exact ⟨hk, hresult⟩

end
end HC4.Polynomial.RankThreeCubic
