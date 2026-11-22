import HC4.Polynomial.RankThreeCubicFixedTangentTensorNormalForm
import HC4.Polynomial.RankThreeCubicTensorFrameBinaryKernel
import Mathlib.Tactic

/-!
# Canonical tangent axis for the actual fixed-kernel cubic source

The source's exactly-double pole branch gives an invertible adapted
frame M and one fixed nonzero tangent kernel w=(0,r,t).  The explicit
five-parameter normal form is stated in coordinates in which this
kernel is e_2.

This file constructs that extra change of frame WITHOUT changing the
normal coordinate or leaving the source tensor: the completed frame
is M * B, with B invertible and B e_2=w.  The transformed tensor
is the honest cubicTensorInFrame of the original tensor, so its full
symmetry and fixed-kernel property remain exact.

No rational-velocity isotropy, pole contradiction, or source mixed-
gradient vanishing is assumed or claimed here.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 2500000

/-- Complete an arbitrary nonzero tangent vector (0,r,t) to an
invertible frame which fixes the normal coordinate. -/
theorem cubicTangent_completeFrame
    {K : Type*} [Field K] (r t : K)
    (hrt : r ≠ 0 ∨ t ≠ 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) K,
      B.det ≠ 0 ∧
      B.mulVec ![(0 : K), 0, 1] = ![(0 : K), r, t] ∧
      (∀ x : Fin 3 → K, (B.mulVec x) 0 = x 0) := by
  classical
  rcases hrt with hr | ht
  · refine ⟨![![1, 0, 0], ![0, 0, r], ![0, 1, t]], ?_, ?_, ?_⟩
    · simpa [Matrix.det_fin_three] using (neg_ne_zero.mpr hr)
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro x
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨![![1, 0, 0], ![0, 1, r], ![0, 0, t]], ?_, ?_, ?_⟩
    · simpa [Matrix.det_fin_three] using ht
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro x
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- An invertible pole-adapted source frame with a fixed full tangent
kernel can always be refined so that the common kernel is e_2.
The normal plane remains coordinate zero in the refined frame. -/
theorem cubicTensor_fixedTangentKernel_normalizeFrame
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (r t : K) (hrt : r ≠ 0 ∨ t ≠ 0)
    (hfixed : ∀ u v : K,
      (M.transpose *
        cubicTensorHessianAt D (M.mulVec ![(0 : K), u, v]) *
        M) *ᵥ ![(0 : K), r, t] = 0) :
    ∃ N : Matrix (Fin 3) (Fin 3) K,
      N.det ≠ 0 ∧
      ∀ u v : K,
        (N.transpose *
          cubicTensorHessianAt D (N.mulVec ![(0 : K), u, v]) *
          N) *ᵥ ![(0 : K), 0, 1] = 0 := by
  classical
  obtain ⟨B, hBdet, hBker, hBnormal⟩ :=
    cubicTangent_completeFrame r t hrt
  refine ⟨M * B, ?_, ?_⟩
  · simpa only [Matrix.det_mul] using mul_ne_zero hM hBdet
  · intro u v
    let x : Fin 3 → K := B.mulVec ![(0 : K), u, v]
    have hx0 : x 0 = 0 := by
      change (B.mulVec ![(0 : K), u, v]) 0 = 0
      simpa using hBnormal ![(0 : K), u, v]
    have hx : x = ![(0 : K), x 1, x 2] := by
      funext i
      fin_cases i <;> simp [hx0]
    have hold :
        (M.transpose * cubicTensorHessianAt D (M.mulVec x) *
          M) *ᵥ ![(0 : K), r, t] = 0 := by
      rw [hx]
      exact hfixed (x 1) (x 2)
    change
      (((M * B).transpose *
        cubicTensorHessianAt D ((M * B).mulVec ![(0 : K), u, v]) *
        (M * B)) *ᵥ ![(0 : K), 0, 1]) = 0
    calc
      _ =
          B.transpose *ᵥ
            ((M.transpose * cubicTensorHessianAt D (M.mulVec x) * M) *ᵥ
              (B.mulVec ![(0 : K), 0, 1])) := by
            dsimp [x]
            simp only [Matrix.transpose_mul, Matrix.mulVec_mulVec,
              Matrix.mul_assoc]
      _ =
          B.transpose *ᵥ
            ((M.transpose * cubicTensorHessianAt D (M.mulVec x) * M) *ᵥ
              ![(0 : K), r, t]) := by rw [hBker]
      _ = 0 := by rw [hold]; simp

/-- The completed *source* cubic tensor is in the exact five-parameter
normal form.  This theorem does not use the rational characteristic:
it is the coordinate-compatibility bridge needed before transporting
the source gradient and residue into the model. -/
theorem cubicTensor_fixedTangentKernel_sourceFrame_fiveParameter
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (r t : K) (hrt : r ≠ 0 ∨ t ≠ 0)
    (hfixed : ∀ u v : K,
      (M.transpose *
        cubicTensorHessianAt D (M.mulVec ![(0 : K), u, v]) *
        M) *ᵥ ![(0 : K), r, t] = 0) :
    ∃ N : Matrix (Fin 3) (Fin 3) K,
      N.det ≠ 0 ∧
      ∀ z u v : K,
        N.transpose *
            cubicTensorHessianAt D (N.mulVec ![z, u, v]) * N =
          cubicFixedTangentHessian
            (cubicTensorInFrame D N 0 0 0)
            (cubicTensorInFrame D N 0 0 1)
            (cubicTensorInFrame D N 0 0 2)
            (cubicTensorInFrame D N 0 1 1)
            (cubicTensorInFrame D N 1 1 1) z u v := by
  classical
  obtain ⟨N, hN, hkernel⟩ :=
    cubicTensor_fixedTangentKernel_normalizeFrame
      D M hM r t hrt hfixed
  let E := cubicTensorInFrame D N
  have hs₁ (i j k : Fin 3) : E i j k = E j i k :=
    cubicTensorInFrame_swap12 D hswap₁ N i j k
  have hs₂ (i j k : Fin 3) : E i j k = E i k j :=
    cubicTensorInFrame_swap23 D hswap₂ N i j k
  have hfixedE (u v : K) :
      let H := cubicTensorHessianAt E ![(0 : K), u, v]
      H 0 2 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0 := by
    have hh :
        (cubicTensorHessianAt E ![(0 : K), u, v]) *ᵥ
            ![(0 : K), 0, 1] = 0 := by
      rw [← cubicTensorInFrame_hessian]
      exact hkernel u v
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h2 := congrFun hh 2
    exact ⟨by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0,
      by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1,
      by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h2⟩
  refine ⟨N, hN, ?_⟩
  intro z u v
  rw [cubicTensorInFrame_hessian]
  exact cubicTensor_fixedTangentKernel_exactFiveParameterForm
    E hs₁ hs₂ hfixedE z u v

end
end HC4.Polynomial.RankThreeCubic
