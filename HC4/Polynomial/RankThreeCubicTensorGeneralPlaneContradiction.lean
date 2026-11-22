import HC4.Polynomial.RankThreeCubicLinearPoleFrame
import Mathlib.Tactic

/-!
# An arbitrary invertible rank-one cubic plane forces global degeneracy

Previous results show that if the rank-one cofactor condition holds
at three points spanning the plane of the last two columns of a
coordinate matrix M, then det H_D(Mw)=0 for every w.

Here we remove the parameterisation by M entirely. When det(M) != 0,
every vector is of the form M w, using the nonsingular matrix inverse.
Thus the cubic tensor's full Hessian determinant vanishes at every
transverse point.

This is the coordinate-free algebraic terminal statement required
to exclude a rank-one *linear* pole of the actual source Hessian.
Extracting the linear functional of the pole polynomial and applying
it to the source remains the next bridge.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- Rank-one behaviour on any plane spanned by the last two columns
of an invertible frame forces the entire cubic tensor Hessian
determinant to vanish at every point. -/
theorem cubicTensor_rankOnePlane_global_det_zero
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hA : (cubicTensorHessianAt D (fun t => M t 1)).adjugate = 0)
    (hB : (cubicTensorHessianAt D (fun t => M t 2)).adjugate = 0)
    (hAB : (cubicTensorHessianAt D
      (fun t => M t 1 + M t 2)).adjugate = 0) :
    ∀ v : Fin 3 → K, (cubicTensorHessianAt D v).det = 0 := by
  classical
  intro v
  let w : Fin 3 → K := M⁻¹ *ᵥ v
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMw : M *ᵥ w = v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMunit,
      Matrix.one_mulVec]
  rw [← hMw]
  exact cubicTensor_rankOnePlane_det_zero_on_frame
    D hswap₁ hswap₂ M hM hA hB hAB w

end
end HC4.Polynomial.RankThreeCubic
