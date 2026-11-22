import HC4.Polynomial.RankThreeCubicCoordinatePlaneBinary
import HC4.Polynomial.RankThreeCubicTensorLinearChange
import Mathlib.Tactic

/-!
# Binary Hessian rigidity survives an arbitrary transverse coordinate frame

The congruence Mᵀ H_D(Mw) M is itself the Hessian pencil of the
transformed completely symmetric cubic tensor

  D_M(a,i,j) = D(M_a,M_i,M_j).

Thus vanishing of its normal (0,0) cofactor along w₀=0 invokes
the *same* three-point binary cubic rigidity lemma. In particular
the tangent 2x2 block has a fixed, nonzero kernel vector, independent
of the point on the plane.

The lemma deliberately states only a tangent-block kernel; it
does not assume the full 3x3 Hessian has that kernel.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 2500000

/-- Pull a symmetric cubic tensor back through a linear frame. -/
def cubicTensorInFrame
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (a i j : Fin 3) : K :=
  cubicTensorTrilinear D
    (fun t => M t a) (fun t => M t i) (fun t => M t j)

/-- Pullback preserves the first-two-index symmetry. -/
theorem cubicTensorInFrame_swap12
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap : ∀ i j k : Fin 3, D i j k = D j i k)
    (M : Matrix (Fin 3) (Fin 3) K)
    (a i j : Fin 3) :
    cubicTensorInFrame D M a i j =
      cubicTensorInFrame D M i a j := by
  unfold cubicTensorInFrame
  exact cubicTensorTrilinear_swap12 D hswap
    (fun t => M t a) (fun t => M t i) (fun t => M t j)

/-- Pullback preserves the final-two-index symmetry. -/
theorem cubicTensorInFrame_swap23
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap : ∀ i j k : Fin 3, D i j k = D i k j)
    (M : Matrix (Fin 3) (Fin 3) K)
    (a i j : Fin 3) :
    cubicTensorInFrame D M a i j =
      cubicTensorInFrame D M a j i := by
  unfold cubicTensorInFrame
  exact cubicTensorTrilinear_swap23 D hswap
    (fun t => M t a) (fun t => M t i) (fun t => M t j)

/-- Congruence and tensor pullback commute with Hessian evaluation.
No invertibility or symmetry hypotheses are needed here. -/
theorem cubicTensorInFrame_hessian
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (w : Fin 3 → K) :
    M.transpose * cubicTensorHessianAt D (M.mulVec w) * M =
      cubicTensorHessianAt (cubicTensorInFrame D M) w := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, cubicTensorHessianAt, cubicTensorInFrame,
    cubicTensorTrilinear, Fin.sum_univ_three]
  ring

/-- If the normal principal cofactor of the congruent Hessian
vanishes on a plane, its tangential 2x2 block has a common
nonzero kernel direction for *every* plane point. -/
theorem cubicTensor_adaptedPlane_constantTangentKernel
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hnormal : ∀ u v : K,
      (M.transpose *
        cubicTensorHessianAt D (M.mulVec ![(0 : K), u, v]) *
        M).adjugate 0 0 = 0) :
    ∃ r t : K,
      (r ≠ 0 ∨ t ≠ 0) ∧
      ∀ u v : K,
        let B := M.transpose *
          cubicTensorHessianAt D (M.mulVec ![(0 : K), u, v]) * M
        (B 1 1 * r + B 1 2 * t = 0) ∧
          (B 2 1 * r + B 2 2 * t = 0) := by
  classical
  let E := cubicTensorInFrame D M
  have hs12 (a i j : Fin 3) : E a i j = E i a j :=
    cubicTensorInFrame_swap12 D hswap₁ M a i j
  have hs23 (a i j : Fin 3) : E a i j = E a j i :=
    cubicTensorInFrame_swap23 D hswap₂ M a i j
  have hnormal' (u v : K) :
      (cubicTensorHessianAt E ![(0 : K), u, v]).adjugate 0 0 = 0 := by
    rw [← cubicTensorInFrame_hessian]
    exact hnormal u v
  obtain ⟨r, t, hrt, hbinary⟩ :=
    cubicTensor_coordinatePlane_normalCofactor_threeZeros_constantTangentKernel
      E hs12 hs23 (hnormal' 1 0) (hnormal' 0 1) (hnormal' 1 1)
  refine ⟨r, t, hrt, ?_⟩
  intro u v
  have hs := hbinary u v
  dsimp only
  rw [cubicTensorInFrame_hessian]
  change
    (cubicTensorHessianAt E ![(0 : K), u, v]) 1 1 * r +
      (cubicTensorHessianAt E ![(0 : K), u, v]) 1 2 * t = 0 ∧
    (cubicTensorHessianAt E ![(0 : K), u, v]) 2 1 * r +
      (cubicTensorHessianAt E ![(0 : K), u, v]) 2 2 * t = 0
  have h211 : E 2 1 1 = E 1 1 2 :=
    (hs12 2 1 1).trans (hs23 1 2 1)
  have h212 : E 2 1 2 = E 1 2 2 := hs12 2 1 2
  have h121 : E 1 2 1 = E 1 1 2 := hs23 1 2 1
  have h221 : E 2 2 1 = E 1 2 2 :=
    (hs23 2 2 1).trans (hs12 2 1 2)
  simpa [cubicTensorHessianAt, Fin.sum_univ_three,
    h211, h212, h121, h221, mul_comm] using hs

end
end HC4.Polynomial.RankThreeCubic
