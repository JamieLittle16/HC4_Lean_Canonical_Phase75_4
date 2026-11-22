import HC4.Polynomial.RankThreeCubicHessianCongruence
import Mathlib.Tactic

/-!
# Coordinate-free polarisation of a cubic Hessian

The Hessian of a ternary cubic is the contraction of its symmetric
third-derivative tensor D with a vector v:
  H_D(v)_{ij} = sum_t v_t * D_{tij}.

For an arbitrary linear coordinate matrix M, the congruent Hessian
Mᵀ H_D(M e_a) M has entries equal to the trilinear contraction of
D against the columns a,i,j of M.

The identities below make third-derivative symmetry available
after arbitrary *linear* changes of transverse coordinates,
without assuming any new source gradient equation.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- The full polarisation of a cubic third-derivative tensor. -/
def cubicTensorTrilinear
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (u v w : Fin 3 → K) : K :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    D i j k * u i * v j * w k

/-- The Hessian obtained by contracting a cubic tensor with a vector. -/
def cubicTensorHessianAt
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (u : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => ∑ k : Fin 3, u k * D k i j

/-- Symmetry in the first two variables of the trilinear form. -/
theorem cubicTensorTrilinear_swap12
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap : ∀ i j k : Fin 3, D i j k = D j i k)
    (u v w : Fin 3 → K) :
    cubicTensorTrilinear D u v w =
      cubicTensorTrilinear D v u w := by
  classical
  unfold cubicTensorTrilinear
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      D i j k * u i * v j * w k) =
        ∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
          D i j k * u i * v j * w k := Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
          D j i k * v j * u i * w k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [hswap i j k]
      ring

/-- Symmetry in the final two variables of the trilinear form. -/
theorem cubicTensorTrilinear_swap23
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap : ∀ i j k : Fin 3, D i j k = D i k j)
    (u v w : Fin 3 → K) :
    cubicTensorTrilinear D u v w =
      cubicTensorTrilinear D u w v := by
  classical
  unfold cubicTensorTrilinear
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j : Fin 3, ∑ k : Fin 3,
      D i j k * u i * v j * w k) =
        ∑ k : Fin 3, ∑ j : Fin 3,
          D i j k * u i * v j * w k := Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ j : Fin 3,
          D i k j * u i * w k * v j := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [hswap i j k]
      ring

/-- A completely symmetric cubic tensor gives a fully symmetric
trilinear contraction, without choosing a coordinate basis. -/
theorem cubicTensorTrilinear_swap13
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (u v w : Fin 3 → K) :
    cubicTensorTrilinear D u v w =
      cubicTensorTrilinear D w v u := by
  calc
    cubicTensorTrilinear D u v w =
        cubicTensorTrilinear D v u w :=
          cubicTensorTrilinear_swap12 D hswap₁ u v w
    _ = cubicTensorTrilinear D v w u :=
          cubicTensorTrilinear_swap23 D hswap₂ v u w
    _ = cubicTensorTrilinear D w v u :=
          cubicTensorTrilinear_swap12 D hswap₁ v w u

/-- The matrix-congruence change-of-coordinates rule for the
linear Hessian associated to a cubic third-derivative tensor.
No invertibility or tensor symmetry is needed for this identity. -/
theorem cubicTensorHessianAt_congruence_apply
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (a i j : Fin 3) :
    (M.transpose * cubicTensorHessianAt D (fun t => M t a) * M) i j =
      cubicTensorTrilinear D
        (fun t => M t a)
        (fun t => M t i)
        (fun t => M t j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    cubicTensorHessianAt, cubicTensorTrilinear,
    Fin.sum_univ_three]
  ring

end
end HC4.Polynomial.RankThreeCubic
