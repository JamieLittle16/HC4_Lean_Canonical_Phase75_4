import HC4.Polynomial.RankThreeCubicZeroAdjugateRankOne
import Mathlib.Tactic

/-!
# Finite cubic Hessian plane obstruction from actual tensor symmetry

A ternary cubic's Hessian is the linear matrix pencil
  H(x,y,z) = x*C + y*A + z*B,
where C, A, B are the slices of its completely symmetric
third-derivative tensor.

If all 2x2 cofactors vanish at the three points
(0,1,0), (0,0,1), and (0,1,1), then A, B, A+B
each have rank at most one. Pencil rigidity and the symmetry
of the third derivative tensor then force the determinant of
H(x,y,z) to vanish for every x,y,z.

This statement explicitly records the tensor integrability
required for a Hessian, with no separate rank-pivot assumption.
It is an algebraic coordinate-plane theorem. Connecting an
arbitrary source pole hyperplane requires an adapted
linear coordinate chart.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- A symmetric cubic third-derivative tensor cannot have a
generically nonsingular Hessian if three points on the
coordinate plane all have vanishing 2x2 cofactors. -/
theorem integrable_ternaryTensor_det_zero_of_plane_cofactor_zero
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hA : (fun i j : Fin 3 => D 1 i j : Matrix (Fin 3) (Fin 3) K).adjugate = 0)
    (hB : (fun i j : Fin 3 => D 2 i j : Matrix (Fin 3) (Fin 3) K).adjugate = 0)
    (hAB : ((fun i j : Fin 3 => D 1 i j : Matrix (Fin 3) (Fin 3) K) +
      (fun i j : Fin 3 => D 2 i j : Matrix (Fin 3) (Fin 3) K)).adjugate = 0)
    (x y z : K) :
    Matrix.det (fun i j : Fin 3 =>
      x * D 0 i j + y * D 1 i j + z * D 2 i j) = 0 := by
  classical
  let C : Matrix (Fin 3) (Fin 3) K := fun i j => D 0 i j
  let A : Matrix (Fin 3) (Fin 3) K := fun i j => D 1 i j
  let B : Matrix (Fin 3) (Fin 3) K := fun i j => D 2 i j
  have hAsym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact (hswap₂ 1 i j).symm
  have hBsym : B.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact (hswap₂ 2 i j).symm
  have hcompatAB (i : Fin 3) : A i 2 = B i 1 := by
    calc
      D 1 i 2 = D 1 2 i := hswap₂ 1 i 2
      _ = D 2 1 i := hswap₁ 1 2 i
      _ = D 2 i 1 := hswap₂ 2 1 i
  have hcompatCA (i : Fin 3) : C i 1 = A i 0 := by
    calc
      D 0 i 1 = D 0 1 i := hswap₂ 0 i 1
      _ = D 1 0 i := hswap₁ 0 1 i
      _ = D 1 i 0 := hswap₂ 1 0 i
  have hcompatCB (i : Fin 3) : C i 2 = B i 0 := by
    calc
      D 0 i 2 = D 0 2 i := hswap₂ 0 i 2
      _ = D 2 0 i := hswap₁ 0 2 i
      _ = D 2 i 0 := hswap₂ 2 0 i
  exact integrable_ternaryHessian_det_zero_of_rankOne_plane
    C A B hAsym hBsym hcompatAB hcompatCA hcompatCB
    (fun k i j => crossProducts_of_adjugate_eq_zero A hA k i j)
    (fun k i j => crossProducts_of_adjugate_eq_zero B hB k i j)
    (fun k i j => crossProducts_of_adjugate_eq_zero (A + B) hAB k i j)
    x y z

/-- Contrapositive: a generically nonsingular ternary cubic
Hessian has a surviving 2x2 cofactor at one of three points
on a coordinate plane. This is the finite-points certificate
needed to exclude a rank-at-most-one coordinate hyperplane. -/
theorem integrable_ternaryTensor_surviving_plane_cofactor
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hregular : ∃ x y z : K,
      Matrix.det (fun i j : Fin 3 =>
        x * D 0 i j + y * D 1 i j + z * D 2 i j) ≠ 0) :
    (fun i j : Fin 3 => D 1 i j : Matrix (Fin 3) (Fin 3) K).adjugate ≠ 0 ∨
    (fun i j : Fin 3 => D 2 i j : Matrix (Fin 3) (Fin 3) K).adjugate ≠ 0 ∨
    ((fun i j : Fin 3 => D 1 i j : Matrix (Fin 3) (Fin 3) K) +
      (fun i j : Fin 3 => D 2 i j : Matrix (Fin 3) (Fin 3) K)).adjugate ≠ 0 := by
  classical
  let A : Matrix (Fin 3) (Fin 3) K := fun i j => D 1 i j
  let B : Matrix (Fin 3) (Fin 3) K := fun i j => D 2 i j
  by_cases hA : A.adjugate = 0
  · by_cases hB : B.adjugate = 0
    · by_cases hAB : (A + B).adjugate = 0
      · obtain ⟨x, y, z, hnon⟩ := hregular
        exact False.elim (hnon
          (integrable_ternaryTensor_det_zero_of_plane_cofactor_zero
            D hswap₁ hswap₂ hA hB hAB x y z))
      · exact Or.inr (Or.inr hAB)
    · exact Or.inr (Or.inl hB)
  · exact Or.inl hA

end
end HC4.Polynomial.RankThreeCubic
