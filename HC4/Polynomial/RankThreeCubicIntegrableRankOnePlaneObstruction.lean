import HC4.Polynomial.RankThreeCubicIntegrableRankOnePencil
import Mathlib.Tactic

/-!
# A genuinely integrable rank-one linear Hessian pencil is singular

This removes the surviving-pivot assumption from the previous
rank-one pencil obstruction.

For a ternary cubic, write its Hessian as x*C + y*A + z*B.
Symmetry of third derivatives supplies the compatibility equations
between C, A and B. If A, B and A+B all have vanishing 2x2 minors,
then the determinant of the full pencil vanishes identically.

There are only two cases:
* A=0: integrability forces the middle column of the full Hessian
  to vanish.
* A!=0: its symmetric rank-one property produces a nonzero
  principal pivot. The pencil-rigidity and integrability lemmas
  force two full Hessian columns to be proportional.

This is a source-independent algebraic obstruction. To apply it
to an arbitrary source linear pole still requires transporting
that pole hyperplane into a coordinate plane, preserving the
symmetry-of-third-derivatives identities.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- A nonzero symmetric matrix satisfying every rank-one cross
identity has a nonzero principal diagonal entry, over a domain. -/
theorem symmetric_rankOne_nonzero_has_principal_pivot
    {R : Type*} [CommRing R] [IsDomain R]
    (A : Matrix (Fin 3) (Fin 3) R)
    (hSym : A.IsSymm)
    (hRank : ∀ k i j : Fin 3,
      A k k * A i j = A i k * A k j)
    (hA : A ≠ 0) :
    ∃ k : Fin 3, A k k ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hA
  ext i j
  have hminor := hRank i j j
  have hsq : A j i * A i j = 0 := by
    simpa only [h i, zero_mul] using hminor.symm
  rw [hSym.apply i j] at hsq
  rcases mul_eq_zero.mp hsq with hij | hij
  · exact hij
  · exact hij

/-- The full linear Hessian of an integrable symmetric cubic tensor
has determinant zero if its y-z pencil has rank <= 1 throughout.
The rank-one condition is stated by its exact cross-product
identities for the coefficient matrices A, B and A+B. -/
theorem integrable_ternaryHessian_det_zero_of_rankOne_plane
    {K : Type*} [Field K]
    (C A B : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
    (hAB : ∀ i : Fin 3, A i 2 = B i 1)
    (hCA : ∀ i : Fin 3, C i 1 = A i 0)
    (hCB : ∀ i : Fin 3, C i 2 = B i 0)
    (hA : ∀ k i j : Fin 3,
      A k k * A i j = A i k * A k j)
    (hB : ∀ k i j : Fin 3,
      B k k * B i j = B i k * B k j)
    (hABrank : ∀ k i j : Fin 3,
      (A + B) k k * (A + B) i j =
        (A + B) i k * (A + B) k j)
    (x y z : K) :
    (fun i j : Fin 3 => x * C i j + y * A i j + z * B i j).det = 0 := by
  classical
  by_cases ha0 : A = 0
  · let H : Matrix (Fin 3) (Fin 3) K :=
      fun i j => x * C i j + y * A i j + z * B i j
    have hB1 (i : Fin 3) : B i 1 = 0 := by
      rw [← hAB i, ha0]
      rfl
    have hC1 (i : Fin 3) : C i 1 = 0 := by
      rw [hCA i, ha0]
      rfl
    have hcol (i : Fin 3) : H i 1 = 0 := by
      dsimp [H]
      simp only [hC1 i, hB1 i, ha0, Matrix.zero_apply,
        mul_zero, add_zero]
    change H.det = 0
    rw [Matrix.det_fin_three, hcol 0, hcol 1, hcol 2]
    ring
  · obtain ⟨k, hak⟩ :=
      symmetric_rankOne_nonzero_has_principal_pivot A hA_symm hA ha0
    exact integrable_ternaryHessian_det_zero_of_rankOne_pencil_pivot
      C A B hA_symm hB_symm hAB hCA hCB k hak
      (hA k) (hB k) (hABrank k) x y z

end
end HC4.Polynomial.RankThreeCubic
