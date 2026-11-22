import HC4.Polynomial.RankThreeCubicSymmetricRankOnePencil
import Mathlib.Tactic

/-!
# Integrability turns a proportional pair of cubic Hessian slices
# into a singular full three-variable Hessian

Write the linear transverse Hessian of a homogeneous ternary cubic
as H(x,y,z) = x*C + y*A + z*B. Full third-derivative symmetry
implies the three compatibility equations
    A(_,2) = B(_,1)
    C(_,1) = A(_,0)
    C(_,2) = B(_,0).

If B is a scalar multiple of A, these equations force the
second and third columns of H to be proportional for every x,y,z.
Consequently det(H) is identically zero.

This is the integrability obstruction which a *rank-one pencil*
must confront. It uses genuine symmetry of source third derivatives,
not just symmetry of individual Hessian matrices.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- A rank-one-direction pencil in the y-z plane, compatible with
a symmetric cubic third-derivative tensor, forces the full ternary
linear Hessian to have determinant zero. -/
theorem integrable_ternaryHessian_det_zero_of_proportional_slices
    {R : Type*} [CommRing R]
    (C A B : Matrix (Fin 3) (Fin 3) R)
    (hAB : ∀ i : Fin 3, A i 2 = B i 1)
    (hCA : ∀ i : Fin 3, C i 1 = A i 0)
    (hCB : ∀ i : Fin 3, C i 2 = B i 0)
    (scale : R)
    (hB : ∀ i j : Fin 3, B i j = scale * A i j)
    (x y z : R) :
    ((fun i j : Fin 3 => x * C i j + y * A i j + z * B i j) : Matrix (Fin 3) (Fin 3) R).det = 0 := by
  classical
  let H : Matrix (Fin 3) (Fin 3) R :=
    fun i j => x * C i j + y * A i j + z * B i j
  have hAcol (i : Fin 3) : A i 2 = scale * A i 1 := by
    rw [hAB i]
    exact hB i 1
  have hCcol (i : Fin 3) : C i 2 = scale * C i 1 := by
    rw [hCB i, hB i 0, hCA i]
  have hBcol (i : Fin 3) : B i 2 = scale * B i 1 := by
    rw [hB i 2, hB i 1, hAcol i]
    ring
  have hcol (i : Fin 3) : H i 2 = scale * H i 1 := by
    dsimp [H]
    rw [hCcol i, hAcol i, hBcol i]
    ring
  change H.det = 0
  rw [Matrix.det_fin_three, hcol 0, hcol 1, hcol 2]
  ring

/-- Source integrability plus rank-one cross-product identities on
two transverse Hessian slices and their sum excludes a generically
nonsingular full ternary Hessian, whenever one principal slice pivot
survives. No coordinate change or extra source hypothesis is hidden. -/
theorem integrable_ternaryHessian_det_zero_of_rankOne_pencil_pivot
    {K : Type*} [Field K]
    (C A B : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
    (hAB : ∀ i : Fin 3, A i 2 = B i 1)
    (hCA : ∀ i : Fin 3, C i 1 = A i 0)
    (hCB : ∀ i : Fin 3, C i 2 = B i 0)
    (k : Fin 3)
    (hak : A k k ≠ 0)
    (hA : ∀ i j : Fin 3,
      A k k * A i j = A i k * A k j)
    (hB : ∀ i j : Fin 3,
      B k k * B i j = B i k * B k j)
    (hABrank : ∀ i j : Fin 3,
      (A + B) k k * (A + B) i j =
        (A + B) i k * (A + B) k j)
    (x y z : K) :
    ((fun i j : Fin 3 => x * C i j + y * A i j + z * B i j) : Matrix (Fin 3) (Fin 3) R).det = 0 := by
  classical
  have hprop :=
    symmetric_rankOne_pencil_proportional
      A B hA_symm hB_symm k hak hA hB hABrank
  let scale : K := B k k / A k k
  have hscalar (i j : Fin 3) : B i j = scale * A i j := by
    apply mul_left_cancel₀ hak
    calc
      A k k * B i j = B k k * A i j := hprop i j
      _ = A k k * (scale * A i j) := by
        dsimp [scale]
        field_simp [hak]
        ring
  exact integrable_ternaryHessian_det_zero_of_proportional_slices
    C A B hAB hCA hCB scale hscalar x y z

end
end HC4.Polynomial.RankThreeCubic
