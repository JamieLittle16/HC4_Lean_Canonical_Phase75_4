import HC4.Polynomial.RankThreeCubicDetOneSourceGenuinePolePrincipalSchurOrTriple
import HC4.Polynomial.RankThreeCubicDetOnePrincipalSchurSquareAlgebra
import Mathlib.Tactic

/-!
# Principal source-origin four-block chart (original coordinates)

The source's selected principal cofactor identifies the two transverse
coordinates other than k as an invertible principal block.
We place those two coordinates first, the longitudinal coordinate third,
and the kernel coordinate k last.

This is only a simultaneous reindexing of the original Hessian. It
does not change F and preserves the determinant exactly.

The principal chart packages those four Hessian rows/columns in the
existing GeneralFourBlock data, making the already verified cleared
Schur identities available at the source origin.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

/-- Order the two transverse coordinates complementary to k first,
then the longitudinal coordinate and finally the kernel coordinate.
This is a coordinate *reindexing*, not a source transformation. -/
noncomputable def principalSourceFourOrder
    (k : Fin 3) : Fin 4 ≃ (Unit ⊕ Fin 3) :=
  Equiv.ofBijective
    ![(Sum.inr (k.succAbove 0)),
      (Sum.inr (k.succAbove 1)),
      (Sum.inl ()),
      (Sum.inr k)]
    (by fin_cases k <;> decide)

/-- Underlying 4x4 symmetric chart on the original source Hessian. -/
noncomputable def principalSourceFourMatrix
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K)
    (k : Fin 3) : Matrix (Fin 4) (Fin 4) K :=
  B.submatrix (principalSourceFourOrder k) (principalSourceFourOrder k)

/-- GeneralFourBlock of the principal chart, with first two
coordinates the active transverse principal block. -/
noncomputable def principalSourceFourBlock
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K)
    (k : Fin 3) : GeneralFourBlock K :=
  GeneralFourBlock.ofSymmetricMatrix (principalSourceFourMatrix B k)

/-- The principal four-block chart preserves the full determinant
for symmetric matrices; in particular it preserves det Hess(F)=1. -/
theorem principalSourceFourBlock_determinantCore
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K)
    (hB : B.IsSymm)
    (k : Fin 3) :
    (principalSourceFourBlock B k).determinantCore = B.det := by
  let Q := principalSourceFourMatrix B k
  have hQ : ∀ i j : Fin 4, Q i j = Q j i := by
    intro i j
    exact hB.apply _ _
  have hM : (principalSourceFourBlock B k).matrix = Q :=
    GeneralFourBlock.matrix_ofSymmetricMatrix Q hQ
  calc
    (principalSourceFourBlock B k).determinantCore =
      (principalSourceFourBlock B k).matrix.det := by
        exact (GeneralFourBlock.matrix_det _).symm
    _ = Q.det := by rw [hM]
    _ = B.det := Matrix.det_submatrix_equiv_self
      (principalSourceFourOrder k) B

end
end HC4.Polynomial.RankThreeCubic
