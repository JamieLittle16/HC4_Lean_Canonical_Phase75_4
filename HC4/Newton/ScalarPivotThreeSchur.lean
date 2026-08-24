import HC4.Newton.GeneralFourBlock
import Mathlib.Tactic

/-!
# A18.4.92: cleared scalar-pivot three-by-three Schur block

Let

    H = [[a,b,p,q],
         [b,d,r,s],
         [p,r,x,y],
         [q,s,y,z]]

be a symmetric four-block.  Clearing the denominator of the Schur complement
of the scalar pivot `a` gives the symmetric `3 x 3` block

    S = a * D - v v^T.

Its determinant satisfies the exact polynomial identity

    det S = a^2 * det H.

This is the rank-one analogue of the already-used active-`2 x 2` Schur
identity.  It is purely commutative algebra and is valid over an arbitrary
commutative ring.
-/

namespace HC4.Newton

noncomputable section

universe u
variable {R : Type u} [CommRing R]

namespace GeneralFourBlock

/-- `(1,1)` entry of the cleared scalar-pivot Schur block. -/
def scalarSchur11 (H : GeneralFourBlock R) : R :=
  H.a * H.d - H.b * H.b

/-- `(1,2)` entry of the cleared scalar-pivot Schur block. -/
def scalarSchur12 (H : GeneralFourBlock R) : R :=
  H.a * H.r - H.b * H.p

/-- `(1,3)` entry of the cleared scalar-pivot Schur block. -/
def scalarSchur13 (H : GeneralFourBlock R) : R :=
  H.a * H.s - H.b * H.q

/-- `(2,2)` entry of the cleared scalar-pivot Schur block. -/
def scalarSchur22 (H : GeneralFourBlock R) : R :=
  H.a * H.x - H.p * H.p

/-- `(2,3)` entry of the cleared scalar-pivot Schur block. -/
def scalarSchur23 (H : GeneralFourBlock R) : R :=
  H.a * H.y - H.p * H.q

/-- `(3,3)` entry of the cleared scalar-pivot Schur block. -/
def scalarSchur33 (H : GeneralFourBlock R) : R :=
  H.a * H.z - H.q * H.q

/-- The complete symmetric cleared `1+3` Schur block. -/
noncomputable def scalarSchurThreeMatrix
    (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![H.scalarSchur11, H.scalarSchur12, H.scalarSchur13;
     H.scalarSchur12, H.scalarSchur22, H.scalarSchur23;
     H.scalarSchur13, H.scalarSchur23, H.scalarSchur33]

/-- The scalar-pivot Schur block is symmetric. -/
theorem scalarSchurThreeMatrix_symmetric
    (H : GeneralFourBlock R) :
    H.scalarSchurThreeMatrix.IsSymm := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    rfl

/-- **Cleared scalar Schur determinant identity.** -/
theorem scalarSchurThreeMatrix_det
    (H : GeneralFourBlock R) :
    H.scalarSchurThreeMatrix.det = H.a ^ 2 * H.determinantCore := by
  simp [scalarSchurThreeMatrix, scalarSchur11, scalarSchur12, scalarSchur13,
    scalarSchur22, scalarSchur23, scalarSchur33,
    Matrix.det_fin_three, GeneralFourBlock.determinantCore]
  ring

/-- If all `2 x 2` minors of the four-block vanish, every entry of the
scalar-pivot Schur block vanishes. -/
theorem scalarSchurThreeMatrix_eq_zero_of_allTwoByTwoMinorsZero
    (H : GeneralFourBlock R)
    (hall : H.AllTwoByTwoMinorsZero) :
    H.scalarSchurThreeMatrix = 0 := by
  have h11 := hall (0 : Fin 4) 0 1 1
  have h12 := hall (0 : Fin 4) 0 1 2
  have h13 := hall (0 : Fin 4) 0 1 3
  have h22 := hall (0 : Fin 4) 0 2 2
  have h23 := hall (0 : Fin 4) 0 2 3
  have h33 := hall (0 : Fin 4) 0 3 3
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarSchurThreeMatrix, scalarSchur11, scalarSchur12, scalarSchur13,
      scalarSchur22, scalarSchur23, scalarSchur33,
      GeneralFourBlock.matrix] at h11 h12 h13 h22 h23 h33 ⊢ <;>
    assumption

end GeneralFourBlock

end

end HC4.Newton
