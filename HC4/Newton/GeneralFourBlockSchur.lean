import HC4.Newton.RankTwoFourBlockSchur
import Mathlib.Tactic

/-!
# General denominator-cleared 2+2 Schur block

The earlier `RankTwoFourBlockSchur` module treats an already diagonal active
`2 x 2` block.  At the retained Smith frontier the active block need not be
diagonal, and forcing a diagonalisation before taking the Schur complement
would add an unnecessary coordinate-change interface.

This file keeps the full symmetric active block

    [ a  b ]
    [ b  d ]

and clears the Schur denominator by its determinant

    delta = a*d - b^2.

For the symmetric four-block

    [ a  b  p  q ]
    [ b  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ]

we define the cleared binary Schur entries `U,V,W` and prove the exact
polynomial identity

    U*W - V^2 = delta * det(H).

No inverse, localization, or field hypothesis is used: this is a commutative
ring identity.  It is therefore suitable for polynomial parameter series.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- A completely general symmetric `2+2` four-block. -/
structure GeneralFourBlock (R : Type*) where
  a : R
  b : R
  d : R
  p : R
  q : R
  r : R
  s : R
  x : R
  y : R
  z : R

namespace GeneralFourBlock

/-- Extensionality for the ten scalar entries of a general symmetric four-block. -/
@[ext]
theorem ext
    {H₁ H₂ : GeneralFourBlock R}
    (ha : H₁.a = H₂.a)
    (hb : H₁.b = H₂.b)
    (hd : H₁.d = H₂.d)
    (hp : H₁.p = H₂.p)
    (hq : H₁.q = H₂.q)
    (hr : H₁.r = H₂.r)
    (hs : H₁.s = H₂.s)
    (hx : H₁.x = H₂.x)
    (hy : H₁.y = H₂.y)
    (hz : H₁.z = H₂.z) :
    H₁ = H₂ := by
  cases H₁
  cases H₂
  simp_all

/-- The displayed symmetric `4 × 4` matrix represented by a general four-block. -/
def matrix (H : GeneralFourBlock R) : Matrix (Fin 4) (Fin 4) R :=
  !![H.a, H.b, H.p, H.q;
     H.b, H.d, H.r, H.s;
     H.p, H.r, H.x, H.y;
     H.q, H.s, H.y, H.z]

/-- Package the upper triangle of a symmetric `4 × 4` matrix as a four-block. -/
def ofSymmetricMatrix (M : Matrix (Fin 4) (Fin 4) R) : GeneralFourBlock R where
  a := M 0 0
  b := M 0 1
  d := M 1 1
  p := M 0 2
  q := M 0 3
  r := M 1 2
  s := M 1 3
  x := M 2 2
  y := M 2 3
  z := M 3 3

/-- Repacking a symmetric matrix and displaying it again recovers the matrix. -/
theorem matrix_ofSymmetricMatrix
    (M : Matrix (Fin 4) (Fin 4) R)
    (hsymm : ∀ i j, M i j = M j i) :
    (ofSymmetricMatrix M).matrix = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, ofSymmetricMatrix]
  all_goals exact hsymm _ _


/-- Determinant of the active `2 x 2` block. -/
def activeDet (H : GeneralFourBlock R) : R :=
  H.a * H.d - H.b * H.b

/-- Cleared `(1,1)` entry of the binary Schur complement. -/
def schurA (H : GeneralFourBlock R) : R :=
  H.activeDet * H.x -
    (H.d * H.p * H.p - 2 * H.b * H.p * H.r + H.a * H.r * H.r)

/-- Cleared off-diagonal entry of the binary Schur complement. -/
def schurB (H : GeneralFourBlock R) : R :=
  H.activeDet * H.y -
    (H.d * H.p * H.q - H.b * (H.p * H.s + H.q * H.r) + H.a * H.r * H.s)

/-- Cleared `(2,2)` entry of the binary Schur complement. -/
def schurC (H : GeneralFourBlock R) : R :=
  H.activeDet * H.z -
    (H.d * H.q * H.q - 2 * H.b * H.q * H.s + H.a * H.s * H.s)

/-- The denominator-cleared binary Schur block, retained as raw data.
The determinant identity below is stated separately over the ambient
commutative ring so that it applies when `R = Polynomial K`. -/
def schurBlock (H : GeneralFourBlock R) : BinarySchurBlock R where
  a := H.schurA
  b := H.schurB
  c := H.schurC

/-- Determinant core of the cleared binary Schur block, stated directly over
a commutative ring. -/
def schurDetCore (H : GeneralFourBlock R) : R :=
  H.schurA * H.schurC - H.schurB * H.schurB

/-- Explicit determinant of the general symmetric four-block. -/
def determinantCore (H : GeneralFourBlock R) : R :=
  H.a * H.d * H.x * H.z
    - H.a * H.d * H.y * H.y
    - H.a * H.r * H.r * H.z
    + 2 * H.a * H.r * H.s * H.y
    - H.a * H.s * H.s * H.x
    - H.b * H.b * H.x * H.z
    + H.b * H.b * H.y * H.y
    + 2 * H.b * H.p * H.r * H.z
    - 2 * H.b * H.p * H.s * H.y
    - 2 * H.b * H.q * H.r * H.y
    + 2 * H.b * H.q * H.s * H.x
    - H.d * H.p * H.p * H.z
    + 2 * H.d * H.p * H.q * H.y
    - H.d * H.q * H.q * H.x
    + H.p * H.p * H.s * H.s
    - 2 * H.p * H.q * H.r * H.s
    + H.q * H.q * H.r * H.r

/-- The explicit determinant core is exactly the determinant of the displayed
symmetric matrix.  This finite identity is the bridge that lets later code
transport an actual Hessian determinant through a ring equivalence without
re-expanding all twenty-four Leibniz terms. -/
theorem matrix_det (H : GeneralFourBlock R) :
    H.matrix.det = H.determinantCore := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [matrix, determinantCore, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- **General cleared Schur determinant identity.**

This is deliberately a `CommRing` theorem: the parameter-series application
takes `R = Polynomial K`, which is not a field. -/
theorem schurDetCore_eq_activeDet_mul_determinantCore
    (H : GeneralFourBlock R) :
    H.schurDetCore = H.activeDet * H.determinantCore := by
  unfold schurDetCore schurA schurB schurC activeDet determinantCore
  ring

/-- Vanishing of the full determinant forces vanishing of the cleared
binary Schur determinant, without any active-block invertibility hypothesis. -/
theorem schurDetCore_eq_zero_of_determinantCore_eq_zero
    (H : GeneralFourBlock R)
    (hdet : H.determinantCore = 0) :
    H.schurDetCore = 0 := by
  rw [H.schurDetCore_eq_activeDet_mul_determinantCore, hdet]
  simp

/-- Compatibility with the older field-valued `BinarySchurBlock.detCore`. -/
theorem schurBlock_detCore
    {F : Type*} [Field F]
    (H : GeneralFourBlock F) :
    H.schurBlock.detCore = H.activeDet * H.determinantCore := by
  simpa [schurBlock, schurDetCore, BinarySchurBlock.detCore] using
    H.schurDetCore_eq_activeDet_mul_determinantCore

end GeneralFourBlock

end

end HC4.Newton
