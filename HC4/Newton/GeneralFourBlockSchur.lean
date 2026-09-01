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

/-- Map all ten entries of a general four-block through a ring homomorphism.
This is the canonical representation bridge between source-first and
parameter-first coefficient rings. -/
def map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) : GeneralFourBlock S where
  a := f H.a
  b := f H.b
  d := f H.d
  p := f H.p
  q := f H.q
  r := f H.r
  s := f H.s
  x := f H.x
  y := f H.y
  z := f H.z

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

@[simp]
theorem activeDet_map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) :
    (H.map f).activeDet = f H.activeDet := by
  simp [map, activeDet]

@[simp]
theorem schurA_map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) :
    (H.map f).schurA = f H.schurA := by
  simp [map, schurA, activeDet]

@[simp]
theorem schurB_map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) :
    (H.map f).schurB = f H.schurB := by
  simp [map, schurB, activeDet]

@[simp]
theorem schurC_map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) :
    (H.map f).schurC = f H.schurC := by
  simp [map, schurC, activeDet]

@[simp]
theorem schurDetCore_map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) :
    (H.map f).schurDetCore = f H.schurDetCore := by
  simp [schurDetCore]

@[simp]
theorem determinantCore_map {S : Type*} [CommRing S]
    (H : GeneralFourBlock R) (f : R →+* S) :
    (H.map f).determinantCore = f H.determinantCore := by
  simp [map, determinantCore]

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

/-- Congruence scaling of the four underlying directions.  This is the raw
algebraic operation used when an ordinary Hessian is replaced by its
Euler-scaled Hessian: each matrix entry is multiplied by the scale on its row
and on its column. -/
def diagonalScale (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    GeneralFourBlock R where
  a := s0 * s0 * H.a
  b := s0 * s1 * H.b
  d := s1 * s1 * H.d
  p := s0 * t0 * H.p
  q := s0 * t1 * H.q
  r := s1 * t0 * H.r
  s := s1 * t1 * H.s
  x := t0 * t0 * H.x
  y := t0 * t1 * H.y
  z := t1 * t1 * H.z

@[simp]
theorem activeDet_diagonalScale
    (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    (H.diagonalScale s0 s1 t0 t1).activeDet =
      (s0 * s1) ^ 2 * H.activeDet := by
  unfold diagonalScale activeDet
  ring

@[simp]
theorem schurA_diagonalScale
    (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    (H.diagonalScale s0 s1 t0 t1).schurA =
      (s0 * s1) ^ 2 * t0 ^ 2 * H.schurA := by
  unfold diagonalScale schurA activeDet
  ring

@[simp]
theorem schurB_diagonalScale
    (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    (H.diagonalScale s0 s1 t0 t1).schurB =
      (s0 * s1) ^ 2 * t0 * t1 * H.schurB := by
  unfold diagonalScale schurB activeDet
  ring

@[simp]
theorem schurC_diagonalScale
    (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    (H.diagonalScale s0 s1 t0 t1).schurC =
      (s0 * s1) ^ 2 * t1 ^ 2 * H.schurC := by
  unfold diagonalScale schurC activeDet
  ring

/-- The cleared Schur determinant transforms by the square of the determinant
of the diagonal change on the active pair and the square of the determinant
of the diagonal change on the complementary pair. -/
@[simp]
theorem schurDetCore_diagonalScale
    (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    (H.diagonalScale s0 s1 t0 t1).schurDetCore =
      (s0 * s1) ^ 4 * (t0 * t1) ^ 2 * H.schurDetCore := by
  unfold schurDetCore
  rw [schurA_diagonalScale, schurB_diagonalScale, schurC_diagonalScale]
  ring

/-- Replace the second complementary direction by

`lam * v + mu * u + alpha * e₀ + beta * e₁`,

where `e₀,e₁` are the active directions and `u,v` are the two complementary
directions.  The formula is the corresponding symmetric congruence written in
the ten scalar entries. -/
def shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) : GeneralFourBlock R where
  a := H.a
  b := H.b
  d := H.d
  p := H.p
  q := lam * H.q + mu * H.p + alpha * H.a + beta * H.b
  r := H.r
  s := lam * H.s + mu * H.r + alpha * H.b + beta * H.d
  x := H.x
  y := lam * H.y + mu * H.x + alpha * H.p + beta * H.r
  z := lam ^ 2 * H.z + mu ^ 2 * H.x + alpha ^ 2 * H.a + beta ^ 2 * H.d +
    2 * lam * mu * H.y + 2 * lam * alpha * H.q + 2 * lam * beta * H.s +
    2 * mu * alpha * H.p + 2 * mu * beta * H.r + 2 * alpha * beta * H.b

@[simp]
theorem activeDet_shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) :
    (H.shearSecondComplement lam mu alpha beta).activeDet = H.activeDet := by
  rfl

/-- Active-span additions disappear after taking the Schur quotient; only the
components in the two-dimensional complementary quotient remain. -/
@[simp]
theorem schurA_shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) :
    (H.shearSecondComplement lam mu alpha beta).schurA = H.schurA := by
  unfold shearSecondComplement schurA activeDet
  ring

@[simp]
theorem schurB_shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) :
    (H.shearSecondComplement lam mu alpha beta).schurB =
      lam * H.schurB + mu * H.schurA := by
  unfold shearSecondComplement schurA schurB activeDet
  ring

@[simp]
theorem schurC_shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) :
    (H.shearSecondComplement lam mu alpha beta).schurC =
      lam ^ 2 * H.schurC + 2 * lam * mu * H.schurB + mu ^ 2 * H.schurA := by
  unfold shearSecondComplement schurA schurB schurC activeDet
  ring

/-- Consequently the cleared Schur determinant is insensitive to active-span
shears and to adding the first complementary direction, and scales only by the
square of the genuine second-quotient component. -/
@[simp]
theorem schurDetCore_shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) :
    (H.shearSecondComplement lam mu alpha beta).schurDetCore =
      lam ^ 2 * H.schurDetCore := by
  unfold schurDetCore
  rw [schurA_shearSecondComplement, schurB_shearSecondComplement,
    schurC_shearSecondComplement]
  ring

end GeneralFourBlock

end

end HC4.Newton