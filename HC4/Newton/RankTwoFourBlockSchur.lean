import HC4.Newton.FirstSchurDeterminantOrder
import Mathlib.Tactic

/-!
# Rank-two 4x4 block and its binary Schur pivot

After choosing coordinates adapted to a rank-two leading symmetric block,
the four-dimensional matrix core may be written in the form

    [ a  0  p  q ]
    [ 0  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ].

Rather than introduce fractions, we use the denominator-cleared Schur
entries

    U = a*d*x - d*p^2 - a*r^2,
    V = a*d*y - d*p*q - a*r*s,
    W = a*d*z - d*q^2 - a*s^2.

A direct polynomial identity gives

    U*W - V^2 = (a*d) * det(H).

Thus, whenever the 4x4 determinant vanishes, the binary Schur block
`[U V; V W]` has zero determinant core. If that Schur block is nonzero,
Phase 90.1 immediately supplies the rank-one pivot certificate.

The explicit formula avoids any dependency on a general matrix Schur
complement API and is exactly the algebra needed for the rank-two
first-entry branch.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Coordinate data for a symmetric 4x4 block with a diagonal rank-two
leading block. -/
structure RankTwoFourBlock (K : Type*) where
  a : K
  d : K
  p : K
  q : K
  r : K
  s : K
  x : K
  y : K
  z : K

namespace RankTwoFourBlock

/-- Denominator-cleared `(1,1)` Schur entry. -/
def schurA (H : RankTwoFourBlock K) : K :=
  H.a * H.d * H.x - H.d * H.p * H.p - H.a * H.r * H.r

/-- Denominator-cleared off-diagonal Schur entry. -/
def schurB (H : RankTwoFourBlock K) : K :=
  H.a * H.d * H.y - H.d * H.p * H.q - H.a * H.r * H.s

/-- Denominator-cleared `(2,2)` Schur entry. -/
def schurC (H : RankTwoFourBlock K) : K :=
  H.a * H.d * H.z - H.d * H.q * H.q - H.a * H.s * H.s

/-- The denominator-cleared binary Schur block. -/
def schurBlock (H : RankTwoFourBlock K) : BinarySchurBlock K where
  a := H.schurA
  b := H.schurB
  c := H.schurC

/-- Explicit determinant of the adapted symmetric 4x4 block

    [ a  0  p  q ]
    [ 0  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ].

This is kept as a polynomial expression so that the core Schur identity is
proved entirely by commutative-ring normalisation. -/
def determinantCore (H : RankTwoFourBlock K) : K :=
  H.a * H.d * H.x * H.z
    - H.a * H.d * H.y * H.y
    - H.a * H.r * H.r * H.z
    + 2 * H.a * H.r * H.s * H.y
    - H.a * H.s * H.s * H.x
    - H.d * H.p * H.p * H.z
    + 2 * H.d * H.p * H.q * H.y
    - H.d * H.q * H.q * H.x
    + H.p * H.p * H.s * H.s
    - 2 * H.p * H.q * H.r * H.s
    + H.q * H.q * H.r * H.r

/-- **Cleared Schur determinant identity.**
The binary Schur determinant is the 4x4 determinant multiplied by the
determinant `a*d` of the leading rank-two block. -/
theorem schurBlock_detCore
    (H : RankTwoFourBlock K) :
    H.schurBlock.detCore =
      (H.a * H.d) * H.determinantCore := by
  unfold schurBlock schurA schurB schurC
    determinantCore BinarySchurBlock.detCore
  ring

/-- A vanishing adapted 4x4 determinant forces the denominator-cleared
binary Schur block to have zero determinant core. -/
theorem schurBlock_detCore_eq_zero_of_determinantCore_eq_zero
    (H : RankTwoFourBlock K)
    (hdet : H.determinantCore = 0) :
    H.schurBlock.detCore = 0 := by
  rw [H.schurBlock_detCore, hdet]
  simp

/-- If the Schur block is nonzero, a vanishing 4x4 determinant forces the
rank-one binary pivot certificate from Phase 90.1. -/
theorem schurPivot_of_determinantCore_eq_zero
    (H : RankTwoFourBlock K)
    (hnz : H.schurBlock.Nonzero)
    (hdet : H.determinantCore = 0) :
    H.schurBlock.LeftPivot ∨
      H.schurBlock.RightAxisPivot := by
  apply H.schurBlock.pivot_of_detCore_eq_zero
  · exact H.schurBlock_detCore_eq_zero_of_determinantCore_eq_zero hdet
  · exact hnz

end RankTwoFourBlock

/-- Packaged data for the rank-two branch: the leading two diagonal pivots
are nonzero and the first binary Schur block is nonzero. -/
structure RankTwoFourBlockEntry (K : Type*) [Field K] where
  block : RankTwoFourBlock K
  a_ne_zero : block.a ≠ 0
  d_ne_zero : block.d ≠ 0
  schur_nonzero : block.schurBlock.Nonzero

namespace RankTwoFourBlockEntry

/-- Determinant-zero in an adapted rank-two 4x4 entry yields the binary
rank-one pivot required by the corank-entry argument. -/
theorem schurPivot_of_determinantCore_eq_zero
    (E : RankTwoFourBlockEntry K)
    (hdet : E.block.determinantCore = 0) :
    E.block.schurBlock.LeftPivot ∨
      E.block.schurBlock.RightAxisPivot := by
  exact E.block.schurPivot_of_determinantCore_eq_zero
    E.schur_nonzero hdet

end RankTwoFourBlockEntry

end

end HC4.Newton
