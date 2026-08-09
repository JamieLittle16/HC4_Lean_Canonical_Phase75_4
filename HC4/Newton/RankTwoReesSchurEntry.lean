import HC4.Newton.RankTwoFourBlockSchur
import HC4.Newton.FirstSchurDeterminantOrder
import Mathlib.Tactic

/-!
# Rank-two Rees Schur first entry

Phase 90.4 proved the cleared Schur identity for an adapted 4x4 block over
a field.  At the Rees stage the entries themselves are polynomials in the
parameter, so the same identity must be used over `Polynomial K`.

This file records that polynomial-valued version and connects it to the
first-order binary-tail machinery from Phase 90.3.

For a polynomial-valued adapted block, let the cleared Schur entries be
`U,V,W`.  Suppose their first common parameter order is explicitly
factored as

    U = X^e A,
    V = X^e B,
    W = X^e C,

and the evaluated tail block `(A(0),B(0),C(0))` is nonzero.

The 4x4 determinant identity gives `U*W - V^2 = 0` whenever the full
determinant vanishes.  The factorisation hypotheses identify this with the
`scaledDeterminant` of the `BinarySchurTail (A,B,C)`.  Phase 90.3 then
forces the first coefficient block to have zero determinant, and Phase
90.1 supplies the binary rank-one pivot.

This completes the algebraic enclosure of the rank-two first-entry branch:
once an adapted Rees block and its first common Schur order are supplied,
the pivot conclusion is automatic.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Polynomial/Rees-valued version of the adapted rank-two 4x4 block. -/
structure PolynomialRankTwoFourBlock (K : Type*) [Field K] where
  a : Polynomial K
  d : Polynomial K
  p : Polynomial K
  q : Polynomial K
  r : Polynomial K
  s : Polynomial K
  x : Polynomial K
  y : Polynomial K
  z : Polynomial K

namespace PolynomialRankTwoFourBlock

/-- Denominator-cleared `(1,1)` Schur entry over the Rees parameter. -/
def schurA (H : PolynomialRankTwoFourBlock K) : Polynomial K :=
  H.a * H.d * H.x - H.d * H.p * H.p - H.a * H.r * H.r

/-- Denominator-cleared off-diagonal Schur entry over the Rees parameter. -/
def schurB (H : PolynomialRankTwoFourBlock K) : Polynomial K :=
  H.a * H.d * H.y - H.d * H.p * H.q - H.a * H.r * H.s

/-- Denominator-cleared `(2,2)` Schur entry over the Rees parameter. -/
def schurC (H : PolynomialRankTwoFourBlock K) : Polynomial K :=
  H.a * H.d * H.z - H.d * H.q * H.q - H.a * H.s * H.s

/-- Determinant of the cleared binary Schur block. -/
def schurDeterminant
    (H : PolynomialRankTwoFourBlock K) : Polynomial K :=
  H.schurA * H.schurC - H.schurB * H.schurB

/-- Explicit determinant core of the adapted polynomial-valued 4x4 block. -/
def determinantCore
    (H : PolynomialRankTwoFourBlock K) : Polynomial K :=
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

/-- The cleared Schur determinant identity remains valid over the
polynomial/Rees coefficient ring. -/
theorem schurDeterminant_eq
    (H : PolynomialRankTwoFourBlock K) :
    H.schurDeterminant =
      (H.a * H.d) * H.determinantCore := by
  unfold schurDeterminant schurA schurB schurC determinantCore
  ring

/-- Vanishing of the polynomial 4x4 determinant forces vanishing of the
cleared polynomial Schur determinant. -/
theorem schurDeterminant_eq_zero_of_determinantCore_eq_zero
    (H : PolynomialRankTwoFourBlock K)
    (hdet : H.determinantCore = 0) :
    H.schurDeterminant = 0 := by
  rw [H.schurDeterminant_eq, hdet]
  simp

end PolynomialRankTwoFourBlock

/-- Data specifying the first common Schur order of an adapted polynomial
rank-two block. -/
structure RankTwoReesSchurEntry (K : Type*) [Field K] where
  block : PolynomialRankTwoFourBlock K
  order : ℕ
  tailA : Polynomial K
  tailB : Polynomial K
  tailC : Polynomial K
  schurA_factor :
    block.schurA =
      BinarySchurTail.firstFactor order * tailA
  schurB_factor :
    block.schurB =
      BinarySchurTail.firstFactor order * tailB
  schurC_factor :
    block.schurC =
      BinarySchurTail.firstFactor order * tailC
  entry_nonzero :
    (BinarySchurTail.mk tailA tailB tailC).entryBlock.Nonzero

namespace RankTwoReesSchurEntry

/-- The normalised binary Schur tail after removing the common first
parameter factor. -/
def tail (E : RankTwoReesSchurEntry K) : BinarySchurTail K where
  a := E.tailA
  b := E.tailB
  c := E.tailC

@[simp] theorem tail_a (E : RankTwoReesSchurEntry K) :
    E.tail.a = E.tailA := rfl

@[simp] theorem tail_b (E : RankTwoReesSchurEntry K) :
    E.tail.b = E.tailB := rfl

@[simp] theorem tail_c (E : RankTwoReesSchurEntry K) :
    E.tail.c = E.tailC := rfl

/-- The scaled determinant of the normalised tail is exactly the cleared
Schur determinant of the original polynomial 4x4 block. -/
theorem tail_scaledDeterminant_eq_schurDeterminant
    (E : RankTwoReesSchurEntry K) :
    E.tail.scaledDeterminant E.order =
      E.block.schurDeterminant := by
  unfold tail BinarySchurTail.scaledDeterminant
    BinarySchurTail.scaledA BinarySchurTail.scaledB
    BinarySchurTail.scaledC
  rw [← E.schurA_factor, ← E.schurB_factor, ← E.schurC_factor]
  rfl

/-- A vanishing polynomial 4x4 determinant therefore makes the scaled
binary tail determinant vanish. -/
theorem tail_scaledDeterminant_eq_zero_of_determinantCore_eq_zero
    (E : RankTwoReesSchurEntry K)
    (hdet : E.block.determinantCore = 0) :
    E.tail.scaledDeterminant E.order = 0 := by
  rw [E.tail_scaledDeterminant_eq_schurDeterminant]
  exact E.block.schurDeterminant_eq_zero_of_determinantCore_eq_zero hdet

/-- The nonzero hypothesis packaged in the entry data is exactly the
nonvanishing condition for the evaluated normalised tail. -/
theorem tail_entryBlock_nonzero
    (E : RankTwoReesSchurEntry K) :
    E.tail.entryBlock.Nonzero := by
  simpa [tail] using E.entry_nonzero

/-- **Rank-two Rees first-entry pivot.**
If the adapted polynomial 4x4 determinant vanishes and the factored first
Schur coefficient is nonzero, then its evaluated first coefficient carries
the binary rank-one pivot certificate. -/
theorem firstEntryPivot_of_determinantCore_eq_zero
    (E : RankTwoReesSchurEntry K)
    (hdet : E.block.determinantCore = 0) :
    E.tail.entryBlock.LeftPivot ∨
      E.tail.entryBlock.RightAxisPivot := by
  apply E.tail.entryBlock_pivot_of_scaledDeterminant_eq_zero E.order
  · exact E.tail_entryBlock_nonzero
  · exact
      E.tail_scaledDeterminant_eq_zero_of_determinantCore_eq_zero hdet

end RankTwoReesSchurEntry

end

end HC4.Newton
