import HC4.Newton.FirstSchurEntry
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# Determinant order at the first binary Schur entry

Suppose the three entries of a symmetric binary Schur block all acquire the
same first parameter factor `X^e`:

    A_e = X^e A,
    B_e = X^e B,
    C_e = X^e C.

Then

    A_e C_e - B_e^2 = (X^e)^2 (A C - B^2).

Because `Polynomial K` is a domain, vanishing of the full determinant
therefore forces the tail determinant `A C - B^2` to vanish. Evaluating the
tail at `X = 0` shows that the first coefficient block has determinant zero.

This is the determinant-order step required in the rank-two first-entry
branch. Combined with Phase 90.1, a nonzero first coefficient therefore
carries a rank-one binary pivot certificate.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Polynomial tails of the three entries in a symmetric binary Schur
family after a common first parameter power has been factored out. -/
structure BinarySchurTail (K : Type*) [Field K] where
  a : Polynomial K
  b : Polynomial K
  c : Polynomial K

namespace BinarySchurTail

/-- The binary block obtained by evaluating the tails at the first
parameter value `X = 0`. -/
def entryBlock (T : BinarySchurTail K) : BinarySchurBlock K where
  a := Polynomial.eval 0 T.a
  b := Polynomial.eval 0 T.b
  c := Polynomial.eval 0 T.c

/-- Determinant polynomial of the normalised tails. -/
def determinantTail (T : BinarySchurTail K) : Polynomial K :=
  T.a * T.c - T.b * T.b

/-- The common first parameter factor. -/
def firstFactor (e : ℕ) : Polynomial K :=
  Polynomial.X ^ e

/-- The first-factor-scaled `a` entry. -/
def scaledA (e : ℕ) (T : BinarySchurTail K) : Polynomial K :=
  firstFactor e * T.a

/-- The first-factor-scaled `b` entry. -/
def scaledB (e : ℕ) (T : BinarySchurTail K) : Polynomial K :=
  firstFactor e * T.b

/-- The first-factor-scaled `c` entry. -/
def scaledC (e : ℕ) (T : BinarySchurTail K) : Polynomial K :=
  firstFactor e * T.c

/-- Determinant of the scaled symmetric binary family. -/
def scaledDeterminant (e : ℕ) (T : BinarySchurTail K) : Polynomial K :=
  scaledA e T * scaledC e T - scaledB e T * scaledB e T

/-- Factoring the common first parameter order out of the determinant
produces its square. -/
theorem scaledDeterminant_eq
    (e : ℕ) (T : BinarySchurTail K) :
    T.scaledDeterminant e =
      (firstFactor e) ^ 2 * T.determinantTail := by
  unfold scaledDeterminant scaledA scaledB scaledC determinantTail
  ring

/-- The common first parameter factor is nonzero. -/
theorem firstFactor_ne_zero
    (e : ℕ) :
    (firstFactor e : Polynomial K) ≠ 0 := by
  unfold firstFactor
  exact pow_ne_zero e Polynomial.X_ne_zero

/-- Vanishing of the scaled determinant forces vanishing of the normalised
tail determinant. -/
theorem determinantTail_eq_zero_of_scaledDeterminant_eq_zero
    (e : ℕ) (T : BinarySchurTail K)
    (hdet : T.scaledDeterminant e = 0) :
    T.determinantTail = 0 := by
  rw [T.scaledDeterminant_eq e] at hdet
  have hfactor : ((firstFactor e : Polynomial K) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (firstFactor_ne_zero (K := K) e)
  exact (mul_eq_zero.mp hdet).resolve_left hfactor

/-- Evaluating a zero tail determinant at the first parameter value gives
zero determinant core for the first coefficient block. -/
theorem entryBlock_detCore_eq_zero_of_determinantTail_eq_zero
    (T : BinarySchurTail K)
    (hdet : T.determinantTail = 0) :
    T.entryBlock.detCore = 0 := by
  have hEval := congrArg (Polynomial.eval (0 : K)) hdet
  simpa [entryBlock, determinantTail, BinarySchurBlock.detCore] using hEval

/-- **First determinant-order certificate.**
If the determinant of the common-order-scaled Schur family vanishes, then
the first coefficient block has zero determinant core. -/
theorem entryBlock_detCore_eq_zero_of_scaledDeterminant_eq_zero
    (e : ℕ) (T : BinarySchurTail K)
    (hdet : T.scaledDeterminant e = 0) :
    T.entryBlock.detCore = 0 := by
  apply T.entryBlock_detCore_eq_zero_of_determinantTail_eq_zero
  exact T.determinantTail_eq_zero_of_scaledDeterminant_eq_zero e hdet

/-- If the first coefficient block is nonzero, determinant-order vanishing
forces the Phase 90.1 binary pivot. -/
theorem entryBlock_pivot_of_scaledDeterminant_eq_zero
    (e : ℕ) (T : BinarySchurTail K)
    (hnz : T.entryBlock.Nonzero)
    (hdet : T.scaledDeterminant e = 0) :
    T.entryBlock.LeftPivot ∨ T.entryBlock.RightAxisPivot := by
  apply T.entryBlock.pivot_of_detCore_eq_zero
  · exact T.entryBlock_detCore_eq_zero_of_scaledDeterminant_eq_zero e hdet
  · exact hnz

end BinarySchurTail

/-- Packaged first-order binary Schur-family data. -/
structure FirstBinarySchurFamilyEntry (K : Type*) [Field K] where
  order : ℕ
  tail : BinarySchurTail K
  entry_nonzero : tail.entryBlock.Nonzero

namespace FirstBinarySchurFamilyEntry

/-- The determinant of the represented first-order Schur family. -/
def determinant (E : FirstBinarySchurFamilyEntry K) : Polynomial K :=
  E.tail.scaledDeterminant E.order

/-- Vanishing determinant of the represented family forces a binary
rank-one pivot at its first nonzero entry. -/
theorem pivot_of_determinant_eq_zero
    (E : FirstBinarySchurFamilyEntry K)
    (hdet : E.determinant = 0) :
    E.tail.entryBlock.LeftPivot ∨
      E.tail.entryBlock.RightAxisPivot := by
  exact E.tail.entryBlock_pivot_of_scaledDeterminant_eq_zero
    E.order E.entry_nonzero hdet

end FirstBinarySchurFamilyEntry

end

end HC4.Newton
