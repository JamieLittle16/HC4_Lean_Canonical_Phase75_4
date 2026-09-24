import HC4.Newton.ZeroSchurFirstEntryClock
import HC4.Newton.ZeroThreeSchurFirstEntryClock
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Cleared 1+2 Schur quotient of a symmetric 3x3 polynomial matrix

This is the second finite Schur step used after the 1+3 quotient of a
rank-one four-dimensional special fibre.

For a symmetric 3x3 matrix

    [ a b c ]
    [ b d e ]
    [ c e f ]

the denominator-cleared binary Schur quotient at pivot a is

    [ ad-b^2   ae-bc ]
    [ ae-bc    af-c^2 ]

and its determinant is

    a * det(M).

The same identity is recorded for pivots d and f.  The resulting binary
series is exactly the `BinarySchurPolynomialSeries` already consumed by the
green zero-Schur first-entry machinery.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

/-- Pointwise form of matrix symmetry, derived directly from the defining
transpose equality so this file is independent of the pointwise API name. -/
private theorem symmEntry
    {n α : Type*}
    {M : Matrix n n α}
    (h : M.IsSymm)
    (i j : n) :
    M i j = M j i := by
  have h' := congrArg (fun N : Matrix n n α => N j i) h
  simpa using h'

/-- Cleared binary quotient of a symmetric 3x3 series using coordinate 0 as
scalar pivot. -/
def threePivot0BinarySchurSeries
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := M 0 0 * M 1 1 - M 0 1 * M 0 1
  offDiag := M 0 0 * M 1 2 - M 0 1 * M 0 2
  kernel := M 0 0 * M 2 2 - M 0 2 * M 0 2

/-- Coordinate-1 pivot, retaining coordinates 0 and 2. -/
def threePivot1BinarySchurSeries
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := M 1 1 * M 0 0 - M 0 1 * M 0 1
  offDiag := M 1 1 * M 0 2 - M 0 1 * M 1 2
  kernel := M 1 1 * M 2 2 - M 1 2 * M 1 2

/-- Coordinate-2 pivot, retaining coordinates 0 and 1. -/
def threePivot2BinarySchurSeries
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := M 2 2 * M 0 0 - M 0 2 * M 0 2
  offDiag := M 2 2 * M 0 1 - M 0 2 * M 1 2
  kernel := M 2 2 * M 1 1 - M 1 2 * M 1 2

/-- Exact determinant identity for the coordinate-0 pivot. -/
theorem threePivot0BinarySchurSeries_determinant
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsymm : M.IsSymm) :
    (threePivot0BinarySchurSeries M).determinant =
      M 0 0 * M.det := by
  have h10 : M 1 0 = M 0 1 := symmEntry hsymm 1 0
  have h20 : M 2 0 = M 0 2 := symmEntry hsymm 2 0
  have h21 : M 2 1 = M 1 2 := symmEntry hsymm 2 1
  simp [threePivot0BinarySchurSeries,
    BinarySchurPolynomialSeries.determinant, Matrix.det_fin_three,
    h10, h20, h21]
  ring

/-- Exact determinant identity for the coordinate-1 pivot. -/
theorem threePivot1BinarySchurSeries_determinant
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsymm : M.IsSymm) :
    (threePivot1BinarySchurSeries M).determinant =
      M 1 1 * M.det := by
  have h10 : M 1 0 = M 0 1 := symmEntry hsymm 1 0
  have h20 : M 2 0 = M 0 2 := symmEntry hsymm 2 0
  have h21 : M 2 1 = M 1 2 := symmEntry hsymm 2 1
  simp [threePivot1BinarySchurSeries,
    BinarySchurPolynomialSeries.determinant, Matrix.det_fin_three,
    h10, h20, h21]
  ring

/-- Exact determinant identity for the coordinate-2 pivot. -/
theorem threePivot2BinarySchurSeries_determinant
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsymm : M.IsSymm) :
    (threePivot2BinarySchurSeries M).determinant =
      M 2 2 * M.det := by
  have h10 : M 1 0 = M 0 1 := symmEntry hsymm 1 0
  have h20 : M 2 0 = M 0 2 := symmEntry hsymm 2 0
  have h21 : M 2 1 = M 1 2 := symmEntry hsymm 2 1
  simp [threePivot2BinarySchurSeries,
    BinarySchurPolynomialSeries.determinant, Matrix.det_fin_three,
    h10, h20, h21]
  ring


/-! ## Rank-one 3x3 tail to an exact binary zero-Schur clock -/

namespace ZeroThreeSchurSeries

variable [IsDomain R]

/-- Entrywise division by the common first power preserves symmetry. -/
theorem tailMatrix_isSymm
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (hsymm : S.matrix.IsSymm) :
    (S.tailMatrix h).IsSymm := by
  apply Matrix.ext
  intro i j
  have hij := S.entry_eq_firstFactor_mul_tail h i j
  have hji := S.entry_eq_firstFactor_mul_tail h j i
  have hs : S.matrix j i = S.matrix i j :=
    symmEntry hsymm j i
  have hmul :
      Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailMatrix h j i =
        Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailMatrix h i j := by
    rw [← hji, ← hij]
    exact hs
  exact mul_left_cancel₀
    (pow_ne_zero _ Polynomial.X_ne_zero) hmul

end ZeroThreeSchurSeries

namespace ExactZeroThreeSchurClock

variable [IsDomain R]

/-- Symmetry of the normalised first-entry tail matrix. -/
theorem tailMatrix_isSymm
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm) :
    (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).IsSymm :=
  E.zeroSeries.tailMatrix_isSymm E.hasPositiveEntryLayer hsymm

/-- Hence the constant coefficient matrix of the tail is symmetric. -/
theorem tailConstantMatrix_isSymm
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm) :
    E.tailConstantMatrix.IsSymm := by
  intro i j
  exact congrArg
    (fun p : Polynomial R => p.coeff 0)
    (E.tailMatrix_isSymm symmEntry hsymm i j)

/-- A nonzero symmetric 3x3 matrix with all 2x2 minors zero has a nonzero
diagonal entry.  This is the scalar pivot needed for the second Schur step. -/
theorem exists_diagonal_ne_zero_of_rankOne
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hall : AllTwoByTwoMinorsZero E.tailConstantMatrix)
    (hne : E.tailConstantMatrix ≠ 0) :
    ∃ p : Fin 3, E.tailConstantMatrix p p ≠ 0 := by
  let C := E.tailConstantMatrix
  have hCsymm : C.IsSymm := E.tailConstantMatrix_isSymm hsymm
  by_contra hnot
  push_neg at hnot
  apply hne
  ext i j
  by_cases hij : i = j
  · subst j
    exact hnot i
  · have hm := hall i i j j
    have hprod : C i j * C j i = 0 := by
      simpa [C, hnot i, hnot j] using hm
    rcases mul_eq_zero.mp hprod with hz | hz
    · exact hz
    · have hs := symmEntry hCsymm j i
      rw [hs] at hz
      exact hz

private noncomputable def toBinaryClockPivot0
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hall : AllTwoByTwoMinorsZero E.tailConstantMatrix)
    (hpivot : E.tailConstantMatrix 0 0 ≠ 0) :
    ExactZeroSchurClock R := by
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hM : M.IsSymm := E.tailMatrix_isSymm hsymm
  have hC : E.tailConstantMatrix.IsSymm :=
    E.tailConstantMatrix_isSymm hsymm
  refine {
    zeroSeries := {
      series := threePivot0BinarySchurSeries M
      active_coeff_zero := ?_
      offDiag_coeff_zero := ?_
      kernel_coeff_zero := ?_
    }
    clearingFactor := M 0 0 * E.clearingFactor
    defect := E.residualDefect
    clearingFactor_coeff_zero_ne_zero := ?_
    determinantFactor := ?_
  }
  · have hm := hall 0 0 1 1
    have hs := symmEntry hC 1 0
    simpa [threePivot0BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs] using hm
  · have hm := hall 0 0 1 2
    have hs := symmEntry hC 1 0
    simpa [threePivot0BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs,
      mul_comm] using hm
  · have hm := hall 0 0 2 2
    have hs := symmEntry hC 2 0
    simpa [threePivot0BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs] using hm
  · have hp :
        (M 0 0).coeff 0 ≠ 0 := by
      simpa [M, tailConstantMatrix] using hpivot
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      mul_ne_zero hp E.clearingFactor_coeff_zero_ne_zero
  · rw [threePivot0BinarySchurSeries_determinant M hM]
    rw [E.tail_determinantFactor]
    ring

private noncomputable def toBinaryClockPivot1
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hall : AllTwoByTwoMinorsZero E.tailConstantMatrix)
    (hpivot : E.tailConstantMatrix 1 1 ≠ 0) :
    ExactZeroSchurClock R := by
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hM : M.IsSymm := E.tailMatrix_isSymm hsymm
  have hC : E.tailConstantMatrix.IsSymm :=
    E.tailConstantMatrix_isSymm hsymm
  refine {
    zeroSeries := {
      series := threePivot1BinarySchurSeries M
      active_coeff_zero := ?_
      offDiag_coeff_zero := ?_
      kernel_coeff_zero := ?_
    }
    clearingFactor := M 1 1 * E.clearingFactor
    defect := E.residualDefect
    clearingFactor_coeff_zero_ne_zero := ?_
    determinantFactor := ?_
  }
  · have hm := hall 1 1 0 0
    have hs := symmEntry hC 0 1
    simpa [threePivot1BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs] using hm
  · have hm := hall 1 1 0 2
    have hs := symmEntry hC 0 1
    simpa [threePivot1BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs,
      mul_comm] using hm
  · have hm := hall 1 1 2 2
    have hs := symmEntry hC 2 1
    simpa [threePivot1BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs] using hm
  · have hp :
        (M 1 1).coeff 0 ≠ 0 := by
      simpa [M, tailConstantMatrix] using hpivot
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      mul_ne_zero hp E.clearingFactor_coeff_zero_ne_zero
  · rw [threePivot1BinarySchurSeries_determinant M hM]
    rw [E.tail_determinantFactor]
    ring

private noncomputable def toBinaryClockPivot2
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hall : AllTwoByTwoMinorsZero E.tailConstantMatrix)
    (hpivot : E.tailConstantMatrix 2 2 ≠ 0) :
    ExactZeroSchurClock R := by
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hM : M.IsSymm := E.tailMatrix_isSymm hsymm
  have hC : E.tailConstantMatrix.IsSymm :=
    E.tailConstantMatrix_isSymm hsymm
  refine {
    zeroSeries := {
      series := threePivot2BinarySchurSeries M
      active_coeff_zero := ?_
      offDiag_coeff_zero := ?_
      kernel_coeff_zero := ?_
    }
    clearingFactor := M 2 2 * E.clearingFactor
    defect := E.residualDefect
    clearingFactor_coeff_zero_ne_zero := ?_
    determinantFactor := ?_
  }
  · have hm := hall 2 2 0 0
    have hs := symmEntry hC 0 2
    simpa [threePivot2BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs] using hm
  · have hm := hall 2 2 0 1
    have hs0 := symmEntry hC 0 2
    have hs1 := symmEntry hC 1 2
    simpa [threePivot2BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs0, hs1,
      mul_comm] using hm
  · have hm := hall 2 2 1 1
    have hs := symmEntry hC 1 2
    simpa [threePivot2BinarySchurSeries, M,
      tailConstantMatrix, Polynomial.coeff_zero_eq_eval_zero, hs] using hm
  · have hp :
        (M 2 2).coeff 0 ≠ 0 := by
      simpa [M, tailConstantMatrix] using hpivot
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      mul_ne_zero hp E.clearingFactor_coeff_zero_ne_zero
  · rw [threePivot2BinarySchurSeries_determinant M hM]
    rw [E.tail_determinantFactor]
    ring

/-- **Second finite Schur step.**

If the first normalised 3x3 coefficient block is rank one, symmetry supplies
a nonzero scalar diagonal pivot.  Its cleared 1+2 Schur quotient is an exact
zero-constant binary clock with precisely the residual 3x3 determinant
order. -/
noncomputable def toBinaryZeroSchurClock_of_rankOne
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hall : AllTwoByTwoMinorsZero E.tailConstantMatrix)
    (hne : E.tailConstantMatrix ≠ 0) :
    ExactZeroSchurClock R := by
  by_cases h0 : E.tailConstantMatrix 0 0 ≠ 0
  · exact E.toBinaryClockPivot0 hsymm hall h0
  · by_cases h1 : E.tailConstantMatrix 1 1 ≠ 0
    · exact E.toBinaryClockPivot1 hsymm hall h1
    · have h2 : E.tailConstantMatrix 2 2 ≠ 0 := by
        rcases E.exists_diagonal_ne_zero_of_rankOne hsymm hall hne with
          ⟨p, hp⟩
        fin_cases p
        · exact (h0 hp).elim
        · exact (h1 hp).elim
        · exact hp
      exact E.toBinaryClockPivot2 hsymm hall h2


/-! ## Singular rank-two 3x3 tail has a principal pivot -/

/-- In a symmetric singular 3x3 matrix over a domain, the existence of any
nonzero 2x2 minor forces one of the three coordinate-principal 2x2 minors to
be nonzero.

The proof is division-free.  If all three principal minors vanish, the
identities

    (a*e-b*c)^2 + a*det(M) = (a*d-b^2)(a*f-c^2),
    (b*e-c*d)^2 + d*det(M) = (a*d-b^2)(d*f-e^2),
    (b*f-c*e)^2 + f*det(M) = (a*f-c^2)(d*f-e^2)

kill the three cross minors as well.  Symmetry then kills every 2x2 minor,
contradicting the retained rank-two witness. -/
theorem exists_principalTwoByTwoMinor_ne_zero_of_symmetric_singular
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hdet : E.tailConstantMatrix.det = 0)
    (hminor : HasTwoByTwoMinor E.tailConstantMatrix) :
    (E.tailConstantMatrix 0 0 * E.tailConstantMatrix 1 1 -
        E.tailConstantMatrix 0 1 * E.tailConstantMatrix 1 0 ≠ 0) ∨
      (E.tailConstantMatrix 0 0 * E.tailConstantMatrix 2 2 -
        E.tailConstantMatrix 0 2 * E.tailConstantMatrix 2 0 ≠ 0) ∨
      (E.tailConstantMatrix 1 1 * E.tailConstantMatrix 2 2 -
        E.tailConstantMatrix 1 2 * E.tailConstantMatrix 2 1 ≠ 0) := by
  let M := E.tailConstantMatrix
  have hM : M.IsSymm := E.tailConstantMatrix_isSymm hsymm
  have h01sym : M 1 0 = M 0 1 := symmEntry hM 1 0
  have h02sym : M 2 0 = M 0 2 := symmEntry hM 2 0
  have h12sym : M 2 1 = M 1 2 := symmEntry hM 2 1

  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨hp01, hp02, hp12⟩

  have hp01' : M 0 0 * M 1 1 - M 0 1 * M 0 1 = 0 := by
    simpa [M, h01sym] using hp01
  have hp02' : M 0 0 * M 2 2 - M 0 2 * M 0 2 = 0 := by
    simpa [M, h02sym] using hp02
  have hp12' : M 1 1 * M 2 2 - M 1 2 * M 1 2 = 0 := by
    simpa [M, h12sym] using hp12

  have hdet' :
      M 0 0 * M 1 1 * M 2 2 +
          2 * M 0 1 * M 0 2 * M 1 2 -
          M 0 0 * M 1 2 * M 1 2 -
          M 1 1 * M 0 2 * M 0 2 -
          M 2 2 * M 0 1 * M 0 1 = 0 := by
    simpa [M, Matrix.det_fin_three, h01sym, h02sym, h12sym] using hdet

  have hcross0sq :
      (M 0 0 * M 1 2 - M 0 1 * M 0 2) *
          (M 0 0 * M 1 2 - M 0 1 * M 0 2) = 0 := by
    have hid :
        (M 0 0 * M 1 2 - M 0 1 * M 0 2) *
              (M 0 0 * M 1 2 - M 0 1 * M 0 2) +
            M 0 0 *
              (M 0 0 * M 1 1 * M 2 2 +
                2 * M 0 1 * M 0 2 * M 1 2 -
                M 0 0 * M 1 2 * M 1 2 -
                M 1 1 * M 0 2 * M 0 2 -
                M 2 2 * M 0 1 * M 0 1) =
          (M 0 0 * M 1 1 - M 0 1 * M 0 1) *
            (M 0 0 * M 2 2 - M 0 2 * M 0 2) := by
      ring
    rw [hdet', hp01', hp02'] at hid
    simpa using hid
  have hcross0 :
      M 0 0 * M 1 2 - M 0 1 * M 0 2 = 0 := by
    rcases mul_eq_zero.mp hcross0sq with h | h
    · exact h
    · exact h

  have hcross1sq :
      (M 0 1 * M 1 2 - M 0 2 * M 1 1) *
          (M 0 1 * M 1 2 - M 0 2 * M 1 1) = 0 := by
    have hid :
        (M 0 1 * M 1 2 - M 0 2 * M 1 1) *
              (M 0 1 * M 1 2 - M 0 2 * M 1 1) +
            M 1 1 *
              (M 0 0 * M 1 1 * M 2 2 +
                2 * M 0 1 * M 0 2 * M 1 2 -
                M 0 0 * M 1 2 * M 1 2 -
                M 1 1 * M 0 2 * M 0 2 -
                M 2 2 * M 0 1 * M 0 1) =
          (M 0 0 * M 1 1 - M 0 1 * M 0 1) *
            (M 1 1 * M 2 2 - M 1 2 * M 1 2) := by
      ring
    rw [hdet', hp01', hp12'] at hid
    simpa using hid
  have hcross1 :
      M 0 1 * M 1 2 - M 0 2 * M 1 1 = 0 := by
    rcases mul_eq_zero.mp hcross1sq with h | h
    · exact h
    · exact h

  have hcross2sq :
      (M 0 1 * M 2 2 - M 0 2 * M 1 2) *
          (M 0 1 * M 2 2 - M 0 2 * M 1 2) = 0 := by
    have hid :
        (M 0 1 * M 2 2 - M 0 2 * M 1 2) *
              (M 0 1 * M 2 2 - M 0 2 * M 1 2) +
            M 2 2 *
              (M 0 0 * M 1 1 * M 2 2 +
                2 * M 0 1 * M 0 2 * M 1 2 -
                M 0 0 * M 1 2 * M 1 2 -
                M 1 1 * M 0 2 * M 0 2 -
                M 2 2 * M 0 1 * M 0 1) =
          (M 0 0 * M 2 2 - M 0 2 * M 0 2) *
            (M 1 1 * M 2 2 - M 1 2 * M 1 2) := by
      ring
    rw [hdet', hp02', hp12'] at hid
    simpa using hid
  have hcross2 :
      M 0 1 * M 2 2 - M 0 2 * M 1 2 = 0 := by
    rcases mul_eq_zero.mp hcross2sq with h | h
    · exact h
    · exact h

  rcases hminor with ⟨i, j, k, l, hne⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [M]

/-- Applied to a residual-positive first 3x3 tail, the rank-two branch has a
literal coordinate-principal active 2x2 pivot. -/
theorem rankTwo_has_principalPivot
    (E : ExactZeroThreeSchurClock R)
    (hsymm : E.zeroSeries.matrix.IsSymm)
    (hres : 0 < E.residualDefect)
    (hminor : HasTwoByTwoMinor E.tailConstantMatrix) :
    (E.tailConstantMatrix 0 0 * E.tailConstantMatrix 1 1 -
        E.tailConstantMatrix 0 1 * E.tailConstantMatrix 1 0 ≠ 0) ∨
      (E.tailConstantMatrix 0 0 * E.tailConstantMatrix 2 2 -
        E.tailConstantMatrix 0 2 * E.tailConstantMatrix 2 0 ≠ 0) ∨
      (E.tailConstantMatrix 1 1 * E.tailConstantMatrix 2 2 -
        E.tailConstantMatrix 1 2 * E.tailConstantMatrix 2 1 ≠ 0) := by
  exact E.exists_principalTwoByTwoMinor_ne_zero_of_symmetric_singular
    hsymm (E.tailConstantMatrix_det_zero_of_residual_pos hres) hminor


end ExactZeroThreeSchurClock

end

end HC4.Newton
