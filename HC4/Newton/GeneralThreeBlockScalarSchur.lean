import HC4.Newton.ZeroSchurFirstEntryClock
import Mathlib.Tactic

/-!
# A18.4.95: symmetric three-block rank split and second scalar Schur identity

The first scalar-pivot stage leaves a symmetric `3 x 3` coefficient block.
This file records the finite algebra needed for the second and final stage of
the rank ladder.

For

    T = [[a,b,c],
         [b,d,e],
         [c,e,f]],

the cleared scalar Schur complement of the pivot `a` is the binary block

    [[a d - b^2, a e - b c],
     [a e - b c, a f - c^2]],

whose determinant is exactly

    a * det T.

We also retain the exact division-free split `some 2 x 2 minor nonzero` versus
`all 2 x 2 minors zero`.  In the latter branch, a nonzero symmetric matrix
over a domain has a nonzero diagonal pivot.
-/

namespace HC4.Newton

noncomputable section

universe u
variable {R : Type u} [CommRing R]

structure GeneralThreeBlock (R : Type*) [CommRing R] where
  a : R
  b : R
  c : R
  d : R
  e : R
  f : R

namespace GeneralThreeBlock

/-- Displayed symmetric matrix. -/
noncomputable def matrix (T : GeneralThreeBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![T.a, T.b, T.c;
     T.b, T.d, T.e;
     T.c, T.e, T.f]

/-- Explicit determinant core. -/
def determinantCore (T : GeneralThreeBlock R) : R :=
  T.a * T.d * T.f + 2 * T.b * T.c * T.e -
    T.a * T.e * T.e - T.d * T.c * T.c - T.f * T.b * T.b

/-- The explicit core is the matrix determinant. -/
theorem matrix_det (T : GeneralThreeBlock R) :
    T.matrix.det = T.determinantCore := by
  simp [matrix, determinantCore, Matrix.det_fin_three]
  ring

/-- Package an arbitrary symmetric `3 x 3` matrix. -/
noncomputable def ofSymmetricMatrix
    (M : Matrix (Fin 3) (Fin 3) R)
    (hsymm : ∀ i j, M i j = M j i) : GeneralThreeBlock R where
  a := M 0 0
  b := M 0 1
  c := M 0 2
  d := M 1 1
  e := M 1 2
  f := M 2 2

/-- Repacking a symmetric matrix recovers it literally. -/
theorem matrix_ofSymmetricMatrix
    (M : Matrix (Fin 3) (Fin 3) R)
    (hsymm : ∀ i j, M i j = M j i) :
    (ofSymmetricMatrix M hsymm).matrix = M := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ofSymmetricMatrix, matrix]
  all_goals exact hsymm _ _

/-- Every displayed `2 x 2` minor vanishes. -/
def AllTwoByTwoMinorsZero (T : GeneralThreeBlock R) : Prop :=
  ∀ i j k l : Fin 3,
    T.matrix i j * T.matrix k l -
      T.matrix i l * T.matrix k j = 0

/-- Explicit witness that the matrix has rank at least two. -/
def HasTwoByTwoMinorWitness (T : GeneralThreeBlock R) : Prop :=
  ∃ i j k l : Fin 3,
    T.matrix i j * T.matrix k l -
      T.matrix i l * T.matrix k j ≠ 0

/-- Exhaustive finite determinantal split. -/
theorem twoByTwoWitness_or_allZero
    (T : GeneralThreeBlock R) :
    T.HasTwoByTwoMinorWitness ∨ T.AllTwoByTwoMinorsZero := by
  classical
  by_cases hall : T.AllTwoByTwoMinorsZero
  · exact Or.inr hall
  · left
    unfold AllTwoByTwoMinorsZero at hall
    simp only [not_forall] at hall
    rcases hall with ⟨i, hi⟩
    rcases hi with ⟨j, hj⟩
    rcases hj with ⟨k, hk⟩
    rcases hk with ⟨l, hl⟩
    exact ⟨i, j, k, l, hl⟩

/-- A nonzero rank-at-most-one symmetric three-block has a nonzero diagonal
entry. -/
theorem exists_diagonal_ne_zero_of_allTwoByTwoMinorsZero
    [IsDomain R]
    (T : GeneralThreeBlock R)
    (hall : T.AllTwoByTwoMinorsZero)
    (hmat : T.matrix ≠ 0) :
    T.a ≠ 0 ∨ T.d ≠ 0 ∨ T.f ≠ 0 := by
  by_contra hdiag
  push_neg at hdiag
  rcases hdiag with ⟨ha, hd, hf⟩
  have hb2 : T.b * T.b = 0 := by
    have h := hall (0 : Fin 3) 1 1 0
    simpa [matrix, ha, hd] using h
  have hc2 : T.c * T.c = 0 := by
    have h := hall (0 : Fin 3) 2 2 0
    simpa [matrix, ha, hf] using h
  have he2 : T.e * T.e = 0 := by
    have h := hall (1 : Fin 3) 2 2 1
    simpa [matrix, hd, hf] using h
  have hb : T.b = 0 := by
    rcases mul_eq_zero.mp hb2 with h | h <;> exact h
  have hc : T.c = 0 := by
    rcases mul_eq_zero.mp hc2 with h | h <;> exact h
  have he : T.e = 0 := by
    rcases mul_eq_zero.mp he2 with h | h <;> exact h
  apply hmat
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, ha, hd, hf, hb, hc, he]

/-- Entries of the cleared second scalar Schur block. -/
def scalarSchurA (T : GeneralThreeBlock R) : R :=
  T.a * T.d - T.b * T.b

def scalarSchurB (T : GeneralThreeBlock R) : R :=
  T.a * T.e - T.b * T.c

def scalarSchurC (T : GeneralThreeBlock R) : R :=
  T.a * T.f - T.c * T.c

/-- Binary polynomial-style determinant expression of the cleared block. -/
def scalarSchurDeterminant (T : GeneralThreeBlock R) : R :=
  T.scalarSchurA * T.scalarSchurC - T.scalarSchurB * T.scalarSchurB

/-- **Second scalar Schur determinant identity.** -/
theorem scalarSchurDeterminant_eq
    (T : GeneralThreeBlock R) :
    T.scalarSchurDeterminant = T.a * T.determinantCore := by
  unfold scalarSchurDeterminant scalarSchurA scalarSchurB scalarSchurC
    determinantCore
  ring

/-- All `2 x 2` minors zero makes the entire second scalar Schur block zero. -/
theorem scalarSchur_eq_zero_of_allTwoByTwoMinorsZero
    (T : GeneralThreeBlock R)
    (hall : T.AllTwoByTwoMinorsZero) :
    T.scalarSchurA = 0 ∧ T.scalarSchurB = 0 ∧ T.scalarSchurC = 0 := by
  have hA := hall (0 : Fin 3) 0 1 1
  have hB := hall (0 : Fin 3) 0 1 2
  have hC := hall (0 : Fin 3) 0 2 2
  constructor
  · simpa [matrix, scalarSchurA] using hA
  constructor
  · simpa [matrix, scalarSchurB, mul_comm] using hB
  · simpa [matrix, scalarSchurC] using hC

end GeneralThreeBlock

end

end HC4.Newton
