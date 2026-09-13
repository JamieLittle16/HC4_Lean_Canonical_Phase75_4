import HC4.Newton.GeneralThreeBlockScalarSchur
import Mathlib.Tactic

/-!
# A18.4.97: generic second scalar Schur clock

After the first scalar-pivot stage, the remaining rank-one case is a symmetric
polynomial `3 x 3` block whose constant matrix is nonzero but has every
`2 x 2` minor zero.  Choosing a nonzero diagonal constant coefficient gives a
scalar pivot.  The cleared binary Schur block then has zero constant block and
its determinant is the pivot times the determinant of the `3 x 3` block.

This file packages that purely algebraic step as the existing
`ExactZeroSchurClock`.  Two explicit simultaneous reorderings allow any of the
three diagonal entries to serve as the first coordinate.  The construction is
independent of HC4 geometry.
-/

namespace HC4.Newton

noncomputable section

universe u
variable {R : Type u} [CommRing R]

namespace GeneralThreeBlock

/-- Simultaneous order `(1,0,2)`. -/
noncomputable def pivotD (T : GeneralThreeBlock R) : GeneralThreeBlock R where
  a := T.d
  b := T.b
  c := T.e
  d := T.a
  e := T.c
  f := T.f

/-- Simultaneous order `(2,1,0)`. -/
noncomputable def pivotF (T : GeneralThreeBlock R) : GeneralThreeBlock R where
  a := T.f
  b := T.e
  c := T.c
  d := T.d
  e := T.b
  f := T.a

/-- Simultaneous reordering preserves the determinant core. -/
theorem pivotD_determinantCore (T : GeneralThreeBlock R) :
    T.pivotD.determinantCore = T.determinantCore := by
  unfold pivotD determinantCore
  ring

/-- Simultaneous reordering preserves the determinant core. -/
theorem pivotF_determinantCore (T : GeneralThreeBlock R) :
    T.pivotF.determinantCore = T.determinantCore := by
  unfold pivotF determinantCore
  ring

end GeneralThreeBlock

/-- Binary series obtained by clearing the scalar Schur complement of the
first coordinate of a polynomial three-block. -/
noncomputable def GeneralThreeBlock.binaryScalarSchurSeries
    (T : GeneralThreeBlock (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := T.scalarSchurA
  offDiag := T.scalarSchurB
  kernel := T.scalarSchurC

/-- Its binary determinant is the scalar-Schur determinant expression. -/
theorem GeneralThreeBlock.binaryScalarSchurSeries_determinant
    (T : GeneralThreeBlock (Polynomial R)) :
    T.binaryScalarSchurSeries.determinant = T.scalarSchurDeterminant := by
  rfl

/-- **Generic second scalar clock.**

A nonzero scalar constant pivot together with zero constant cleared entries and
an exact determinant clock on `T` produces an `ExactZeroSchurClock`. -/
noncomputable def GeneralThreeBlock.exactZeroSchurClockOfScalarPivot
    [IsDomain R]
    (T : GeneralThreeBlock (Polynomial R))
    (clearingFactor : Polynomial R)
    (defect : ℕ)
    (hdet : T.determinantCore = clearingFactor * Polynomial.X ^ defect)
    (hpivot : T.a.coeff 0 ≠ 0)
    (hclear : clearingFactor.coeff 0 ≠ 0)
    (hA0 : T.scalarSchurA.coeff 0 = 0)
    (hB0 : T.scalarSchurB.coeff 0 = 0)
    (hC0 : T.scalarSchurC.coeff 0 = 0) :
    ExactZeroSchurClock R := by
  let Z : ZeroSchurSeries R := {
    series := T.binaryScalarSchurSeries
    active_coeff_zero := hA0
    offDiag_coeff_zero := hB0
    kernel_coeff_zero := hC0
  }
  have hfactor0 : (T.a * clearingFactor).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_mul]
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    exact mul_ne_zero hpivot hclear
  have hdetZ :
      Z.series.determinant =
        (T.a * clearingFactor) * Polynomial.X ^ defect := by
    calc
      Z.series.determinant = T.scalarSchurDeterminant := by
        rfl
      _ = T.a * T.determinantCore := T.scalarSchurDeterminant_eq
      _ = T.a * (clearingFactor * Polynomial.X ^ defect) := by
        rw [hdet]
      _ = (T.a * clearingFactor) * Polynomial.X ^ defect := by ring
  exact {
    zeroSeries := Z
    clearingFactor := T.a * clearingFactor
    defect := defect
    clearingFactor_coeff_zero_ne_zero := hfactor0
    determinantFactor := hdetZ
  }

end

end HC4.Newton
