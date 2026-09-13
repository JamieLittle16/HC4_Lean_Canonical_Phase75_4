import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningFirstTailRank
import HC4.Newton.GeneralThreeBlockSecondScalarSchur
import Mathlib.Tactic

/-!
# A18.4.98: select the second scalar Schur clock

In the rank-one branch of A18.4.96 the first normalised `3 x 3` tail is
nonzero and every `2 x 2` minor of its constant matrix vanishes.  A18.4.95
therefore supplies a nonzero diagonal entry.  We use that entry as the second
scalar pivot.

The polynomial tail is kept literally, up to one of the two explicit
simultaneous reorderings from A18.4.97.  The three cleared binary Schur entries
have zero constant coefficient because they are precisely `2 x 2` minors of
the first tail constant matrix.  A18.4.97 then produces the existing
`ExactZeroSchurClock` with defect equal to the first-tail residual defect.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock

@[simp] theorem tailBlock_a_coeff_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.a.coeff 0 = D.tailConstantBlock.a := rfl

@[simp] theorem tailBlock_b_coeff_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.b.coeff 0 = D.tailConstantBlock.b := rfl

@[simp] theorem tailBlock_c_coeff_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.c.coeff 0 = D.tailConstantBlock.c := rfl

@[simp] theorem tailBlock_d_coeff_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.d.coeff 0 = D.tailConstantBlock.d := rfl

@[simp] theorem tailBlock_e_coeff_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.e.coeff 0 = D.tailConstantBlock.e := rfl

@[simp] theorem tailBlock_f_coeff_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.f.coeff 0 = D.tailConstantBlock.f := rfl

end AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock

/-- Provenance of the selected second scalar pivot. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivotOrigin
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G)
    (T : GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K))) : Prop
  | first (block_eq : T = D.tailBlock)
  | second (block_eq : T = D.tailBlock.pivotD)
  | third (block_eq : T = D.tailBlock.pivotF)

/-- The actual second scalar-pivot block together with its exact binary clock. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarClock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) : Type (u + 1) where
  block : GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K))
  origin : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivotOrigin D block
  pivot_coeff_zero_ne_zero : block.a.coeff 0 ≠ 0
  block_determinantCore :
    block.determinantCore =
      D.clock.clearingFactor * Polynomial.X ^ D.clock.residualDefect
  clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K)
  clock_defect_eq : clock.defect = D.clock.residualDefect

/-- **The rank-one first tail always supplies the exact second scalar clock.** -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.secondScalarClock_of_rankOne
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G)
    (hres : 0 < D.clock.residualDefect)
    (hall : D.tailConstantBlock.AllTwoByTwoMinorsZero) :
    Nonempty (AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarClock D) := by
  have hmat := D.tailConstantBlock_matrix_ne_zero
  rcases D.tailConstantBlock.exists_diagonal_ne_zero_of_allTwoByTwoMinorsZero
      hall hmat with ha | hd | hf
  · let T := D.tailBlock
    have hpivot : T.a.coeff 0 ≠ 0 := by
      simpa [T] using ha
    have hA0 : T.scalarSchurA.coeff 0 = 0 := by
      have h := hall (0 : Fin 3) 0 1 1
      simpa [T, GeneralThreeBlock.scalarSchurA,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero] using h
    have hB0 : T.scalarSchurB.coeff 0 = 0 := by
      have h := hall (0 : Fin 3) 0 1 2
      simpa [T, GeneralThreeBlock.scalarSchurB,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero] using h
    have hC0 : T.scalarSchurC.coeff 0 = 0 := by
      have h := hall (0 : Fin 3) 0 2 2
      simpa [T, GeneralThreeBlock.scalarSchurC,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero] using h
    have hdet :
        T.determinantCore =
          D.clock.clearingFactor * Polynomial.X ^ D.clock.residualDefect := by
      simpa [T] using D.tailBlock_determinantCore
    let E := T.exactZeroSchurClockOfScalarPivot
      D.clock.clearingFactor D.clock.residualDefect
      hdet hpivot D.clock.clearingFactor_coeff_zero_ne_zero hA0 hB0 hC0
    exact ⟨{
      block := T
      origin := .first rfl
      pivot_coeff_zero_ne_zero := hpivot
      block_determinantCore := hdet
      clock := E
      clock_defect_eq := rfl
    }⟩

  · let T := D.tailBlock.pivotD
    have hpivot : T.a.coeff 0 ≠ 0 := by
      simpa [T, GeneralThreeBlock.pivotD] using hd
    have hA0 : T.scalarSchurA.coeff 0 = 0 := by
      have h := hall (1 : Fin 3) 1 0 0
      simpa [T, GeneralThreeBlock.pivotD, GeneralThreeBlock.scalarSchurA,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero,
        mul_comm] using h
    have hB0 : T.scalarSchurB.coeff 0 = 0 := by
      have h := hall (1 : Fin 3) 1 0 2
      simpa [T, GeneralThreeBlock.pivotD, GeneralThreeBlock.scalarSchurB,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero,
        mul_comm] using h
    have hC0 : T.scalarSchurC.coeff 0 = 0 := by
      have h := hall (1 : Fin 3) 1 2 2
      simpa [T, GeneralThreeBlock.pivotD, GeneralThreeBlock.scalarSchurC,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero,
        mul_comm] using h
    have hdet :
        T.determinantCore =
          D.clock.clearingFactor * Polynomial.X ^ D.clock.residualDefect := by
      rw [show T.determinantCore = D.tailBlock.determinantCore by
        simpa [T] using GeneralThreeBlock.pivotD_determinantCore D.tailBlock]
      exact D.tailBlock_determinantCore
    let E := T.exactZeroSchurClockOfScalarPivot
      D.clock.clearingFactor D.clock.residualDefect
      hdet hpivot D.clock.clearingFactor_coeff_zero_ne_zero hA0 hB0 hC0
    exact ⟨{
      block := T
      origin := .second rfl
      pivot_coeff_zero_ne_zero := hpivot
      block_determinantCore := hdet
      clock := E
      clock_defect_eq := rfl
    }⟩

  · let T := D.tailBlock.pivotF
    have hpivot : T.a.coeff 0 ≠ 0 := by
      simpa [T, GeneralThreeBlock.pivotF] using hf
    have hA0 : T.scalarSchurA.coeff 0 = 0 := by
      have h := hall (2 : Fin 3) 2 1 1
      simpa [T, GeneralThreeBlock.pivotF, GeneralThreeBlock.scalarSchurA,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero,
        mul_comm] using h
    have hB0 : T.scalarSchurB.coeff 0 = 0 := by
      have h := hall (2 : Fin 3) 2 1 0
      simpa [T, GeneralThreeBlock.pivotF, GeneralThreeBlock.scalarSchurB,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero,
        mul_comm] using h
    have hC0 : T.scalarSchurC.coeff 0 = 0 := by
      have h := hall (2 : Fin 3) 2 0 0
      simpa [T, GeneralThreeBlock.pivotF, GeneralThreeBlock.scalarSchurC,
        GeneralThreeBlock.matrix, Polynomial.coeff_zero_eq_eval_zero,
        mul_comm] using h
    have hdet :
        T.determinantCore =
          D.clock.clearingFactor * Polynomial.X ^ D.clock.residualDefect := by
      rw [show T.determinantCore = D.tailBlock.determinantCore by
        simpa [T] using GeneralThreeBlock.pivotF_determinantCore D.tailBlock]
      exact D.tailBlock_determinantCore
    let E := T.exactZeroSchurClockOfScalarPivot
      D.clock.clearingFactor D.clock.residualDefect
      hdet hpivot D.clock.clearingFactor_coeff_zero_ne_zero hA0 hB0 hC0
    exact ⟨{
      block := T
      origin := .third rfl
      pivot_coeff_zero_ne_zero := hpivot
      block_determinantCore := hdet
      clock := E
      clock_defect_eq := rfl
    }⟩

end

end HC4.Valuation
