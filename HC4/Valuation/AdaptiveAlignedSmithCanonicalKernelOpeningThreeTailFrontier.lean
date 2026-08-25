import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock
import HC4.Newton.GeneralThreeBlockScalarSchur
import Mathlib.Tactic

/-!
# A18.4.96: first scalar-Schur tail is rank three or has a second scalar pivot

The first scalar-pivot clock leaves a normalised polynomial `3 x 3` tail.
Its constant matrix is nonzero.  If its residual determinant order is zero,
that constant matrix is already nondegenerate.  If the residual order is
positive, the constant determinant vanishes and we inspect its `2 x 2`
minors.

A nonzero `2 x 2` minor is the missing pair of directions beyond the original
scalar pivot, hence genuine filtered rank-three geometry.  If every `2 x 2`
minor vanishes, the nonzero symmetric `3 x 3` constant matrix is genuinely
rank one; the domain lemma of A18.4.95 supplies a second scalar pivot.

No repair rank is changed in this file.  Every outcome retains the exact
first scalar-Schur clock and therefore the strict integral residual-defect
descent proved in A18.4.93.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The constant matrix of the first normalised scalar-Schur tail is symmetric. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.tailConstantMatrix_symmetric_threeTail
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    ∀ i j, D.clock.tailConstantMatrix i j = D.clock.tailConstantMatrix j i := by
  intro i j
  have hij :=
    (D.block.scalarSchurThreeMatrix_symmetric i j)
  have hseries :
      D.clock.zeroSeries.series i j = D.block.scalarSchurThreeMatrix i j := by
    rw [D.clock_series_eq]
  have hseries' :
      D.clock.zeroSeries.series j i = D.block.scalarSchurThreeMatrix j i := by
    rw [D.clock_series_eq]
  have hcoeff := congrArg
    (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff D.clock.firstOrder)
    hij
  change
    (D.clock.tailMatrix i j).coeff 0 =
      (D.clock.tailMatrix j i).coeff 0
  rw [← D.clock.zeroSeries.entry_coeff_first_eq_tail_zero
      D.clock.hasPositiveEntryLayer i j,
    ← D.clock.zeroSeries.entry_coeff_first_eq_tail_zero
      D.clock.hasPositiveEntryLayer j i]
  rw [hseries, hseries']
  exact hcoeff

/-- Package the first tail constant matrix as a symmetric three-block. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.tailThreeBlock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
  GeneralThreeBlock.ofSymmetricMatrix
    D.clock.tailConstantMatrix D.tailConstantMatrix_symmetric_threeTail

/-- Its displayed matrix is literally the clock's first-tail constant matrix. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.tailThreeBlock_matrix
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailThreeBlock.matrix = D.clock.tailConstantMatrix :=
  GeneralThreeBlock.matrix_ofSymmetricMatrix
    D.clock.tailConstantMatrix D.tailConstantMatrix_symmetric_threeTail

/-- The first tail three-block is nonzero. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.tailThreeBlock_matrix_ne_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailThreeBlock.matrix ≠ 0 := by
  rw [D.tailThreeBlock_matrix]
  exact D.clock.tailConstantMatrix_ne_zero

/-- Filtered rank-three geometry produced by the first scalar-Schur layer.
The outer scalar pivot is retained together with either an invertible first
`3 x 3` tail or a concrete nonzero `2 x 2` minor of that tail. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningFilteredRankThreeGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) : Type (u + 1)
  | nondegenerateThree
      (clock : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G)
      (residual_zero : clock.clock.residualDefect = 0)
      (det_ne_zero : clock.tailThreeBlock.determinantCore ≠ 0)
  | twoByTwoDeparture
      (clock : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G)
      (residual_pos : 0 < clock.clock.residualDefect)
      (witness : clock.tailThreeBlock.HasTwoByTwoMinorWitness)

/-- Genuine rank-one first tail plus the second scalar pivot which will feed
the binary zero-Schur clock. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) : Type (u + 1) where
  clock : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G
  residual_pos : 0 < clock.clock.residualDefect
  allTwoByTwo : clock.tailThreeBlock.AllTwoByTwoMinorsZero
  pivotIndex : Fin 3
  pivot_ne_zero : clock.tailThreeBlock.matrix pivotIndex pivotIndex ≠ 0

/-- Complete first-tail frontier. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningThreeTailFrontier
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) : Type (u + 1)
  | rankThree
      (geometry : AdaptiveAlignedSmithCanonicalKernelOpeningFilteredRankThreeGeometry G)
  | secondPivot
      (pivot : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot G)

/-- **First scalar-Schur tail exhaustion.** -/
noncomputable def
    AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.threeTailFrontier
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    AdaptiveAlignedSmithCanonicalKernelOpeningThreeTailFrontier G := by
  by_cases hres : D.clock.residualDefect = 0
  · have hdetMatrix : D.clock.tailConstantMatrix.det ≠ 0 :=
      D.clock.tailConstantMatrix_det_ne_zero_of_residual_zero hres
    have hdet : D.tailThreeBlock.determinantCore ≠ 0 := by
      rw [← D.tailThreeBlock.matrix_det, D.tailThreeBlock_matrix]
      exact hdetMatrix
    exact .rankThree (.nondegenerateThree D hres hdet)
  · have hrespos : 0 < D.clock.residualDefect := Nat.pos_of_ne_zero hres
    have hdetMatrix : D.clock.tailConstantMatrix.det = 0 :=
      D.clock.tailConstantMatrix_det_zero_of_residual_pos hrespos
    rcases D.tailThreeBlock.twoByTwoWitness_or_allZero with hwit | hall
    · exact .rankThree (.twoByTwoDeparture D hrespos hwit)
    · have hne := D.tailThreeBlock_matrix_ne_zero
      rcases D.tailThreeBlock.exists_diagonal_ne_zero_of_allTwoByTwoMinorsZero
          hall hne with ha | hd | hf
      · exact .secondPivot {
          clock := D
          residual_pos := hrespos
          allTwoByTwo := hall
          pivotIndex := 0
          pivot_ne_zero := by
            simpa [GeneralThreeBlock.matrix] using ha
        }
      · exact .secondPivot {
          clock := D
          residual_pos := hrespos
          allTwoByTwo := hall
          pivotIndex := 1
          pivot_ne_zero := by
            simpa [GeneralThreeBlock.matrix] using hd
        }
      · exact .secondPivot {
          clock := D
          residual_pos := hrespos
          allTwoByTwo := hall
          pivotIndex := 2
          pivot_ne_zero := by
            simpa [GeneralThreeBlock.matrix] using hf
        }

/-- Every genuine rank-one kernel opening reaches either filtered rank-three
geometry or the unique second scalar-pivot stage. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry.threeTailFrontier
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) :
    Nonempty (AdaptiveAlignedSmithCanonicalKernelOpeningThreeTailFrontier G) := by
  rcases G.scalarSchurClock with ⟨D⟩
  exact ⟨D.threeTailFrontier⟩

end

end HC4.Valuation
