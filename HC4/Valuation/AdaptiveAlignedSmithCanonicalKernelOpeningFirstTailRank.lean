import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock
import HC4.Newton.GeneralThreeBlockScalarSchur
import Mathlib.Tactic

/-!
# A18.4.96: rank of the first scalar-Schur tail

A18.4.94 attaches an exact scalar-pivot `3 x 3` Schur clock to the genuine
rank-one saturated opening.  A18.4.93 removes the first common positive order
and leaves a normalised symmetric `3 x 3` tail whose determinant has the exact
residual clock.

This file packages that tail as an honest `GeneralThreeBlock` and performs the
finite rank split prepared by A18.4.95.

* residual defect zero: the first tail constant matrix is nondegenerate;
* positive residual defect and some `2 x 2` minor nonzero: the first tail has
  rank at least two;
* positive residual defect and all `2 x 2` minors zero: the first tail is the
  genuine rank-one case for the second scalar Schur stage.

No repair tag is introduced.  The output is only matrix geometry carried by
the exact scalar-Schur clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock

/-- The normalised first scalar-Schur tail remains symmetric.  Although the
entry quotients are chosen independently, equality of opposite entries before
factor removal and cancellation of the nonzero common power force equality of
the chosen tails. -/
theorem tailMatrix_symmetric
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.clock.tailMatrix.IsSymm := by
  intro i j
  have hseries :
      D.clock.zeroSeries.series i j = D.clock.zeroSeries.series j i := by
    rw [D.clock_series_eq]
    exact GeneralFourBlock.scalarSchurThreeMatrix_symmetric D.block i j
  have hij :=
    D.clock.zeroSeries.entry_eq_firstFactor_mul_tail
      D.clock.hasPositiveEntryLayer i j
  have hji :=
    D.clock.zeroSeries.entry_eq_firstFactor_mul_tail
      D.clock.hasPositiveEntryLayer j i
  have hmul :
      (Polynomial.X ^ D.clock.firstOrder :
          Polynomial (MvPolynomial (Fin 4) K)) * D.clock.tailMatrix i j =
        Polynomial.X ^ D.clock.firstOrder * D.clock.tailMatrix j i := by
    rw [← hij, ← hji]
    exact hseries
  exact mul_left_cancel₀
    (pow_ne_zero D.clock.firstOrder
      (Polynomial.X_ne_zero :
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ≠ 0))
    hmul

/-- Symmetric polynomial three-block representing the complete normalised
first tail. -/
noncomputable def tailBlock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralThreeBlock.ofSymmetricMatrix D.clock.tailMatrix D.tailMatrix_symmetric

@[simp]
theorem tailBlock_matrix
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.matrix = D.clock.tailMatrix := by
  exact GeneralThreeBlock.matrix_ofSymmetricMatrix
    D.clock.tailMatrix D.tailMatrix_symmetric

/-- The polynomial three-block carries exactly the residual determinant clock. -/
theorem tailBlock_determinantCore
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailBlock.determinantCore =
      D.clock.clearingFactor * Polynomial.X ^ D.clock.residualDefect := by
  calc
    D.tailBlock.determinantCore = D.tailBlock.matrix.det :=
      (GeneralThreeBlock.matrix_det D.tailBlock).symm
    _ = D.clock.tailMatrix.det := by rw [D.tailBlock_matrix]
    _ = D.clock.clearingFactor * Polynomial.X ^ D.clock.residualDefect :=
      D.clock.tail_determinantFactor

/-- Constant coefficient matrix of the first tail remains symmetric. -/
theorem tailConstantMatrix_symmetric
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.clock.tailConstantMatrix.IsSymm := by
  intro i j
  exact congrArg
    (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0)
    (D.tailMatrix_symmetric i j)

/-- Finite three-block at the first positive scalar-Schur layer. -/
noncomputable def tailConstantBlock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
  GeneralThreeBlock.ofSymmetricMatrix
    D.clock.tailConstantMatrix D.tailConstantMatrix_symmetric

@[simp]
theorem tailConstantBlock_matrix
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailConstantBlock.matrix = D.clock.tailConstantMatrix := by
  exact GeneralThreeBlock.matrix_ofSymmetricMatrix
    D.clock.tailConstantMatrix D.tailConstantMatrix_symmetric

/-- The first tail constant block is genuinely nonzero. -/
theorem tailConstantBlock_matrix_ne_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.tailConstantBlock.matrix ≠ 0 := by
  rw [D.tailConstantBlock_matrix]
  exact D.clock.tailConstantMatrix_ne_zero

end AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock

/-- Exact finite rank alternatives for the first scalar-Schur tail. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningFirstTailRankFrontier
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) : Prop
  | fullRank
      (residual_zero : D.clock.residualDefect = 0)
      (det_ne_zero : D.tailConstantBlock.determinantCore ≠ 0)
  | rankTwo
      (residual_pos : 0 < D.clock.residualDefect)
      (witness : D.tailConstantBlock.HasTwoByTwoMinorWitness)
  | rankOne
      (residual_pos : 0 < D.clock.residualDefect)
      (allTwoByTwo : D.tailConstantBlock.AllTwoByTwoMinorsZero)

/-- **Complete first-tail rank split.** -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.firstTailRankFrontier
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    AdaptiveAlignedSmithCanonicalKernelOpeningFirstTailRankFrontier D := by
  by_cases hres0 : D.clock.residualDefect = 0
  · have hdetM :=
      D.clock.tailConstantMatrix_det_ne_zero_of_residual_zero hres0
    have hdet : D.tailConstantBlock.determinantCore ≠ 0 := by
      intro hzero
      apply hdetM
      calc
        D.clock.tailConstantMatrix.det = D.tailConstantBlock.matrix.det := by
          rw [D.tailConstantBlock_matrix]
        _ = D.tailConstantBlock.determinantCore :=
          GeneralThreeBlock.matrix_det D.tailConstantBlock
        _ = 0 := hzero
    exact .fullRank hres0 hdet
  · have hres : 0 < D.clock.residualDefect := Nat.pos_of_ne_zero hres0
    rcases D.tailConstantBlock.twoByTwoWitness_or_allZero with hwitness | hall
    · exact .rankTwo hres hwitness
    · exact .rankOne hres hall

end

end HC4.Valuation
