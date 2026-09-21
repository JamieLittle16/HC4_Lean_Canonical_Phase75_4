import HC4.Newton.RankOneThreeToBinarySchur
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurFirstEntry
import Mathlib.Tactic

/-!
# Second finite Schur stage for the zero-clock top-kernel seam

The first 1+3 Schur quotient gives an exact zero-constant 3x3 clock.
After removing its common first parameter factor, the constant coefficient
matrix is nonzero and has exactly three possibilities:

* determinant nonzero: the 3x3 determinant clock closes at that first layer;
* some 2x2 minor nonzero: literal rank-two geometry is already present;
* all 2x2 minors zero: the first coefficient matrix has rank one.

The generic second-Schur theorem now removes the last case.  Since the actual
1+3 quotient is symmetric, its normalised tail is symmetric; a nonzero
symmetric rank-one 3x3 matrix has a nonzero diagonal pivot, and the cleared
1+2 quotient is an exact binary zero-Schur clock.

Thus no rank-one 3x3 residual remains after this stage.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The actual cleared 1+3 Schur matrix is symmetric in every scalar-pivot
orientation. -/
theorem TopKernelThreeSchurClockData.exactZeroThreeSchurClock_isSymm
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    S.toExactZeroThreeSchurClock.zeroSeries.matrix.IsSymm := by
  cases S with
  | pivotA hpivot hzero hdet =>
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          GeneralFourBlock.rankOneClearedThreeSchurMatrix]
  | pivotD hpivot hzero hdet =>
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixD]
  | pivotX hpivot hzero hdet =>
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixX]

/-- Finite second-stage frontier of the actual top-kernel 1+3 quotient. -/
inductive TopKernelThreeSchurSecondStageFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | determinantClosing
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)
  | rankTwo
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (minor :
        ExactZeroThreeSchurClock.HasTwoByTwoMinor
          S.toExactZeroThreeSchurClock.tailConstantMatrix)
  | binaryZeroSchur
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (defect_eq :
        clock.defect =
          S.toExactZeroThreeSchurClock.residualDefect)

/-- **Second finite Schur exhaustion.**

The rank-one branch of the first 3x3 coefficient block is converted
canonically into an exact binary zero-Schur clock. -/
theorem TopKernelThreeSchurClockData.secondStageFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    Nonempty (P.TopKernelThreeSchurSecondStageFrontier S) := by
  let E := S.toExactZeroThreeSchurClock
  have hsymm : E.zeroSeries.matrix.IsSymm := by
    simpa [E] using S.exactZeroThreeSchurClock_isSymm
  cases E.firstTailRankFrontier with
  | determinantClosing hres hdet =>
      exact ⟨.determinantClosing hres hdet⟩
  | rankTwo hres hminor =>
      exact ⟨.rankTwo hres hminor⟩
  | rankOne hres hall hne =>
      let B : ExactZeroSchurClock (MvPolynomial (Fin 4) K) :=
        E.toBinaryZeroSchurClock_of_rankOne hsymm hall hne
      exact ⟨.binaryZeroSchur hres B rfl⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
