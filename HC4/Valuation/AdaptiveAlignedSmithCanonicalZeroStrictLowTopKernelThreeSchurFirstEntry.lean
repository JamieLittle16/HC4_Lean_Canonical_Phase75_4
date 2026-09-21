import HC4.Newton.ZeroThreeSchurFirstEntryClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurClock
import Mathlib.Tactic

/-!
# First positive layer of the zero-clock top-kernel 1+3 Schur quotient

The preceding HC4-specific module produces, in one of three scalar-pivot
orientations, a zero-constant 3x3 cleared Schur quotient whose determinant is

    pivot(X)^2 * X^(4D-8)

and whose pivot has nonzero constant coefficient.

The generic 3x3 first-entry clock therefore applies directly.  This file
packages that clock back onto the actual top-kernel reverse-Rees seam.

The conclusion is deliberately algebraic:

* a genuine positive first quotient order e exists;
* the normalised first quotient coefficient matrix is nonzero;
* 3e <= 4D-8.

No repair edge, terminal cocharacter, or JC2 hypothesis is introduced.
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

/-- Turn the source-facing three-Schur packet into the generic exact
zero-constant 3x3 determinant clock. -/
noncomputable def TopKernelThreeSchurClockData.toExactZeroThreeSchurClock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    ExactZeroThreeSchurClock (MvPolynomial (Fin 4) K) := by
  cases S with
  | pivotA hpivot hzero hdet =>
      exact {
        zeroSeries := {
          matrix := P.threeSchurBlock.rankOneClearedThreeSchurMatrix
          coeff_zero := hzero
        }
        clearingFactor := P.threeSchurBlock.a ^ 2
        defect := T.topKernelOrdinaryReesDefect
        clearingFactor_coeff_zero_ne_zero := by
          rw [Polynomial.coeff_pow]
          simp [hpivot]
        determinantFactor := hdet
      }
  | pivotD hpivot hzero hdet =>
      exact {
        zeroSeries := {
          matrix := P.threeSchurBlock.rankOneClearedThreeSchurMatrixD
          coeff_zero := hzero
        }
        clearingFactor := P.threeSchurBlock.d ^ 2
        defect := T.topKernelOrdinaryReesDefect
        clearingFactor_coeff_zero_ne_zero := by
          rw [Polynomial.coeff_pow]
          simp [hpivot]
        determinantFactor := hdet
      }
  | pivotX hpivot hzero hdet =>
      exact {
        zeroSeries := {
          matrix := P.threeSchurBlock.rankOneClearedThreeSchurMatrixX
          coeff_zero := hzero
        }
        clearingFactor := P.threeSchurBlock.x ^ 2
        defect := T.topKernelOrdinaryReesDefect
        clearingFactor_coeff_zero_ne_zero := by
          rw [Polynomial.coeff_pow]
          simp [hpivot]
        determinantFactor := hdet
      }

/-- Every top-kernel linear-power seam has an exact zero-constant 3x3 Schur
clock. -/
theorem exists_exactZeroThreeSchurClock
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty (ExactZeroThreeSchurClock (MvPolynomial (Fin 4) K)) := by
  rcases P.threeSchurClockData with ⟨S⟩
  exact ⟨S.toExactZeroThreeSchurClock⟩

/-- First positive 1+3 quotient order attached canonically to a chosen clock
packet. -/
noncomputable def TopKernelThreeSchurClockData.firstThreeSchurOrder
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : ℕ :=
  S.toExactZeroThreeSchurClock.firstOrder

theorem TopKernelThreeSchurClockData.firstThreeSchurOrder_pos
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    0 < S.firstThreeSchurOrder :=
  S.toExactZeroThreeSchurClock.firstOrder_pos

/-- **Three-way rank budget.**  The first common quotient order consumes at
most one third of the exact four-variable reverse-Rees determinant clock. -/
theorem TopKernelThreeSchurClockData.triple_firstThreeSchurOrder_le_defect
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    3 * S.firstThreeSchurOrder ≤ T.topKernelOrdinaryReesDefect := by
  exact S.toExactZeroThreeSchurClock.triple_firstOrder_le_defect

/-- Expanded form of the same budget against the selected top degree. -/
theorem TopKernelThreeSchurClockData.triple_firstThreeSchurOrder_le_fourDegree_sub_eight
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    3 * S.firstThreeSchurOrder ≤ 4 * T.topFace.degree - 8 := by
  simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelOrdinaryReesDefect]
    using S.triple_firstThreeSchurOrder_le_defect

/-- The normalised first 3x3 quotient coefficient matrix is genuinely
nonzero. -/
theorem TopKernelThreeSchurClockData.firstThreeSchurTail_nonzero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    ∃ i j : Fin 3,
      (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
        S.toExactZeroThreeSchurClock.hasPositiveEntryLayer i j).coeff 0 ≠ 0 :=
  S.toExactZeroThreeSchurClock.tail_constant_entry_ne_zero

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
