import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativePrincipalSourceLift
import HC4.Newton.RankOneThreeToBinarySchur
import Mathlib.Tactic

/-!
# Orientation-preserving binary clock for the zero-relative tail

The zero-relative principal source frontier retains the rank-one constant 3x3
tail before the generic second Schur stage forgets which diagonal pivot was
used.  This file spends that retained witness directly.

A nonzero symmetric rank-one 3x3 constant matrix has a nonzero diagonal entry.
We choose the first available coordinate in the order 0, 1, 2 and construct
the corresponding exact binary zero-Schur clock through the public oriented
constructors.  The exact binary series, determinant defect, physical
zero-relative opening, and the original rank-one witness are all retained.

No repair progress and no terminal claim is introduced here.
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

/-- Exact binary zero-Schur clock together with the literal diagonal pivot of
the rank-one normalised 3x3 tail that constructed it. -/
inductive ZeroRelativeExplicitBinaryClockData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | pivot0
      (allMinors :
        ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
          S.toExactZeroThreeSchurClock.tailConstantMatrix)
      (matrix_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix ≠ 0)
      (pivot_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 ≠ 0)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (series_eq :
        clock.zeroSeries.series =
          threePivot0BinarySchurSeries
            (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
              S.toExactZeroThreeSchurClock.hasPositiveEntryLayer))
      (defect_eq :
        clock.defect = S.toExactZeroThreeSchurClock.residualDefect)
  | pivot1
      (allMinors :
        ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
          S.toExactZeroThreeSchurClock.tailConstantMatrix)
      (matrix_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix ≠ 0)
      (pivot0_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 = 0)
      (pivot_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 ≠ 0)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (series_eq :
        clock.zeroSeries.series =
          threePivot1BinarySchurSeries
            (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
              S.toExactZeroThreeSchurClock.hasPositiveEntryLayer))
      (defect_eq :
        clock.defect = S.toExactZeroThreeSchurClock.residualDefect)
  | pivot2
      (allMinors :
        ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
          S.toExactZeroThreeSchurClock.tailConstantMatrix)
      (matrix_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix ≠ 0)
      (pivot0_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 = 0)
      (pivot1_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 = 0)
      (pivot_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 ≠ 0)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (series_eq :
        clock.zeroSeries.series =
          threePivot2BinarySchurSeries
            (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
              S.toExactZeroThreeSchurClock.hasPositiveEntryLayer))
      (defect_eq :
        clock.defect = S.toExactZeroThreeSchurClock.residualDefect)

/-- Zero-relative source frontier with the remaining binary branch made
orientation-explicit. -/
inductive TopKernelThreeSchurZeroRelativeBinaryFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | determinantClosing
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)
  | representedSchur
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (geometry : P.PositiveTailRepresentedSourceSchurWitness)
  | explicitBinary
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (binary : P.ZeroRelativeExplicitBinaryClockData S)

/-- **D3: explicit diagonal pivot and exact binary zero-Schur clock.**

The rank-one zero-relative branch retains enough provenance to choose the
actual diagonal pivot before constructing the second Schur clock. -/
theorem TopKernelThreeSchurZeroRelativeSourceFrontier.toBinaryFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (F : P.TopKernelThreeSchurZeroRelativeSourceFrontier S M) :
    Nonempty (P.TopKernelThreeSchurZeroRelativeBinaryFrontier S M) := by
  cases F with
  | determinantClosing tail hz hopen hres hdet =>
      exact ⟨.determinantClosing tail hz hopen hres hdet⟩
  | representedSchur tail hz hopen geometry =>
      exact ⟨.representedSchur tail hz hopen geometry⟩
  | binaryZeroSchur tail hz hopen hres hall hne =>
      let E := S.toExactZeroThreeSchurClock
      have hsymm : E.zeroSeries.matrix.IsSymm := by
        simpa [E] using S.exactZeroThreeSchurClock_isSymm
      by_cases h0 : E.tailConstantMatrix 0 0 ≠ 0
      · let clock := E.toBinaryZeroSchurClockPivot0 hsymm hall h0
        refine ⟨.explicitBinary tail hz hopen hres
          (.pivot0 (by simpa [E] using hall) (by simpa [E] using hne)
            (by simpa [E] using h0) clock ?_ ?_)⟩
        · simpa [clock, E] using
            E.toBinaryZeroSchurClockPivot0_series hsymm hall h0
        · simpa [clock, E] using
            E.toBinaryZeroSchurClockPivot0_defect hsymm hall h0
      · have h0z : E.tailConstantMatrix 0 0 = 0 := by
          exact not_ne_iff.mp h0
        by_cases h1 : E.tailConstantMatrix 1 1 ≠ 0
        · let clock := E.toBinaryZeroSchurClockPivot1 hsymm hall h1
          refine ⟨.explicitBinary tail hz hopen hres
            (.pivot1 (by simpa [E] using hall) (by simpa [E] using hne)
              (by simpa [E] using h0z) (by simpa [E] using h1)
              clock ?_ ?_)⟩
          · simpa [clock, E] using
              E.toBinaryZeroSchurClockPivot1_series hsymm hall h1
          · simpa [clock, E] using
              E.toBinaryZeroSchurClockPivot1_defect hsymm hall h1
        · have h1z : E.tailConstantMatrix 1 1 = 0 := by
            exact not_ne_iff.mp h1
          have h2 : E.tailConstantMatrix 2 2 ≠ 0 := by
            rcases E.exists_diagonal_ne_zero_of_rankOne hsymm hall hne with
              ⟨p, hp⟩
            fin_cases p
            · exact (h0 hp).elim
            · exact (h1 hp).elim
            · exact hp
          let clock := E.toBinaryZeroSchurClockPivot2 hsymm hall h2
          refine ⟨.explicitBinary tail hz hopen hres
            (.pivot2 (by simpa [E] using hall) (by simpa [E] using hne)
              (by simpa [E] using h0z) (by simpa [E] using h1z)
              (by simpa [E] using h2) clock ?_ ?_)⟩
          · simpa [clock, E] using
              E.toBinaryZeroSchurClockPivot2_series hsymm hall h2
          · simpa [clock, E] using
              E.toBinaryZeroSchurClockPivot2_defect hsymm hall h2

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
