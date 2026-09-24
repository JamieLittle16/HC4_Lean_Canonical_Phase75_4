import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativePrincipalSourceLift
import HC4.Newton.RankOneThreeToBinarySchur
import Mathlib.Tactic

/-!
# Orientation-preserving binary clock for the zero-relative tail

At relative order zero the retained physical opening is already a nonzero entry
in column 2 of the constant normalised 3x3 tail.  In the remaining rank-one
case all 2x2 minors vanish.  Symmetry then forces the diagonal entry (2,2) to
be nonzero: if it vanished, the principal minor on the opened row and
coordinate 2 would force the retained column-2 entry to vanish as well.

Thus this branch has a canonical second scalar pivot: coordinate 2.  We retain
that pivot and construct the exact coordinate-2 binary zero-Schur clock through
the public oriented Newton API.  No arbitrary pivot choice, repair progress, or
terminal claim is introduced.
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

/-- In a symmetric rank-one constant 3x3 tail, a nonzero entry in column 2
forces the (2,2) diagonal pivot to be nonzero. -/
theorem TopKernelThreeSchurClockData.pivot2_ne_zero_of_rankOne_column2_opening
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (hall :
      ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
        S.toExactZeroThreeSchurClock.tailConstantMatrix)
    {i : Fin 3}
    (hopen :
      S.toExactZeroThreeSchurClock.tailConstantMatrix i 2 ≠ 0) :
    S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 ≠ 0 := by
  let E := S.toExactZeroThreeSchurClock
  let C := E.tailConstantMatrix
  have hsymm : E.zeroSeries.matrix.IsSymm := by
    simpa [E] using S.exactZeroThreeSchurClock_isSymm
  have hCsymm : C.IsSymm := E.tailConstantMatrix_isSymm hsymm
  intro h22
  have hm := hall i i 2 2
  change C i i * C 2 2 - C i 2 * C 2 i = 0 at hm
  have hs : C 2 i = C i 2 := by
    have h := congrArg
      (fun N : Matrix (Fin 3) (Fin 3)
        (MvPolynomial (Fin 4) K) => N 2 i)
      hCsymm
    simpa using h
  have hsq : C i 2 * C i 2 = 0 := by
    rw [h22, hs] at hm
    simpa using hm
  rcases mul_eq_zero.mp hsq with hz | hz
  · exact hopen (by simpa [E, C] using hz)
  · exact hopen (by simpa [E, C] using hz)

/-- Exact coordinate-2 binary clock together with the rank-one 3x3 witness
and the physical pivot that constructed it. -/
structure ZeroRelativeExplicitBinaryClockData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1) where
  allMinors :
    ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
      S.toExactZeroThreeSchurClock.tailConstantMatrix
  matrix_ne_zero :
    S.toExactZeroThreeSchurClock.tailConstantMatrix ≠ 0
  pivot2_ne_zero :
    S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 ≠ 0
  clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K)
  series_eq :
    clock.zeroSeries.series =
      threePivot2BinarySchurSeries
        (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
          S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)
  defect_eq :
    clock.defect = S.toExactZeroThreeSchurClock.residualDefect

/-- Zero-relative source frontier with the remaining rank-one branch converted
to its canonical coordinate-2 exact binary clock. -/
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

/-- **D3: rank-one constant tail -> explicit coordinate-2 binary clock.**

The retained physical column-2 opening selects the diagonal pivot itself, so
this step is finite and canonical. -/
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
      have h2 :
          S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 ≠ 0 :=
        S.pivot2_ne_zero_of_rankOne_column2_opening hall hopen
      let clock := E.toBinaryZeroSchurClockPivot2
        hsymm (by simpa [E] using hall) (by simpa [E] using h2)
      have hseries :
          clock.zeroSeries.series =
            threePivot2BinarySchurSeries
              (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
                S.toExactZeroThreeSchurClock.hasPositiveEntryLayer) := by
        simpa [clock, E] using
          E.toBinaryZeroSchurClockPivot2_series
            hsymm (by simpa [E] using hall) (by simpa [E] using h2)
      have hdefect :
          clock.defect =
            S.toExactZeroThreeSchurClock.residualDefect := by
        simpa [clock, E] using
          E.toBinaryZeroSchurClockPivot2_defect
            hsymm (by simpa [E] using hall) (by simpa [E] using h2)
      exact ⟨.explicitBinary tail hz hopen hres
        {
          allMinors := hall
          matrix_ne_zero := hne
          pivot2_ne_zero := h2
          clock := clock
          series_eq := hseries
          defect_eq := hdefect
        }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
