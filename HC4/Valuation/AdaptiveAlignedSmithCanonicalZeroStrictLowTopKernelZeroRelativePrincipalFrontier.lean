import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurRelativeTailFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPrincipalFrontier
import Mathlib.Tactic

/-!
# Finite principal frontier for the zero-relative top-kernel three-Schur tail

At relative order zero the retained later projected kernel opening is already
present in the constant matrix of the normalised 3x3 Schur tail.  No new
staircase is required.

This file runs the existing principal second-stage frontier directly and keeps
the zero-relative physical provenance in every branch.  The resulting finite
alternatives are exactly:

* determinant closure of the constant 3x3 tail;
* one of the three coordinate-principal rank-two pivots;
* an exact binary zero-Schur clock from the rank-one constant tail.

No source-lift or terminal claim is made here; those are the next finite
consumers.
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

/-- Orientation of the exact binary zero-Schur clock extracted from a
rank-one normalised 3x3 tail.  The all-minors certificate is an index of the
datum, so the selected diagonal pivot and the resulting clock cannot drift
apart downstream. -/
inductive TopKernelThreeSchurRankOneOrientedBinaryClock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (allMinors :
      ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
        S.toExactZeroThreeSchurClock.tailConstantMatrix) : Type (u + 1)
  | pivot0
      (hne :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 ≠ 0)
  | pivot1
      (hne :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 ≠ 0)
  | pivot2
      (hne :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 ≠ 0)

namespace TopKernelThreeSchurRankOneOrientedBinaryClock

/-- The exact orientation-preserving binary clock selected by the retained
diagonal pivot. -/
noncomputable def exactClock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {allMinors :
      ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
        S.toExactZeroThreeSchurClock.tailConstantMatrix}
    (B : P.TopKernelThreeSchurRankOneOrientedBinaryClock S allMinors) :
    ExactZeroSchurClock (MvPolynomial (Fin 4) K) := by
  let E := S.toExactZeroThreeSchurClock
  have hsymm : E.zeroSeries.matrix.IsSymm := by
    simpa [E] using S.exactZeroThreeSchurClock_isSymm
  cases B with
  | pivot0 hne =>
      exact E.toBinaryZeroSchurClockPivot0 hsymm
        (by simpa [E] using allMinors)
        (by simpa [E] using hne)
  | pivot1 hne =>
      exact E.toBinaryZeroSchurClockPivot1 hsymm
        (by simpa [E] using allMinors)
        (by simpa [E] using hne)
  | pivot2 hne =>
      exact E.toBinaryZeroSchurClockPivot2 hsymm
        (by simpa [E] using allMinors)
        (by simpa [E] using hne)

/-- The oriented binary clock keeps exactly the residual determinant defect of
the three-Schur clock. -/
@[simp] theorem exactClock_defect
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {allMinors :
      ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
        S.toExactZeroThreeSchurClock.tailConstantMatrix}
    (B : P.TopKernelThreeSchurRankOneOrientedBinaryClock S allMinors) :
    B.exactClock.defect =
      S.toExactZeroThreeSchurClock.residualDefect := by
  cases B <;> rfl

end TopKernelThreeSchurRankOneOrientedBinaryClock

/-- Exact finite second-stage alternatives in the zero-relative branch,
retaining the physical constant kernel opening that selected this branch. -/
inductive TopKernelThreeSchurZeroRelativePrincipalFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | determinantClosing
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (common_eq_later : tail.commonOrder = tail.physical.laterOrder)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)
  | rankTwoPrincipal
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (common_eq_later : tail.commonOrder = tail.physical.laterOrder)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (pivot : P.TopKernelThreeSchurPrincipalPivot S)
  | binaryZeroSchur
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (common_eq_later : tail.commonOrder = tail.physical.laterOrder)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (allMinors :
        ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
          S.toExactZeroThreeSchurClock.tailConstantMatrix)
      (matrix_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix ≠ 0)
      (orientedClock :
        P.TopKernelThreeSchurRankOneOrientedBinaryClock S allMinors)

/-- **D1: zero-relative finite principal exhaustion.**

The existing principal second-stage frontier applies without modification; the
only work here is to retain the exact physical zero-relative provenance in
every constructor. -/
theorem ThreeSchurTangentTailKernelOpeningData.zeroRelativePrincipalFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hz : D.relativeOrder = 0) :
    Nonempty (P.TopKernelThreeSchurZeroRelativePrincipalFrontier S M) := by
  have hcommon := D.commonOrder_eq_later_of_relativeOrder_eq_zero hz
  have hopen :=
    D.tailConstant_kernelOpening_ne_zero_of_relativeOrder_eq_zero hz
  let E := S.toExactZeroThreeSchurClock
  have hsymm : E.zeroSeries.matrix.IsSymm := by
    simpa [E] using S.exactZeroThreeSchurClock_isSymm
  cases E.firstTailRankFrontier with
  | determinantClosing hres hdet =>
      exact ⟨.determinantClosing D hz hcommon hopen
        (by simpa [E] using hres) (by simpa [E] using hdet)⟩
  | rankTwo hres hminor =>
      have hres' : 0 < S.toExactZeroThreeSchurClock.residualDefect := by
        simpa [E] using hres
      rcases E.rankTwo_has_principalPivot hsymm hres hminor with
        h01 | h02 | h12
      · exact ⟨.rankTwoPrincipal D hz hcommon hopen hres' (.pivot01 (by simpa [E] using h01))⟩
      · exact ⟨.rankTwoPrincipal D hz hcommon hopen hres' (.pivot02 (by simpa [E] using h02))⟩
      · exact ⟨.rankTwoPrincipal D hz hcommon hopen hres' (.pivot12 (by simpa [E] using h12))⟩
  | rankOne hres hall hne =>
      have hall' :
          ExactZeroThreeSchurClock.AllTwoByTwoMinorsZero
            S.toExactZeroThreeSchurClock.tailConstantMatrix := by
        simpa [E] using hall
      have hne' :
          S.toExactZeroThreeSchurClock.tailConstantMatrix ≠ 0 := by
        simpa [E] using hne
      have horiented :
          P.TopKernelThreeSchurRankOneOrientedBinaryClock S hall' := by
        rcases E.exists_diagonal_ne_zero_of_rankOne hsymm hall hne with
          ⟨p, hp⟩
        fin_cases p
        · exact .pivot0 (by simpa [E] using hp)
        · exact .pivot1 (by simpa [E] using hp)
        · exact .pivot2 (by simpa [E] using hp)
      exact ⟨.binaryZeroSchur D hz hcommon hopen
        (by simpa [E] using hres) hall' hne' horiented⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
