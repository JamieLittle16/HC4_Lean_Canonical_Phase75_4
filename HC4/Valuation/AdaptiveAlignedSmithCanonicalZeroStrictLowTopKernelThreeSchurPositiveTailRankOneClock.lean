import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPositiveTailBinaryProvenance
import Mathlib.Tactic

/-!
# Lossless third Schur stage for the positive tangent tail

The preceding file retains the exact active coordinate pivot used to turn the
normalised 3x3 rank-one tail into a binary zero-Schur clock.

This file refuses the generic repair wrapper at the next stage. For that
literal binary clock there are only two determinant-theoretic possibilities:

* its residual determinant order is zero, so the first normalised binary
  coefficient block is already nondegenerate;
* positive residual remains, so the nonzero determinant-zero constant block
  has a literal left or right-axis rank-one pivot. The existing exact
  constructors then give an exact rank-one Schur clock on the same binary
  series.

Thus the positive 3x3 tangent tail reaches either an explicit rank-two
coefficient block or a literal final rank-one Schur clock, with all pivot
provenance retained and no repair conclusion substituted for geometry.
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

/-- The binary clock stored in explicit active-pivot provenance. -/
noncomputable def PositiveTailExplicitBinaryClockData.exactClock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) :
    ExactZeroSchurClock (MvPolynomial (Fin 4) K) :=
  match B with
  | .pivot0 _ clock _ _ => clock
  | .pivot1 _ clock _ _ => clock

/-- Orientation of the rank-one binary tail after one further exact clock
factor is removed. -/
inductive PositiveTailExplicitRankOneClockData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) : Type (u + 1)
  | left
      (residual_pos : 0 < B.exactClock.residualDefect)
      (pivot : B.exactClock.tailSeries.LeftPivot)
      (clock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (clock_eq : clock = B.exactClock.toRankOneClockLeft residual_pos pivot)
  | right
      (residual_pos : 0 < B.exactClock.residualDefect)
      (pivot : B.exactClock.tailSeries.RightAxisPivot)
      (clock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (clock_eq : clock = B.exactClock.toRankOneClockRight residual_pos pivot)

/-- Fully lossless positive-tail rank filtration through the binary stage. -/
inductive TopKernelThreeSchurPositiveTailRankOneFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | activeRankTwo
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (pivot01 :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
            S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 ≠ 0)
  | binaryDeterminantClosing
      (threeResidual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (binaryResidual_eq_zero :
        binary.exactClock.residualDefect = 0)
      (binaryTail_det_ne_zero :
        binary.exactClock.tailSeries.active.coeff 0 *
              binary.exactClock.tailSeries.kernel.coeff 0 -
            binary.exactClock.tailSeries.offDiag.coeff 0 *
              binary.exactClock.tailSeries.offDiag.coeff 0 ≠ 0)
  | rankOneClock
      (threeResidual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)

/-- Positive binary residual produces a literal oriented rank-one exact clock. -/
theorem PositiveTailExplicitBinaryClockData.toRankOneClockData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S)
    (hres : 0 < B.exactClock.residualDefect) :
    Nonempty (P.PositiveTailExplicitRankOneClockData B) := by
  rcases B.exactClock.tail_pivot_of_residual_pos hres with hleft | hright
  · let R := B.exactClock.toRankOneClockLeft hres hleft
    exact ⟨.left hres hleft R rfl⟩
  · let R := B.exactClock.toRankOneClockRight hres hright
    exact ⟨.right hres hright R rfl⟩

/-- Third-stage positive-tail frontier without repair metadata. -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailRankOneFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentTailKernelOpeningData M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty P.TopKernelThreeSchurPositiveTailRankOneFrontier S := by
  rcases D.positiveTailDetailedFrontier hpos with ⟨F⟩
  cases F with
  | activeRankTwo hres h01 =>
      exact ⟨.activeRankTwo hres h01⟩
  | binaryZeroSchur hres B =>
      by_cases hzero : B.exactClock.residualDefect = 0
      · exact ⟨.binaryDeterminantClosing
          hres B hzero
          (B.exactClock.tail_constant_det_ne_zero_of_residual_zero hzero)⟩
      · have hposB : 0 < B.exactClock.residualDefect :=
          Nat.pos_of_ne_zero hzero
        rcases B.toRankOneClockData hposB with ⟨R⟩
        exact ⟨.rankOneClock hres B R⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
