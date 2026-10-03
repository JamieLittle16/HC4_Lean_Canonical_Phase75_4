import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPositiveTailRankOneClock
import Mathlib.Tactic

/-!
# Assembly-facing exact relative-tail split for the top-kernel three-Schur seam

The tangent branch retains:

* `j`: the first physical raw Hessian kernel-row opening;
* `J`: the first strictly later projected kernel-column opening; and
* `q`: the common first positive order of the complete cleared 3x3 Schur
  quotient.

The existing tail packet already stores the exact relative order

    r = J - q.

For final assembly the clean split is therefore simply `r = 0` versus
`0 < r`.

* If `r > 0`, the entire positive-tail rank filtration is already available,
  including explicit binary-pivot and exact rank-one-clock provenance.
* If `r = 0`, the retained projected kernel opening occurs in the constant
  coefficient matrix of the normalised 3x3 tail itself.

This file introduces no new recurrence and no repair conclusion.
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

/-- Assembly-facing exact relative-tail frontier.

The zero branch retains the literal nonzero constant kernel-column entry.  The
positive branch immediately carries the already-developed lossless positive
rank filtration. -/
inductive TopKernelThreeSchurRelativeTailFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | zeroRelative
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (common_eq_later :
        tail.commonOrder = tail.physical.laterOrder)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
  | positiveRelative
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_pos : 0 < tail.relativeOrder)
      (frontier : P.TopKernelThreeSchurPositiveTailRankOneFrontier S)

/-- At zero relative order, the common 3x3 order is exactly the physical
later projected opening order. -/
theorem ThreeSchurTangentTailKernelOpeningData.commonOrder_eq_later_of_relativeOrder_eq_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hz : D.relativeOrder = 0) :
    D.commonOrder = D.physical.laterOrder := by
  have hrel := D.relativeOrder_eq
  rw [hz] at hrel
  have hle : D.physical.laterOrder ≤ D.commonOrder := by
    exact Nat.sub_eq_zero_iff_le.mp hrel.symm
  exact Nat.le_antisymm D.common_le_later hle

/-- At zero relative order, the retained projected kernel opening is already
nonzero in the constant matrix of the normalised 3x3 tail. -/
theorem ThreeSchurTangentTailKernelOpeningData.tailConstant_kernelOpening_ne_zero_of_relativeOrder_eq_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hz : D.relativeOrder = 0) :
    S.toExactZeroThreeSchurClock.tailConstantMatrix
      D.physical.index 2 ≠ 0 := by
  have hopen := D.opens
  rw [hz] at hopen
  simpa [ExactZeroThreeSchurClock.tailConstantMatrix] using hopen

/-- **Exact `r = J-q` assembly split.**

Every tangent first-break packet reaches either a zero-relative constant-tail
kernel opening or the already-complete positive-tail rank-one frontier. -/
theorem ThreeSchurTangentAtFirstBreak.relativeTailFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    Nonempty (P.TopKernelThreeSchurRelativeTailFrontier S M) := by
  rcases R.toLaterKernelOpeningData with ⟨L⟩
  rcases L.toTailKernelOpeningData with ⟨D⟩
  by_cases hz : D.relativeOrder = 0
  · exact ⟨.zeroRelative D hz
      (D.commonOrder_eq_later_of_relativeOrder_eq_zero hz)
      (D.tailConstant_kernelOpening_ne_zero_of_relativeOrder_eq_zero hz)⟩
  · have hpos : 0 < D.relativeOrder := Nat.pos_of_ne_zero hz
    rcases D.positiveTailRankOneFrontier hpos with ⟨F⟩
    exact ⟨.positiveRelative D hpos F⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
