import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurLaterKernelTail
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPrincipalFrontier
import Mathlib.Tactic

/-!
# Collapse the positive-tail tangent branch

Assume the tangent branch reaches the normalised 3x3 Schur tail with a
strictly positive projected kernel opening.  Then the complete constant
kernel column of that tail is zero.

The already-green principal second-stage frontier therefore collapses:

* determinant closing is impossible, because a matrix with a zero column has
  determinant zero;
* a principal rank-two pivot involving the kernel slot 2 is impossible;
* the only rank-two constant block is the active (0,1) principal block;
* otherwise the exact binary zero-Schur clock remains.

Thus the positive-tail branch is reduced to an active rank-two block or one
exact binary clock, with no 3x3 determinant-closing or kernel-involving
rank-two alternative left.
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

/-- Reduced second-stage frontier once the normalised tail kernel column has
strictly positive opening order. -/
inductive TopKernelThreeSchurPositiveTailFrontier
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
  | binaryZeroSchur
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (defect_eq :
        clock.defect =
          S.toExactZeroThreeSchurClock.residualDefect)

/-- Positive relative kernel opening kills the constant kernel column of the
normalised tail. -/
theorem ThreeSchurTangentTailKernelOpeningData.tailConstant_kernelColumn_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentTailKernelOpeningData M)
    (hpos : 0 < D.relativeOrder) :
    ∀ i : Fin 3,
      S.toExactZeroThreeSchurClock.tailConstantMatrix i 2 = 0 := by
  intro i
  have hz := D.lower_zero i 0 hpos
  simpa [ExactZeroThreeSchurClock.tailConstantMatrix] using hz

/-- **Positive-tail 3x3 collapse.** -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentTailKernelOpeningData M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty P.TopKernelThreeSchurPositiveTailFrontier S := by
  let E := S.toExactZeroThreeSchurClock
  let C := E.tailConstantMatrix
  have hcol : ∀ i : Fin 3, C i 2 = 0 := by
    intro i
    simpa [C, E] using D.tailConstant_kernelColumn_zero hpos i
  have hsymm : C.IsSymm := by
    simpa [C, E] using
      E.tailConstantMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have h20 : C 2 0 = 0 := by rw [hsymm 2 0, hcol 0]
  have h21 : C 2 1 = 0 := by rw [hsymm 2 1, hcol 1]
  have h22 : C 2 2 = 0 := hcol 2
  have hdet0 : C.det = 0 := by
    simp [Matrix.det_fin_three, hcol 0, hcol 1, h22, h20, h21]

  rcases S.principalFrontier with ⟨F⟩
  cases F with
  | determinantClosing hres hdet =>
      exfalso
      apply hdet
      simpa [C, E] using hdet0

  | binaryZeroSchur hres clock hdef =>
      exact ⟨.binaryZeroSchur hres clock hdef⟩

  | rankTwoPrincipal hres pivot =>
      cases pivot with
      | pivot01 h01 =>
          exact ⟨.activeRankTwo hres h01⟩
      | pivot02 h02 =>
          exfalso
          apply h02
          have h02c :
              E.tailConstantMatrix 0 2 = 0 := by
            simpa [C, E] using hcol 0
          have h20c :
              E.tailConstantMatrix 2 0 = 0 := by
            simpa [C, E] using h20
          have h22c :
              E.tailConstantMatrix 2 2 = 0 := by
            simpa [C, E] using h22
          rw [h02c, h20c, h22c]
          ring
      | pivot12 h12 =>
          exfalso
          apply h12
          have h12c :
              E.tailConstantMatrix 1 2 = 0 := by
            simpa [C, E] using hcol 1
          have h21c :
              E.tailConstantMatrix 2 1 = 0 := by
            simpa [C, E] using h21
          have h22c :
              E.tailConstantMatrix 2 2 = 0 := by
            simpa [C, E] using h22
          rw [h12c, h21c, h22c]
          ring

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
