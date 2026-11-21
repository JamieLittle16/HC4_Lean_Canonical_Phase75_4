import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurSecondStage
import Mathlib.Tactic

/-!
# Principal second-stage frontier for the top-kernel three-Schur clock

The generic singular-symmetric 3x3 lemma upgrades the rank-two constructor
of the previous frontier: because positive residual determinant order forces
the first tail constant matrix to be singular, any nonzero 2x2 minor implies
one of its three coordinate-principal 2x2 minors is nonzero.

Thus the exact 1+3 Schur filtration now has only:

1. determinant closure at the first 3x3 tail;
2. a literal principal rank-two pivot in that tail; or
3. an exact binary zero-Schur clock obtained from the rank-one tail.

No arbitrary-minor or rank-one 3x3 residual remains.
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

/-- Coordinate-principal rank-two pivot in the first normalised 3x3 tail. -/
inductive TopKernelThreeSchurPrincipalPivot
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Prop
  | pivot01
      (hne :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
            S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 ≠ 0)
  | pivot02
      (hne :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 -
            S.toExactZeroThreeSchurClock.tailConstantMatrix 0 2 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 2 0 ≠ 0)
  | pivot12
      (hne :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 -
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 2 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 2 1 ≠ 0)

/-- Fully principalised second-stage frontier. -/
inductive TopKernelThreeSchurPrincipalFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | determinantClosing
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)
  | rankTwoPrincipal
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (pivot : P.TopKernelThreeSchurPrincipalPivot S)
  | binaryZeroSchur
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (defect_eq :
        clock.defect =
          S.toExactZeroThreeSchurClock.residualDefect)

/-- Upgrade the previous finite Schur exhaustion to coordinate-principal
rank-two data. -/
theorem TopKernelThreeSchurClockData.principalFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    Nonempty (P.TopKernelThreeSchurPrincipalFrontier S) := by
  rcases S.secondStageFrontier with ⟨F⟩
  cases F with
  | determinantClosing hres hdet =>
      exact ⟨.determinantClosing hres hdet⟩
  | binaryZeroSchur hres clock hdef =>
      exact ⟨.binaryZeroSchur hres clock hdef⟩
  | rankTwo hres hminor =>
      let E := S.toExactZeroThreeSchurClock
      have hsymm : E.zeroSeries.matrix.IsSymm := by
        simpa [E] using S.exactZeroThreeSchurClock_isSymm
      rcases E.rankTwo_has_principalPivot hsymm hres hminor with
        h01 | h02 | h12
      · exact ⟨.rankTwoPrincipal hres (.pivot01 h01)⟩
      · exact ⟨.rankTwoPrincipal hres (.pivot02 h02)⟩
      · exact ⟨.rankTwoPrincipal hres (.pivot12 h12)⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
