import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerE2Frontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneGeometricEndpoint
import Mathlib.Tactic

/-!
# E2: collapse the relative three-Schur tail to source rank-three geometry

The C/D source frontier has one residual family indexed by the exact relative
order of the later kernel opening.  Almost all of that family is already
literal represented-source geometry:

* every positive-relative represented-Schur branch is an evaluated nonzero
  source 3x3 Hessian minor;
* the positive-relative rank-one endpoint still retains the same represented
  source Schur witness, hence the same 3x3 minor;
* in the zero-relative branch, a represented Schur witness gives the same
  source-point geometry;
* a zero-relative actual-rank-two chart becomes an exact-active chart, and at
  the literal zero-defect represented state the generic zero-Schur alternative
  is impossible, leaving a nonzero constant 3x3 minor.

Consequently only one algebraic residual remains: zero-relative determinant
closure of the first normalised 3x3 Schur tail.  This file isolates that
constructor exactly; no terminal conclusion is added.
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

/-- Source-facing form of the complete relative-tail analysis. -/
inductive TopKernelThreeSchurRelativeSourceRankThreeFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | sourcePointThreeByThree
      (geometry : P.PositiveTailRepresentedSourceThreeByThreePointGeometry)
  | sourceConstantThreeByThree
      (chart :
        AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented)
      (geometry :
        AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry chart)
  | zeroRelativeDeterminantClosing
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)

/-- A positive-tail rank-one endpoint still contains the represented-source
Schur witness from which it was obtained, so it too gives an evaluated source
3x3 Hessian minor. -/
theorem PositiveTailRankOneSourcePointGeometricEndpoint.exists_sourceThreeByThree
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    {R : P.PositiveTailExplicitRankOneClockData B}
    (G : P.PositiveTailRankOneSourcePointGeometricEndpoint R) :
    Nonempty P.PositiveTailRepresentedSourceThreeByThreePointGeometry := by
  cases G with
  | preterminal E =>
      rcases E.sourceGeometry.exists_sourcePointWitness with ⟨W⟩
      exact ⟨W.toThreeByThreePointGeometry⟩
  | exactClosing E =>
      rcases E.sourceGeometry.exists_sourcePointWitness with ⟨W⟩
      exact ⟨W.toThreeByThreePointGeometry⟩

/-- Every positive-relative geometric endpoint has literal represented-source
3x3 Hessian-minor geometry. -/
theorem TopKernelThreeSchurPositiveTailGeometricFrontier.exists_sourceThreeByThree
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (G : P.TopKernelThreeSchurPositiveTailGeometricFrontier S) :
    Nonempty P.PositiveTailRepresentedSourceThreeByThreePointGeometry := by
  cases G with
  | representedThreeByThree H =>
      exact ⟨H⟩
  | rankOneSourcePoint _binary _rankOne H =>
      exact H.exists_sourceThreeByThree

/-- **Relative-tail source reduction.**

All positive-relative branches and two of the three zero-relative branches
already reach honest represented-source rank-three Hessian geometry.  The
single remaining constructor is the exact zero-relative determinant-closing
tail. -/
theorem TopKernelThreeSchurRelativeGeometricFrontier.toSourceRankThreeFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (G : P.TopKernelThreeSchurRelativeGeometricFrontier S M) :
    Nonempty (P.TopKernelThreeSchurRelativeSourceRankThreeFrontier S M) := by
  cases G with
  | positiveRelative _tail _hpos H =>
      rcases H.exists_sourceThreeByThree with ⟨Q⟩
      exact ⟨.sourcePointThreeByThree Q⟩
  | zeroRelative _tail _hz H =>
      cases H with
      | determinantClosing tail hz hopen hres hdet =>
          exact ⟨.zeroRelativeDeterminantClosing
            tail hz hopen hres hdet⟩
      | representedSchur _tail _hz _hopen source =>
          rcases source.exists_threeByThreePointGeometry with ⟨Q⟩
          exact ⟨.sourcePointThreeByThree Q⟩
      | actualRankTwo _tail _hz _hopen A =>
          let C :
              AdaptiveAlignedSmithCanonicalExactActiveFourBlock
                T.terminal.blocker.presented :=
            AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect A
          rcases P.exactActive_threeByThree_of_presentedZero C with ⟨Q⟩
          exact ⟨.sourceConstantThreeByThree C Q⟩


/-- A nonzero constant tail entry in the zero-relative closing branch lifts
back through the common first three-Schur factor to an honest represented-
source Hessian minor, hence to an exact-active source chart. -/
theorem zeroRelativeClosing_exactActiveFourBlock
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
    (tail : ThreeSchurTangentTailKernelOpeningData S M)
    (hopen :
      S.toExactZeroThreeSchurClock.tailConstantMatrix
        tail.physical.index 2 ≠ 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalExactActiveFourBlock
        T.terminal.blocker.presented) := by
  let E := S.toExactZeroThreeSchurClock
  have htail :
      (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
        tail.physical.index 2).coeff 0 ≠ 0 := by
    simpa [E, ExactZeroThreeSchurClock.tailConstantMatrix] using hopen
  have hraw :
      (E.zeroSeries.matrix tail.physical.index 2).coeff
        S.firstThreeSchurOrder ≠ 0 := by
    have ht := E.zeroSeries.entry_coeff_first_add_eq_tail
      E.hasPositiveEntryLayer tail.physical.index 2 0
    have hfirst :
        E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer =
          S.firstThreeSchurOrder := by
      rfl
    rw [hfirst] at ht
    simp only [Nat.add_zero] at ht
    rw [ht]
    exact htail
  rcases P.sourceTwoByTwoMinor_of_threeSchurEntry_coeff_ne_zero
      S tail.physical.index 2 S.firstThreeSchurOrder
      (by simpa [E] using hraw) with
    ⟨a, b, c, d, hm⟩
  apply exactActiveFourBlock_of_specialFiber_twoByTwoMinor_ne_zero
    T.terminal.blocker.presented a b c d
  simpa [topKernelReesSource] using hm

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
