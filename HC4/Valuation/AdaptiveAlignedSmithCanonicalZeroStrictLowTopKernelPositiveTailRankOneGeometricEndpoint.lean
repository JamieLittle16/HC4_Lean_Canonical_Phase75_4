import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneEndpointSplit
import Mathlib.Tactic

/-!
# Source-point geometry for the positive-tail rank-one endpoint split

The source-honest rank-one endpoint split retains the exact first transverse
coefficient together with represented-source Schur provenance and the exact
whole-family first opening.

This file removes one more auxiliary layer.

* Preterminal: evaluate the nonzero off-diagonal coefficient at a source point.
  The kernel coefficient at the same order is zero, so the evaluated binary
  block has determinant `-b^2 != 0`.
* Exact closing: evaluate the forced nonzero kernel coefficient at a source
  point, retaining the represented-source and whole-family provenance.

No repair progress is introduced.
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

/-- Evaluate the exact first-transverse rank-one Schur block at one source
point. -/
noncomputable def PositiveTailExplicitRankOneClockData.firstTransverseBlock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B)
    (point : Fin 4 → K) : BinarySchurBlock K where
  a := MvPolynomial.eval point
    (R.exactRankOneClock.series.active.coeff R.exactRankOneClock.firstOrder)
  b := MvPolynomial.eval point
    (R.exactRankOneClock.series.offDiag.coeff R.exactRankOneClock.firstOrder)
  c := MvPolynomial.eval point
    (R.exactRankOneClock.series.kernel.coeff R.exactRankOneClock.firstOrder)

/-- Literal nondegenerate source-point event in the preterminal branch.

The determinant statement is geometric: it is the determinant of the evaluated
first-transverse binary Schur block, not a repair-state proxy. -/
structure PositiveTailRankOnePreterminalSourcePointGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) : Type (u + 1) where
  firstOrder_lt :
    R.exactRankOneClock.firstOrder < R.exactRankOneClock.defect
  kernelPolynomial_zero :
    R.exactRankOneClock.series.kernel.coeff
      R.exactRankOneClock.firstOrder = 0
  point : Fin 4 → K
  offDiagValue_ne :
    MvPolynomial.eval point
      (R.exactRankOneClock.series.offDiag.coeff
        R.exactRankOneClock.firstOrder) ≠ 0
  detCore_ne :
    (R.firstTransverseBlock point).detCore ≠ 0
  sourceGeometry :
    P.PositiveTailRankOneTransverseRepresentedSourceGeometry B
  wholeOpening :
    P.PositiveTailRankOneWholeFamilyFirstTransverseOpening R

/-- Literal source-point kernel crossing in the exact-closing branch. -/
structure PositiveTailRankOneClosingSourcePointGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) : Type (u + 1) where
  firstOrder_eq :
    R.exactRankOneClock.firstOrder = R.exactRankOneClock.defect
  kernelPolynomial_ne :
    R.exactRankOneClock.series.kernel.coeff
      R.exactRankOneClock.firstOrder ≠ 0
  point : Fin 4 → K
  kernelValue_ne :
    MvPolynomial.eval point
      (R.exactRankOneClock.series.kernel.coeff
        R.exactRankOneClock.firstOrder) ≠ 0
  sourceGeometry :
    P.PositiveTailRankOneTransverseRepresentedSourceGeometry B
  wholeOpening :
    P.PositiveTailRankOneWholeFamilyFirstTransverseOpening R

/-- Geometric endpoint of the exact positive-tail rank-one timing split. -/
inductive PositiveTailRankOneSourcePointGeometricEndpoint
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) : Type (u + 1)
  | preterminal
      (geometry : P.PositiveTailRankOnePreterminalSourcePointGeometry R)
  | exactClosing
      (geometry : P.PositiveTailRankOneClosingSourcePointGeometry R)

/-- The source-honest rank-one endpoint split always yields literal source-point
geometry. -/
theorem PositiveTailRankOneSourceHonestEndpointSplit.toSourcePointGeometricEndpoint
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    {R : P.PositiveTailExplicitRankOneClockData B}
    (E : P.PositiveTailRankOneSourceHonestEndpointSplit R) :
    Nonempty (P.PositiveTailRankOneSourcePointGeometricEndpoint R) := by
  cases E with
  | preterminal hpre hoff sourceGeometry wholeOpening =>
      have hkernel :
          R.exactRankOneClock.series.kernel.coeff
              R.exactRankOneClock.firstOrder = 0 :=
        R.exactRankOneClock.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre
      rcases exists_source_eval_ne_zero_of_ne_zero
          (R.exactRankOneClock.series.offDiag.coeff
            R.exactRankOneClock.firstOrder) hoff with
        ⟨point, hpoint⟩
      have hdetEq :
          (R.firstTransverseBlock point).detCore =
            -((R.firstTransverseBlock point).b *
              (R.firstTransverseBlock point).b) := by
        simp [PositiveTailExplicitRankOneClockData.firstTransverseBlock,
          BinarySchurBlock.detCore, hkernel]
      have hdet :
          (R.firstTransverseBlock point).detCore ≠ 0 := by
        rw [hdetEq]
        apply neg_ne_zero.mpr
        exact mul_ne_zero hpoint hpoint
      exact ⟨.preterminal {
        firstOrder_lt := hpre
        kernelPolynomial_zero := hkernel
        point := point
        offDiagValue_ne := hpoint
        detCore_ne := hdet
        sourceGeometry := sourceGeometry
        wholeOpening := wholeOpening
      }⟩
  | exactClosing hclose hkernel sourceGeometry wholeOpening =>
      rcases exists_source_eval_ne_zero_of_ne_zero
          (R.exactRankOneClock.series.kernel.coeff
            R.exactRankOneClock.firstOrder) hkernel with
        ⟨point, hpoint⟩
      exact ⟨.exactClosing {
        firstOrder_eq := hclose
        kernelPolynomial_ne := hkernel
        point := point
        kernelValue_ne := hpoint
        sourceGeometry := sourceGeometry
        wholeOpening := wholeOpening
      }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
