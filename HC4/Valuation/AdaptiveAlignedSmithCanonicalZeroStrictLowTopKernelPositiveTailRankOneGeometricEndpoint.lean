import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneEndpointSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree
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

/-- Branch-independent represented-source Schur point witness.  This evaluates
one of the three nonzero represented-source Schur polynomials at a source point
where it remains nonzero. -/
inductive PositiveTailRepresentedSourceSchurPointWitness
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | schurA
      (pair : ThreeSchurActivePair)
      (point : Fin 4 → K)
      (value_ne :
        MvPolynomial.eval point
          (permutedPolynomialHessianFourBlock
            (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurA ≠ 0)
  | schurB
      (pair : ThreeSchurActivePair)
      (point : Fin 4 → K)
      (value_ne :
        MvPolynomial.eval point
          (permutedPolynomialHessianFourBlock
            (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurB ≠ 0)
  | schurC
      (pair : ThreeSchurActivePair)
      (point : Fin 4 → K)
      (value_ne :
        MvPolynomial.eval point
          (permutedPolynomialHessianFourBlock
            (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurC ≠ 0)

/-- Evaluate a branch-independent represented-source Schur witness. -/
theorem PositiveTailRepresentedSourceSchurWitness.exists_sourcePointWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (G : P.PositiveTailRepresentedSourceSchurWitness) :
    Nonempty P.PositiveTailRepresentedSourceSchurPointWitness := by
  cases G with
  | schurA pair hne =>
      rcases exists_source_eval_ne_zero_of_ne_zero
          (permutedPolynomialHessianFourBlock
            (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurA
          hne with ⟨point, hpoint⟩
      exact ⟨.schurA pair point hpoint⟩
  | schurB pair hne =>
      rcases exists_source_eval_ne_zero_of_ne_zero
          (permutedPolynomialHessianFourBlock
            (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurB
          hne with ⟨point, hpoint⟩
      exact ⟨.schurB pair point hpoint⟩
  | schurC pair hne =>
      rcases exists_source_eval_ne_zero_of_ne_zero
          (permutedPolynomialHessianFourBlock
            (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurC
          hne with ⟨point, hpoint⟩
      exact ⟨.schurC pair point hpoint⟩

/-- Forget the rank-one coefficient index and retain only the honest
represented-source Schur polynomial. -/
theorem PositiveTailRankOneTransverseRepresentedSourceGeometry.toRepresentedSourceWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (G : P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) :
    P.PositiveTailRepresentedSourceSchurWitness := by
  cases G with
  | schurA pair _ _ hsource =>
      exact .schurA pair hsource
  | schurB pair _ _ hsource =>
      exact .schurB pair hsource
  | schurC pair _ _ hsource =>
      exact .schurC pair hsource

/-- Evaluate the represented-source Schur geometry retained by a rank-one
transverse event. -/
theorem PositiveTailRankOneTransverseRepresentedSourceGeometry.exists_sourcePointWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (G : P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) :
    Nonempty P.PositiveTailRepresentedSourceSchurPointWitness :=
  G.toRepresentedSourceWitness.exists_sourcePointWitness

/-- Actual represented-source 3x3 Hessian-minor geometry at a source point.
The principal and mixed orientations are retained explicitly. -/
inductive PositiveTailRepresentedSourceThreeByThreePointGeometry
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | firstPrincipal
      (pair : ThreeSchurActivePair)
      (point : Fin 4 → K)
      (detValue_ne :
        MvPolynomial.eval point
          (HC4.Valuation.GeneralFourBlock.firstThreeMinorMatrix
            (permutedPolynomialHessianFourBlock
              (pair.sourcePerm kernelCoordinate) T.topKernelReesSource)).det ≠ 0)
  | mixed
      (pair : ThreeSchurActivePair)
      (point : Fin 4 → K)
      (detValue_ne :
        MvPolynomial.eval point
          (HC4.Valuation.GeneralFourBlock.mixedThreeMinorMatrix
            (permutedPolynomialHessianFourBlock
              (pair.sourcePerm kernelCoordinate) T.topKernelReesSource)).det ≠ 0)
  | secondPrincipal
      (pair : ThreeSchurActivePair)
      (point : Fin 4 → K)
      (detValue_ne :
        MvPolynomial.eval point
          (HC4.Valuation.GeneralFourBlock.secondThreeMinorMatrix
            (permutedPolynomialHessianFourBlock
              (pair.sourcePerm kernelCoordinate) T.topKernelReesSource)).det ≠ 0)

/-- A represented-source Schur point witness is literally an evaluated nonzero
3x3 Hessian minor of the represented special fibre. -/
noncomputable def PositiveTailRepresentedSourceSchurPointWitness.toThreeByThreePointGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (G : P.PositiveTailRepresentedSourceSchurPointWitness) :
    P.PositiveTailRepresentedSourceThreeByThreePointGeometry := by
  cases G with
  | schurA pair point hne =>
      refine .firstPrincipal pair point ?_
      rw [HC4.Valuation.GeneralFourBlock.firstThreeMinorMatrix_det]
      exact hne
  | schurB pair point hne =>
      refine .mixed pair point ?_
      rw [HC4.Valuation.GeneralFourBlock.mixedThreeMinorMatrix_det]
      exact hne
  | schurC pair point hne =>
      refine .secondPrincipal pair point ?_
      rw [HC4.Valuation.GeneralFourBlock.secondThreeMinorMatrix_det]
      exact hne

/-- Every branch-independent represented-source Schur witness therefore yields
literal evaluated 3x3 Hessian-minor geometry. -/
theorem PositiveTailRepresentedSourceSchurWitness.exists_threeByThreePointGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (G : P.PositiveTailRepresentedSourceSchurWitness) :
    Nonempty P.PositiveTailRepresentedSourceThreeByThreePointGeometry := by
  rcases G.exists_sourcePointWitness with ⟨W⟩
  exact ⟨W.toThreeByThreePointGeometry⟩

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
