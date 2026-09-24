import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailWholeFamilySchurProvenance
import HC4.Valuation.ReverseWeightedReesSchurNonvanishingLift
import HC4.Valuation.PermutedFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# Represented-source Schur provenance for the positive three-Schur tail

The preceding file reconnects every explicit positive-tail binary clock to one
whole-family 2+2 Schur chart of the honest ordinary reverse-Rees Hessian.
This file identifies those three charts with literal coordinate permutations
of the reverse-Rees family and applies the generic nonvanishing lift back to
the represented determinant-one source.

No parameter order is identified with the blocker clock and no repair
transition is introduced.
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

/-- Reordering of the three non-kernel kernel-last slots for one active pair. -/
def ThreeSchurActivePair.slotPerm : ThreeSchurActivePair → Equiv.Perm (Fin 4)
  | .pair01 => Equiv.refl (Fin 4)
  | .pair02 => Equiv.swap (1 : Fin 4) 2
  | .pair12 =>
      (Equiv.swap (1 : Fin 4) 2).trans
        (Equiv.swap (0 : Fin 4) 1)

/-- Actual source-coordinate permutation for one pair chart: reorder the
kernel-last slots and then map them back to the original source coordinates. -/
def ThreeSchurActivePair.sourcePerm
    (pair : ThreeSchurActivePair)
    (kernelCoordinate : Fin 4) : Equiv.Perm (Fin 4) :=
  pair.slotPerm.trans (kernelLastPerm kernelCoordinate)

/-- The pair chart used by nested Schur elimination is literally the genuine
parameter-first Hessian four-block in the corresponding source-coordinate
permutation. -/
theorem ThreeSchurActivePair.block_threeSchurBlock_eq_permutedFamily
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (pair : ThreeSchurActivePair) :
    pair.block P.threeSchurBlock =
      permutedFamilyHessianFourBlock
        (pair.sourcePerm kernelCoordinate)
        T.topKernelReverseReesFamily := by
  cases pair <;>
    ext <;>
    simp [ThreeSchurActivePair.block, ThreeSchurActivePair.slotPerm,
      ThreeSchurActivePair.sourcePerm,
      GeneralFourBlock.pair02Block, GeneralFourBlock.pair12Block,
      threeSchurBlock, kernelLastFamilyHessianFourBlock,
      kernelLastParameterFirstHessian, permutedFamilyHessianFourBlock,
      kernelLastPerm]

private theorem ordinary_schurA_loss_le
    (pair : ThreeSchurActivePair) :
    reverseReesSchurALoss ordinaryTopNatWeight
        (pair.sourcePerm kernelCoordinate) ≤
      3 * T.topFace.degree := by
  have hD := T.topFace.degree_ge_three
  simp [reverseReesSchurALoss, ordinaryTopNatWeight]
  omega

private theorem ordinary_schurB_loss_le
    (pair : ThreeSchurActivePair) :
    reverseReesSchurBLoss ordinaryTopNatWeight
        (pair.sourcePerm kernelCoordinate) ≤
      3 * T.topFace.degree := by
  have hD := T.topFace.degree_ge_three
  simp [reverseReesSchurBLoss, ordinaryTopNatWeight]
  omega

private theorem ordinary_schurC_loss_le
    (pair : ThreeSchurActivePair) :
    reverseReesSchurCLoss ordinaryTopNatWeight
        (pair.sourcePerm kernelCoordinate) ≤
      3 * T.topFace.degree := by
  have hD := T.topFace.degree_ge_three
  simp [reverseReesSchurCLoss, ordinaryTopNatWeight]
  omega

/-- A nonzero whole-family Schur A in one pair chart is already a nonzero
Schur A polynomial of the represented source in the same chart. -/
theorem ThreeSchurActivePair.sourceSchurA_ne_zero_of_familySchurA_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (pair : ThreeSchurActivePair)
    (hne : (pair.block P.threeSchurBlock).schurA ≠ 0) :
    (permutedPolynomialHessianFourBlock
      (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurA ≠ 0 := by
  have hfamily :
      (permutedFamilyHessianFourBlock
        (pair.sourcePerm kernelCoordinate)
        T.topKernelReverseReesFamily).schurA ≠ 0 := by
    rw [← pair.block_threeSchurBlock_eq_permutedFamily (P := P)]
    exact hne
  exact
    reverseWeightedReesFamily_sourceSchurA_of_familySchurA_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      (pair.sourcePerm kernelCoordinate)
      (ordinary_schurA_loss_le (T := T) (kernelCoordinate := kernelCoordinate) pair)
      (by
        simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReverseReesFamily]
          using hfamily)

/-- Source lift for the off-diagonal Schur B polynomial. -/
theorem ThreeSchurActivePair.sourceSchurB_ne_zero_of_familySchurB_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (pair : ThreeSchurActivePair)
    (hne : (pair.block P.threeSchurBlock).schurB ≠ 0) :
    (permutedPolynomialHessianFourBlock
      (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurB ≠ 0 := by
  have hfamily :
      (permutedFamilyHessianFourBlock
        (pair.sourcePerm kernelCoordinate)
        T.topKernelReverseReesFamily).schurB ≠ 0 := by
    rw [← pair.block_threeSchurBlock_eq_permutedFamily (P := P)]
    exact hne
  exact
    reverseWeightedReesFamily_sourceSchurB_of_familySchurB_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      (pair.sourcePerm kernelCoordinate)
      (ordinary_schurB_loss_le (T := T) (kernelCoordinate := kernelCoordinate) pair)
      (by
        simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReverseReesFamily]
          using hfamily)

/-- Source lift for the Schur C polynomial. -/
theorem ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (pair : ThreeSchurActivePair)
    (hne : (pair.block P.threeSchurBlock).schurC ≠ 0) :
    (permutedPolynomialHessianFourBlock
      (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurC ≠ 0 := by
  have hfamily :
      (permutedFamilyHessianFourBlock
        (pair.sourcePerm kernelCoordinate)
        T.topKernelReverseReesFamily).schurC ≠ 0 := by
    rw [← pair.block_threeSchurBlock_eq_permutedFamily (P := P)]
    exact hne
  exact
    reverseWeightedReesFamily_sourceSchurC_of_familySchurC_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      (pair.sourcePerm kernelCoordinate)
      (ordinary_schurC_loss_le (T := T) (kernelCoordinate := kernelCoordinate) pair)
      (by
        simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReverseReesFamily]
          using hfamily)

/-- Honest represented-source Schur geometry obtained from one positive-tail
binary clock. -/
inductive PositiveTailBinaryRepresentedSourceSchurGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) : Prop
  | schurA
      (pair : ThreeSchurActivePair)
      (hne :
        (permutedPolynomialHessianFourBlock
          (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurA ≠ 0)
  | schurB
      (pair : ThreeSchurActivePair)
      (hne :
        (permutedPolynomialHessianFourBlock
          (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurB ≠ 0)
  | schurC
      (pair : ThreeSchurActivePair)
      (hne :
        (permutedPolynomialHessianFourBlock
          (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurC ≠ 0)

/-- Every positive-tail binary clock yields a genuine nonzero cleared Schur
polynomial on the represented determinant-one source. -/
theorem PositiveTailExplicitBinaryClockData.representedSourceSchurGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) :
    P.PositiveTailBinaryRepresentedSourceSchurGeometry B := by
  rcases B.wholeFamilySchurProvenance with ⟨D⟩
  let E := B.exactClock
  have hpositive := E.hasPositiveEntryLayer
  have hnonzero :=
    E.zeroSeries.entry_nonzero_at_first hpositive
  rcases hnonzero with hA | hB | hC
  · apply .schurA D.pair
    apply D.pair.sourceSchurA_ne_zero_of_familySchurA_ne_zero (P := P)
    apply D.schurA_ne_zero_of_active_ne_zero
    intro hz
    apply hA
    rw [hz]
    simp
  · apply .schurB D.pair
    apply D.pair.sourceSchurB_ne_zero_of_familySchurB_ne_zero (P := P)
    apply D.schurB_ne_zero_of_offDiag_ne_zero
    intro hz
    apply hB
    rw [hz]
    simp
  · apply .schurC D.pair
    apply D.pair.sourceSchurC_ne_zero_of_familySchurC_ne_zero (P := P)
    apply D.schurC_ne_zero_of_kernel_ne_zero
    intro hz
    apply hC
    rw [hz]
    simp

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
