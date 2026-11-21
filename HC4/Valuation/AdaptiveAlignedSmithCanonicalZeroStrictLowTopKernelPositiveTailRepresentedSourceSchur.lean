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

private theorem pair02Block_ofSymmetricMatrix_submatrix
    (M : Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)))
    (hsymm : M.IsSymm) :
    (GeneralFourBlock.ofSymmetricMatrix M).pair02Block =
      GeneralFourBlock.ofSymmetricMatrix
        (M.submatrix (Equiv.swap (1 : Fin 4) 2)
          (Equiv.swap (1 : Fin 4) 2)) := by
  have h0 : (Equiv.swap (1 : Fin 4) 2) 0 = 0 := by native_decide
  have h1 : (Equiv.swap (1 : Fin 4) 2) 1 = 2 := by native_decide
  have h2 : (Equiv.swap (1 : Fin 4) 2) 2 = 1 := by native_decide
  have h3 : (Equiv.swap (1 : Fin 4) 2) 3 = 3 := by native_decide
  have h12 : M 1 2 = M 2 1 := by
    have h := congrArg
      (fun N : Matrix (Fin 4) (Fin 4)
        (Polynomial (MvPolynomial (Fin 4) K)) => N 2 1)
      hsymm
    simpa using h
  apply GeneralFourBlock.ext
  · change M 0 0 = M ((Equiv.swap (1 : Fin 4) 2) 0) ((Equiv.swap (1 : Fin 4) 2) 0)
    rw [h0]
  · change M 0 2 = M ((Equiv.swap (1 : Fin 4) 2) 0) ((Equiv.swap (1 : Fin 4) 2) 1)
    rw [h0, h1]
  · change M 2 2 = M ((Equiv.swap (1 : Fin 4) 2) 1) ((Equiv.swap (1 : Fin 4) 2) 1)
    rw [h1]
  · change M 0 1 = M ((Equiv.swap (1 : Fin 4) 2) 0) ((Equiv.swap (1 : Fin 4) 2) 2)
    rw [h0, h2]
  · change M 0 3 = M ((Equiv.swap (1 : Fin 4) 2) 0) ((Equiv.swap (1 : Fin 4) 2) 3)
    rw [h0, h3]
  · change M 1 2 = M ((Equiv.swap (1 : Fin 4) 2) 1) ((Equiv.swap (1 : Fin 4) 2) 2)
    rw [h1, h2]
    exact h12
  · change M 2 3 = M ((Equiv.swap (1 : Fin 4) 2) 1) ((Equiv.swap (1 : Fin 4) 2) 3)
    rw [h1, h3]
  · change M 1 1 = M ((Equiv.swap (1 : Fin 4) 2) 2) ((Equiv.swap (1 : Fin 4) 2) 2)
    rw [h2]
  · change M 1 3 = M ((Equiv.swap (1 : Fin 4) 2) 2) ((Equiv.swap (1 : Fin 4) 2) 3)
    rw [h2, h3]
  · change M 3 3 = M ((Equiv.swap (1 : Fin 4) 2) 3) ((Equiv.swap (1 : Fin 4) 2) 3)
    rw [h3]

private theorem pair12Block_ofSymmetricMatrix_submatrix
    (M : Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)))
    (hsymm : M.IsSymm) :
    (GeneralFourBlock.ofSymmetricMatrix M).pair12Block =
      GeneralFourBlock.ofSymmetricMatrix
        (M.submatrix
          ((Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1))
          ((Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1))) := by
  let sigma : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)
  have h0 : sigma 0 = 1 := by native_decide
  have h1 : sigma 1 = 2 := by native_decide
  have h2 : sigma 2 = 0 := by native_decide
  have h3 : sigma 3 = 3 := by native_decide
  have h01 : M 0 1 = M 1 0 := by
    have h := congrArg
      (fun N : Matrix (Fin 4) (Fin 4)
        (Polynomial (MvPolynomial (Fin 4) K)) => N 1 0)
      hsymm
    simpa using h
  have h02 : M 0 2 = M 2 0 := by
    have h := congrArg
      (fun N : Matrix (Fin 4) (Fin 4)
        (Polynomial (MvPolynomial (Fin 4) K)) => N 2 0)
      hsymm
    simpa using h
  change
    (GeneralFourBlock.ofSymmetricMatrix M).pair12Block =
      GeneralFourBlock.ofSymmetricMatrix (M.submatrix sigma sigma)
  apply GeneralFourBlock.ext
  · change M 1 1 = M (sigma 0) (sigma 0)
    rw [h0]
  · change M 1 2 = M (sigma 0) (sigma 1)
    rw [h0, h1]
  · change M 2 2 = M (sigma 1) (sigma 1)
    rw [h1]
  · change M 0 1 = M (sigma 0) (sigma 2)
    rw [h0, h2]
    exact h01
  · change M 1 3 = M (sigma 0) (sigma 3)
    rw [h0, h3]
  · change M 0 2 = M (sigma 1) (sigma 2)
    rw [h1, h2]
    exact h02
  · change M 2 3 = M (sigma 1) (sigma 3)
    rw [h1, h3]
  · change M 0 0 = M (sigma 2) (sigma 2)
    rw [h2]
  · change M 0 3 = M (sigma 2) (sigma 3)
    rw [h2, h3]
  · change M 3 3 = M (sigma 3) (sigma 3)
    rw [h3]

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
  let rho := kernelLastPerm kernelCoordinate
  let M :=
    (parameterFirstHessian T.topKernelReverseReesFamily).submatrix rho rho
  have hsymm : M.IsSymm := by
    apply Matrix.ext
    intro i j
    exact parameterFirstHessian_symmetric
      T.topKernelReverseReesFamily (rho j) (rho i)
  cases pair with
  | pair01 =>
      change
        GeneralFourBlock.ofSymmetricMatrix M =
          GeneralFourBlock.ofSymmetricMatrix M
      rfl
  | pair02 =>
      change
        (GeneralFourBlock.ofSymmetricMatrix M).pair02Block =
          GeneralFourBlock.ofSymmetricMatrix
            (M.submatrix (Equiv.swap (1 : Fin 4) 2)
              (Equiv.swap (1 : Fin 4) 2))
      exact pair02Block_ofSymmetricMatrix_submatrix M hsymm
  | pair12 =>
      change
        (GeneralFourBlock.ofSymmetricMatrix M).pair12Block =
          GeneralFourBlock.ofSymmetricMatrix
            (M.submatrix
              ((Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1))
              ((Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)))
      exact pair12Block_ofSymmetricMatrix_submatrix M hsymm

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
  · refine PositiveTailBinaryRepresentedSourceSchurGeometry.schurA D.pair ?_
    apply D.pair.sourceSchurA_ne_zero_of_familySchurA_ne_zero (P := P)
    apply D.schurA_ne_zero_of_active_ne_zero
    intro hz
    apply hA
    rw [hz]
    simp
  · refine PositiveTailBinaryRepresentedSourceSchurGeometry.schurB D.pair ?_
    apply D.pair.sourceSchurB_ne_zero_of_familySchurB_ne_zero (P := P)
    apply D.schurB_ne_zero_of_offDiag_ne_zero
    intro hz
    apply hB
    rw [hz]
    simp
  · refine PositiveTailBinaryRepresentedSourceSchurGeometry.schurC D.pair ?_
    apply D.pair.sourceSchurC_ne_zero_of_familySchurC_ne_zero (P := P)
    apply D.schurC_ne_zero_of_kernel_ne_zero
    intro hz
    apply hC
    rw [hz]
    simp

/-- Branch-independent represented-source Schur witness for the positive-tail
seam.  Unlike `PositiveTailBinaryRepresentedSourceSchurGeometry`, this record
does not retain an auxiliary binary clock index; it remembers only the honest
source-coordinate pair and one nonzero cleared 2+2 Schur polynomial. -/
inductive PositiveTailRepresentedSourceSchurWitness
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Prop
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

/-- Forget only the auxiliary binary-clock index from already source-honest
positive-tail Schur geometry. -/
theorem PositiveTailBinaryRepresentedSourceSchurGeometry.toRepresentedSourceWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (G : P.PositiveTailBinaryRepresentedSourceSchurGeometry B) :
    P.PositiveTailRepresentedSourceSchurWitness := by
  cases G with
  | schurA pair hne =>
      exact PositiveTailRepresentedSourceSchurWitness.schurA pair hne
  | schurB pair hne =>
      exact PositiveTailRepresentedSourceSchurWitness.schurB pair hne
  | schurC pair hne =>
      exact PositiveTailRepresentedSourceSchurWitness.schurC pair hne

/-- Every explicit positive-tail binary clock therefore already determines a
branch-independent honest represented-source Schur witness.  In particular,
this consumes the later binary determinant-closing alternative source-honestly;
the determinant-closing hypotheses add terminal information but are not needed
for this source lift. -/
theorem PositiveTailExplicitBinaryClockData.representedSourceSchurWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) :
    P.PositiveTailRepresentedSourceSchurWitness :=
  B.representedSourceSchurGeometry.toRepresentedSourceWitness

/-- A nonzero active principal 2x2 minor in the normalised positive
three-Schur tail already forces an honest represented-source Schur polynomial
to be nonzero.  This is the source-honest consumer for the
`activeRankTwo` positive-tail alternative. -/
theorem TopKernelThreeSchurClockData.activeRankTwo_representedSourceSchurWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (h01 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
          S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 ≠ 0) :
    P.PositiveTailRepresentedSourceSchurWitness := by
  let E := S.toExactZeroThreeSchurClock
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hsymmM : M.IsSymm :=
    E.tailMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have hm := h01
  change
    (M 0 0).coeff 0 * (M 1 1).coeff 0 -
        (M 0 1).coeff 0 * (M 1 0).coeff 0 ≠ 0 at hm
  have hM10 : M 1 0 = M 0 1 := by
    have h := congrArg
      (fun N : Matrix (Fin 3) (Fin 3)
          (Polynomial (MvPolynomial (Fin 4) K)) => N 0 1)
      hsymmM
    simpa using h
  have hs : (M 1 0).coeff 0 = (M 0 1).coeff 0 :=
    congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hM10
  rw [hs] at hm
  have htailCoeff :
      (threePivot0BinarySchurSeries M).active.coeff 0 ≠ 0 := by
    simpa [threePivot0BinarySchurSeries,
      Polynomial.coeff_zero_eq_eval_zero] using hm
  have htail :
      (threePivot0BinarySchurSeries M).active ≠ 0 := by
    intro hz
    apply htailCoeff
    rw [hz]
    simp
  have hraw :
      (threePivot0BinarySchurSeries E.zeroSeries.matrix).active ≠ 0 := by
    rw [show E.zeroSeries.matrix =
        commonScaleThreeMatrix
          ((Polynomial.X :
            Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder)
          M by
        simpa [E, M] using S.zeroSeries_eq_commonScale_tail]
    rw [threePivot0BinarySchurSeries_commonScale_active]
    exact mul_ne_zero
      (pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero))
      htail
  cases S with
  | pivotA ha hzero hdet =>
      have hprod :
          P.threeSchurBlock.a * P.threeSchurBlock.schurA ≠ 0 := by
        rw [← P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrix_active]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur : P.threeSchurBlock.schurA ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurA
        .pair01
        (ThreeSchurActivePair.sourceSchurA_ne_zero_of_familySchurA_ne_zero
          (T := T) (P := P) .pair01 hschur)
  | pivotD hd hzero hdet =>
      have hprod :
          P.threeSchurBlock.d * P.threeSchurBlock.schurA ≠ 0 := by
        rw [← P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixD_active]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur : P.threeSchurBlock.schurA ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurA
        .pair01
        (ThreeSchurActivePair.sourceSchurA_ne_zero_of_familySchurA_ne_zero
          (T := T) (P := P) .pair01 hschur)
  | pivotX hx hzero hdet =>
      have hprod :
          P.threeSchurBlock.x *
              (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurA ≠ 0 := by
        change
          P.threeSchurBlock.x * P.threeSchurBlock.pair02Block.schurA ≠ 0
        rw [← P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixX_active]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur :
          (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurA ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurA
        .pair02
        (ThreeSchurActivePair.sourceSchurA_ne_zero_of_familySchurA_ne_zero
          (T := T) (P := P) .pair02 hschur)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
