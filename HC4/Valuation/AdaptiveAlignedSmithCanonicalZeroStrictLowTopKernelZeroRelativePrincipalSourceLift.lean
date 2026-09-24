import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativePrincipalFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRepresentedSourceSchur
import Mathlib.Tactic

/-!
# Source lift of zero-relative principal rank-two pivots

The zero-relative finite frontier retains all three coordinate-principal 2x2
pivots of the normalised 3x3 Schur tail.  The positive-tail source lift already
handles the (0,1) pivot.  The other two pivots are the kernel entries of the
same nested binary Schur constructions:

* (0,2) is the kernel of the coordinate-0 nested binary quotient;
* (1,2) is the kernel of the coordinate-1 nested binary quotient.

The common-tail scaling identities and the nested four-block identities
therefore lift both alternatives to nonzero represented-source Schur-C
polynomials in the correct pair chart.

No rank label is identified with a terminal polynomial endpoint.
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

/-- The (0,2) principal pivot in the normalised 3x3 tail lifts to an honest
represented-source Schur-C polynomial. -/
theorem TopKernelThreeSchurClockData.pivot02_representedSourceSchurWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (h02 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 -
          S.toExactZeroThreeSchurClock.tailConstantMatrix 0 2 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 2 0 ≠ 0) :
    P.PositiveTailRepresentedSourceSchurWitness := by
  let E := S.toExactZeroThreeSchurClock
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hsymmM : M.IsSymm :=
    E.tailMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have hm := h02
  change
    (M 0 0).coeff 0 * (M 2 2).coeff 0 -
        (M 0 2).coeff 0 * (M 2 0).coeff 0 ≠ 0 at hm
  have hM20 : M 2 0 = M 0 2 := by
    have h := congrArg
      (fun N : Matrix (Fin 3) (Fin 3)
          (Polynomial (MvPolynomial (Fin 4) K)) => N 0 2)
      hsymmM
    simpa using h
  have hs : (M 2 0).coeff 0 = (M 0 2).coeff 0 :=
    congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hM20
  rw [hs] at hm
  have htailCoeff :
      (threePivot0BinarySchurSeries M).kernel.coeff 0 ≠ 0 := by
    simpa [threePivot0BinarySchurSeries,
      Polynomial.coeff_zero_eq_eval_zero] using hm
  have htail :
      (threePivot0BinarySchurSeries M).kernel ≠ 0 := by
    intro hz
    apply htailCoeff
    rw [hz]
    simp
  have hraw :
      (threePivot0BinarySchurSeries E.zeroSeries.matrix).kernel ≠ 0 := by
    rw [show E.zeroSeries.matrix =
        commonScaleThreeMatrix
          ((Polynomial.X :
            Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder)
          M by
        simpa [E, M] using S.zeroSeries_eq_commonScale_tail]
    rw [threePivot0BinarySchurSeries_commonScale_kernel]
    exact mul_ne_zero
      (pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero))
      htail
  cases S with
  | pivotA ha hzero hdet =>
      have hprod :
          P.threeSchurBlock.a * P.threeSchurBlock.schurC ≠ 0 := by
        rw [← P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrix_kernel]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur : P.threeSchurBlock.schurC ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurC
        .pair01
        (ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
          (T := T) (P := P) .pair01 hschur)
  | pivotD hd hzero hdet =>
      have hprod :
          P.threeSchurBlock.d * P.threeSchurBlock.schurC ≠ 0 := by
        rw [← P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixD_kernel]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur : P.threeSchurBlock.schurC ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurC
        .pair01
        (ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
          (T := T) (P := P) .pair01 hschur)
  | pivotX hx hzero hdet =>
      have hprod :
          P.threeSchurBlock.x *
              (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurC ≠ 0 := by
        change
          P.threeSchurBlock.x * P.threeSchurBlock.pair02Block.schurC ≠ 0
        rw [← P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixX_kernel]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur :
          (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurC ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurC
        .pair02
        (ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
          (T := T) (P := P) .pair02 hschur)

/-- The (1,2) principal pivot in the normalised 3x3 tail lifts to an honest
represented-source Schur-C polynomial in the corresponding pair chart. -/
theorem TopKernelThreeSchurClockData.pivot12_representedSourceSchurWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (h12 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 -
          S.toExactZeroThreeSchurClock.tailConstantMatrix 1 2 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 2 1 ≠ 0) :
    P.PositiveTailRepresentedSourceSchurWitness := by
  let E := S.toExactZeroThreeSchurClock
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hsymmM : M.IsSymm :=
    E.tailMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have hm := h12
  change
    (M 1 1).coeff 0 * (M 2 2).coeff 0 -
        (M 1 2).coeff 0 * (M 2 1).coeff 0 ≠ 0 at hm
  have hM21 : M 2 1 = M 1 2 := by
    have h := congrArg
      (fun N : Matrix (Fin 3) (Fin 3)
          (Polynomial (MvPolynomial (Fin 4) K)) => N 1 2)
      hsymmM
    simpa using h
  have hs : (M 2 1).coeff 0 = (M 1 2).coeff 0 :=
    congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hM21
  rw [hs] at hm
  have htailCoeff :
      (threePivot1BinarySchurSeries M).kernel.coeff 0 ≠ 0 := by
    simpa [threePivot1BinarySchurSeries,
      Polynomial.coeff_zero_eq_eval_zero] using hm
  have htail :
      (threePivot1BinarySchurSeries M).kernel ≠ 0 := by
    intro hz
    apply htailCoeff
    rw [hz]
    simp
  have hraw :
      (threePivot1BinarySchurSeries E.zeroSeries.matrix).kernel ≠ 0 := by
    rw [show E.zeroSeries.matrix =
        commonScaleThreeMatrix
          ((Polynomial.X :
            Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder)
          M by
        simpa [E, M] using S.zeroSeries_eq_commonScale_tail]
    rw [threePivot1BinarySchurSeries_commonScale_kernel]
    exact mul_ne_zero
      (pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero))
      htail
  cases S with
  | pivotA ha hzero hdet =>
      have hprod :
          P.threeSchurBlock.a *
              (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurC ≠ 0 := by
        change
          P.threeSchurBlock.a * P.threeSchurBlock.pair02Block.schurC ≠ 0
        rw [← P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrix_kernel]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur :
          (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurC ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurC
        .pair02
        (ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
          (T := T) (P := P) .pair02 hschur)
  | pivotD hd hzero hdet =>
      have hprod :
          P.threeSchurBlock.d *
              (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurC ≠ 0 := by
        change
          P.threeSchurBlock.d * P.threeSchurBlock.pair12Block.schurC ≠ 0
        rw [← P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixD_kernel]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur :
          (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurC ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurC
        .pair12
        (ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
          (T := T) (P := P) .pair12 hschur)
  | pivotX hx hzero hdet =>
      have hprod :
          P.threeSchurBlock.x *
              (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurC ≠ 0 := by
        change
          P.threeSchurBlock.x * P.threeSchurBlock.pair12Block.schurC ≠ 0
        rw [← P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixX_kernel]
        simpa [E, TopKernelThreeSchurClockData.toExactZeroThreeSchurClock]
          using hraw
      have hschur :
          (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurC ≠ 0 := by
        intro hz
        apply hprod
        rw [hz]
        simp
      exact PositiveTailRepresentedSourceSchurWitness.schurC
        .pair12
        (ThreeSchurActivePair.sourceSchurC_ne_zero_of_familySchurC_ne_zero
          (T := T) (P := P) .pair12 hschur)

/-- Every coordinate-principal rank-two pivot of the zero-relative constant
3x3 tail is therefore source-honest. -/
theorem TopKernelThreeSchurPrincipalPivot.toRepresentedSourceSchurWitness
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (pivot : P.TopKernelThreeSchurPrincipalPivot S) :
    P.PositiveTailRepresentedSourceSchurWitness := by
  cases pivot with
  | pivot01 h01 =>
      exact S.activeRankTwo_representedSourceSchurWitness h01
  | pivot02 h02 =>
      exact S.pivot02_representedSourceSchurWitness h02
  | pivot12 h12 =>
      exact S.pivot12_representedSourceSchurWitness h12

/-- Zero-relative finite frontier after source-honest consumption of every
principal rank-two branch. -/
inductive TopKernelThreeSchurZeroRelativeSourceFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | determinantClosing
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)
  | representedSchur
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (geometry : P.PositiveTailRepresentedSourceSchurWitness)
  | binaryZeroSchur
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
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

/-- **D2: source-honest consumption of every zero-relative principal
rank-two branch.** -/
theorem TopKernelThreeSchurZeroRelativePrincipalFrontier.toSourceFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (F : P.TopKernelThreeSchurZeroRelativePrincipalFrontier S M) :
    Nonempty (P.TopKernelThreeSchurZeroRelativeSourceFrontier S M) := by
  cases F with
  | determinantClosing tail hz _hcommon hopen hres hdet =>
      exact ⟨.determinantClosing tail hz hopen hres hdet⟩
  | rankTwoPrincipal tail hz _hcommon hopen _hres pivot =>
      exact ⟨.representedSchur tail hz hopen
        pivot.toRepresentedSourceSchurWitness⟩
  | binaryZeroSchur tail hz _hcommon hopen hres hall hne oriented =>
      exact ⟨.binaryZeroSchur tail hz hopen hres hall hne oriented⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
