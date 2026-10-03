import HC4.Newton.NestedRankOneThreeSchurPairOrientations
import HC4.Newton.NestedRankOneThreeSchurTailScaling
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPositiveTailRankOneClock
import Mathlib.Tactic

/-!
# Whole-family Schur provenance for the positive top-kernel binary clock

The positive three-Schur tail performs two scalar Schur eliminations among the
three non-kernel coordinates.  The resulting exact binary zero-Schur clock is
built from the *normalised* 3x3 tail, after the common first three-Schur
factor has been removed.

This file reconnects that binary clock to the honest whole reverse-Rees
Hessian four-block.

For the selected active coordinate pair, every binary clock entry satisfies

    firstPivot * wholeFamilyPairSchurEntry
      = (X^q)^2 * binaryClockEntry,

where q is the common first 3x3 Schur order and the first scalar pivot has
nonzero constant coefficient.

Thus nonvanishing in the binary clock is not auxiliary algebra: it forces
nonvanishing of an actual whole-family cleared Schur polynomial in one of the
three coordinate-pair charts.
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

/-- The three possible active coordinate pairs among the kernel-last slots
0,1,2. -/
inductive ThreeSchurActivePair
  | pair01
  | pair02
  | pair12
deriving DecidableEq

/-- Display the honest kernel-last Hessian four-block with the selected active
pair first and the kernel coordinate still last. -/
noncomputable def ThreeSchurActivePair.block
    (pair : ThreeSchurActivePair)
    (H : GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K))) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  match pair with
  | .pair01 => H
  | .pair02 => H.pair02Block
  | .pair12 => H.pair12Block

/-- The raw zero-constant 3x3 quotient is the common first factor times its
normalised tail, entrywise. -/
theorem TopKernelThreeSchurClockData.zeroSeries_eq_commonScale_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    S.toExactZeroThreeSchurClock.zeroSeries.matrix =
      commonScaleThreeMatrix
        ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder)
        (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
          S.toExactZeroThreeSchurClock.hasPositiveEntryLayer) := by
  apply Matrix.ext
  intro i j
  have h :=
    S.toExactZeroThreeSchurClock.zeroSeries.entry_eq_firstFactor_mul_tail
      S.toExactZeroThreeSchurClock.hasPositiveEntryLayer i j
  simpa [TopKernelThreeSchurClockData.firstThreeSchurOrder,
    commonScaleThreeMatrix] using h

private theorem pivot0_raw_active_eq_scaled_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    (threePivot0BinarySchurSeries
      S.toExactZeroThreeSchurClock.zeroSeries.matrix).active =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        (threePivot0BinarySchurSeries
          (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
            S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)).active := by
  rw [S.zeroSeries_eq_commonScale_tail]
  exact threePivot0BinarySchurSeries_commonScale_active _ _

private theorem pivot0_raw_offDiag_eq_scaled_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    (threePivot0BinarySchurSeries
      S.toExactZeroThreeSchurClock.zeroSeries.matrix).offDiag =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        (threePivot0BinarySchurSeries
          (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
            S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)).offDiag := by
  rw [S.zeroSeries_eq_commonScale_tail]
  exact threePivot0BinarySchurSeries_commonScale_offDiag _ _

private theorem pivot0_raw_kernel_eq_scaled_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    (threePivot0BinarySchurSeries
      S.toExactZeroThreeSchurClock.zeroSeries.matrix).kernel =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        (threePivot0BinarySchurSeries
          (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
            S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)).kernel := by
  rw [S.zeroSeries_eq_commonScale_tail]
  exact threePivot0BinarySchurSeries_commonScale_kernel _ _

private theorem pivot1_raw_active_eq_scaled_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    (threePivot1BinarySchurSeries
      S.toExactZeroThreeSchurClock.zeroSeries.matrix).active =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        (threePivot1BinarySchurSeries
          (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
            S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)).active := by
  rw [S.zeroSeries_eq_commonScale_tail]
  exact threePivot1BinarySchurSeries_commonScale_active _ _

private theorem pivot1_raw_offDiag_eq_scaled_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    (threePivot1BinarySchurSeries
      S.toExactZeroThreeSchurClock.zeroSeries.matrix).offDiag =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        (threePivot1BinarySchurSeries
          (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
            S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)).offDiag := by
  rw [S.zeroSeries_eq_commonScale_tail]
  exact threePivot1BinarySchurSeries_commonScale_offDiag _ _

private theorem pivot1_raw_kernel_eq_scaled_tail
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    (threePivot1BinarySchurSeries
      S.toExactZeroThreeSchurClock.zeroSeries.matrix).kernel =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        (threePivot1BinarySchurSeries
          (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
            S.toExactZeroThreeSchurClock.hasPositiveEntryLayer)).kernel := by
  rw [S.zeroSeries_eq_commonScale_tail]
  exact threePivot1BinarySchurSeries_commonScale_kernel _ _

/-- Source-facing provenance of one explicit positive-tail binary clock. -/
structure PositiveTailBinaryWholeFamilySchurProvenance
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) : Type (u + 1) where
  pair : ThreeSchurActivePair
  firstPivot :
    Polynomial (MvPolynomial (Fin 4) K)
  firstPivot_coeff_zero_ne_zero :
    firstPivot.coeff 0 ≠ 0
  active_eq :
    firstPivot *
        (pair.block P.threeSchurBlock).schurA =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        B.exactClock.zeroSeries.series.active
  offDiag_eq :
    firstPivot *
        (pair.block P.threeSchurBlock).schurB =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        B.exactClock.zeroSeries.series.offDiag
  kernel_eq :
    firstPivot *
        (pair.block P.threeSchurBlock).schurC =
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 *
        B.exactClock.zeroSeries.series.kernel

/-- Every explicit binary clock retains exact whole-family Schur provenance
for the corresponding pair of non-kernel coordinates. -/
theorem PositiveTailExplicitBinaryClockData.wholeFamilySchurProvenance
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) :
    Nonempty (P.PositiveTailBinaryWholeFamilySchurProvenance B) := by
  cases B with
  | pivot0 hp clock hseries hdef =>
      cases S with
      | pivotA ha hzero hdet =>
          refine ⟨{
            pair := .pair01
            firstPivot := P.threeSchurBlock.a
            firstPivot_coeff_zero_ne_zero := ha
            active_eq := ?_
            offDiag_eq := ?_
            kernel_eq := ?_
          }⟩
          · calc
              P.threeSchurBlock.a * P.threeSchurBlock.schurA =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrix).active := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrix_active
              _ = _ := by
                    exact pivot0_raw_active_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotA ha hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.a * P.threeSchurBlock.schurB =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrix).offDiag := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrix_offDiag
              _ = _ := by
                    exact pivot0_raw_offDiag_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotA ha hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.a * P.threeSchurBlock.schurC =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrix).kernel := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrix_kernel
              _ = _ := by
                    exact pivot0_raw_kernel_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotA ha hzero hdet)
              _ = _ := by rw [← hseries]; rfl
      | pivotD hd hzero hdet =>
          refine ⟨{
            pair := .pair01
            firstPivot := P.threeSchurBlock.d
            firstPivot_coeff_zero_ne_zero := hd
            active_eq := ?_
            offDiag_eq := ?_
            kernel_eq := ?_
          }⟩
          · calc
              P.threeSchurBlock.d * P.threeSchurBlock.schurA =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixD).active := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixD_active
              _ = _ := by
                    exact pivot0_raw_active_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotD hd hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.d * P.threeSchurBlock.schurB =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixD).offDiag := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixD_offDiag
              _ = _ := by
                    exact pivot0_raw_offDiag_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotD hd hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.d * P.threeSchurBlock.schurC =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixD).kernel := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixD_kernel
              _ = _ := by
                    exact pivot0_raw_kernel_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotD hd hzero hdet)
              _ = _ := by rw [← hseries]; rfl
      | pivotX hx hzero hdet =>
          refine ⟨{
            pair := .pair02
            firstPivot := P.threeSchurBlock.x
            firstPivot_coeff_zero_ne_zero := hx
            active_eq := ?_
            offDiag_eq := ?_
            kernel_eq := ?_
          }⟩
          · calc
              P.threeSchurBlock.x *
                    (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurA =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixX).active := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixX_active
              _ = _ := by
                    exact pivot0_raw_active_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotX hx hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.x *
                    (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurB =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixX).offDiag := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixX_offDiag
              _ = _ := by
                    exact pivot0_raw_offDiag_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotX hx hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.x *
                    (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurC =
                  (threePivot0BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixX).kernel := by
                    symm
                    exact P.threeSchurBlock.threePivot0_rankOneClearedThreeSchurMatrixX_kernel
              _ = _ := by
                    exact pivot0_raw_kernel_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotX hx hzero hdet)
              _ = _ := by rw [← hseries]; rfl

  | pivot1 hp clock hseries hdef =>
      cases S with
      | pivotA ha hzero hdet =>
          refine ⟨{
            pair := .pair02
            firstPivot := P.threeSchurBlock.a
            firstPivot_coeff_zero_ne_zero := ha
            active_eq := ?_
            offDiag_eq := ?_
            kernel_eq := ?_
          }⟩
          · calc
              P.threeSchurBlock.a *
                    (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurA =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrix).active := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrix_active
              _ = _ := by
                    exact pivot1_raw_active_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotA ha hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.a *
                    (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurB =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrix).offDiag := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrix_offDiag
              _ = _ := by
                    exact pivot1_raw_offDiag_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotA ha hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.a *
                    (ThreeSchurActivePair.pair02.block P.threeSchurBlock).schurC =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrix).kernel := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrix_kernel
              _ = _ := by
                    exact pivot1_raw_kernel_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotA ha hzero hdet)
              _ = _ := by rw [← hseries]; rfl
      | pivotD hd hzero hdet =>
          refine ⟨{
            pair := .pair12
            firstPivot := P.threeSchurBlock.d
            firstPivot_coeff_zero_ne_zero := hd
            active_eq := ?_
            offDiag_eq := ?_
            kernel_eq := ?_
          }⟩
          · calc
              P.threeSchurBlock.d *
                    (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurA =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixD).active := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixD_active
              _ = _ := by
                    exact pivot1_raw_active_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotD hd hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.d *
                    (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurB =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixD).offDiag := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixD_offDiag
              _ = _ := by
                    exact pivot1_raw_offDiag_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotD hd hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.d *
                    (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurC =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixD).kernel := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixD_kernel
              _ = _ := by
                    exact pivot1_raw_kernel_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotD hd hzero hdet)
              _ = _ := by rw [← hseries]; rfl
      | pivotX hx hzero hdet =>
          refine ⟨{
            pair := .pair12
            firstPivot := P.threeSchurBlock.x
            firstPivot_coeff_zero_ne_zero := hx
            active_eq := ?_
            offDiag_eq := ?_
            kernel_eq := ?_
          }⟩
          · calc
              P.threeSchurBlock.x *
                    (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurA =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixX).active := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixX_active
              _ = _ := by
                    exact pivot1_raw_active_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotX hx hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.x *
                    (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurB =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixX).offDiag := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixX_offDiag
              _ = _ := by
                    exact pivot1_raw_offDiag_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotX hx hzero hdet)
              _ = _ := by rw [← hseries]; rfl
          · calc
              P.threeSchurBlock.x *
                    (ThreeSchurActivePair.pair12.block P.threeSchurBlock).schurC =
                  (threePivot1BinarySchurSeries
                    P.threeSchurBlock.rankOneClearedThreeSchurMatrixX).kernel := by
                    symm
                    exact P.threeSchurBlock.threePivot1_rankOneClearedThreeSchurMatrixX_kernel
              _ = _ := by
                    exact pivot1_raw_kernel_eq_scaled_tail
                      (TopKernelThreeSchurClockData.pivotX hx hzero hdet)
              _ = _ := by rw [← hseries]; rfl

/-- A nonzero active entry of the explicit binary zero-Schur clock forces the
corresponding honest whole-family Schur polynomial to be nonzero. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.schurA_ne_zero_of_active_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hne : B.exactClock.zeroSeries.series.active ≠ 0) :
    (D.pair.block P.threeSchurBlock).schurA ≠ 0 := by
  intro hz
  have hleft : D.firstPivot * (D.pair.block P.threeSchurBlock).schurA = 0 := by
    rw [hz]
    simp
  rw [D.active_eq] at hleft
  have hx :
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero)
  exact hne ((mul_eq_zero.mp hleft).resolve_left hx)

/-- The same source-honest lift for the off-diagonal binary entry. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.schurB_ne_zero_of_offDiag_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hne : B.exactClock.zeroSeries.series.offDiag ≠ 0) :
    (D.pair.block P.threeSchurBlock).schurB ≠ 0 := by
  intro hz
  have hleft : D.firstPivot * (D.pair.block P.threeSchurBlock).schurB = 0 := by
    rw [hz]
    simp
  rw [D.offDiag_eq] at hleft
  have hx :
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero)
  exact hne ((mul_eq_zero.mp hleft).resolve_left hx)

/-- The same source-honest lift for the binary kernel entry. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.schurC_ne_zero_of_kernel_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hne : B.exactClock.zeroSeries.series.kernel ≠ 0) :
    (D.pair.block P.threeSchurBlock).schurC ≠ 0 := by
  intro hz
  have hleft : D.firstPivot * (D.pair.block P.threeSchurBlock).schurC = 0 := by
    rw [hz]
    simp
  rw [D.kernel_eq] at hleft
  have hx :
      ((Polynomial.X :
          Polynomial (MvPolynomial (Fin 4) K)) ^ S.firstThreeSchurOrder) ^ 2 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero)
  exact hne ((mul_eq_zero.mp hleft).resolve_left hx)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
