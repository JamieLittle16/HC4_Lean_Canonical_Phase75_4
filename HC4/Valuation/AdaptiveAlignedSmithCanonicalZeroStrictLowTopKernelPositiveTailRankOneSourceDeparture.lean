import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRepresentedSourceSchur
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPositiveTailRankOneClock
import Mathlib.Tactic

/-!
# Source-honest first transverse departure of the positive-tail rank-one clock

The positive three-Schur tail now retains both pieces that were previously
separated:

* the exact oriented rank-one binary Schur clock; and
* exact whole-family / represented-source provenance for the binary Schur
  entries.

This file joins them at the *first transverse coefficient* of the final
rank-one clock.

For a left alignment, a nonzero aligned off-diagonal coefficient forces one
of the raw binary tail active/off-diagonal coefficients to be nonzero; a
nonzero aligned kernel coefficient forces one of all three raw tail
coefficients to be nonzero.  For a right-axis alignment the corresponding
statements are immediate.

The zero-Schur tail-to-raw coefficient identities put that event back at the
literal physical binary-clock order, and the whole-family provenance then
lifts the corresponding Schur polynomial to the represented determinant-one
source.

No repair transition is used as a conclusion.
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

/-- The literal exact rank-one clock stored by an oriented positive-tail
rank-one packet. -/
noncomputable def PositiveTailExplicitRankOneClockData.exactRankOneClock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) :
    ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K) :=
  match R with
  | .left _ _ clock _ => clock
  | .right _ _ clock _ => clock

/-- A first transverse rank-one-clock event transported all the way back to
one honest represented-source Schur polynomial.  The raw coefficient is
retained at its physical order in the *un-normalised binary zero-Schur
series*, namely binary first order plus the transverse tail order. -/
inductive PositiveTailRankOneTransverseRepresentedSourceGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) : Type (u + 1)
  | schurA
      (pair : ThreeSchurActivePair)
      (tailOrder : ℕ)
      (rawCoeff_ne :
        B.exactClock.zeroSeries.series.active.coeff
          (B.exactClock.firstOrder + tailOrder) ≠ 0)
      (source_ne :
        (permutedPolynomialHessianFourBlock
          (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurA ≠ 0)
  | schurB
      (pair : ThreeSchurActivePair)
      (tailOrder : ℕ)
      (rawCoeff_ne :
        B.exactClock.zeroSeries.series.offDiag.coeff
          (B.exactClock.firstOrder + tailOrder) ≠ 0)
      (source_ne :
        (permutedPolynomialHessianFourBlock
          (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurB ≠ 0)
  | schurC
      (pair : ThreeSchurActivePair)
      (tailOrder : ℕ)
      (rawCoeff_ne :
        B.exactClock.zeroSeries.series.kernel.coeff
          (B.exactClock.firstOrder + tailOrder) ≠ 0)
      (source_ne :
        (permutedPolynomialHessianFourBlock
          (pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurC ≠ 0)

private theorem PositiveTailExplicitBinaryClockData.transverseGeometry_of_tailActiveCoeff
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S)
    (n : ℕ)
    (hne : B.exactClock.tailSeries.active.coeff n ≠ 0) :
    Nonempty (P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) := by
  rcases B.wholeFamilySchurProvenance with ⟨D⟩
  have hraw :
      B.exactClock.zeroSeries.series.active.coeff
        (B.exactClock.firstOrder + n) ≠ 0 := by
    have ht :=
      B.exactClock.zeroSeries.active_coeff_first_add_eq_tail
        B.exactClock.hasPositiveEntryLayer n
    change
      B.exactClock.zeroSeries.series.active.coeff
          (B.exactClock.firstOrder + n) =
        B.exactClock.tailSeries.active.coeff n at ht
    rw [ht]
    exact hne
  have hpoly : B.exactClock.zeroSeries.series.active ≠ 0 := by
    intro hz
    apply hraw
    rw [hz]
    simp
  have hsource :
      (permutedPolynomialHessianFourBlock
        (D.pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurA ≠ 0 := by
    apply D.pair.sourceSchurA_ne_zero_of_familySchurA_ne_zero (P := P)
    exact D.schurA_ne_zero_of_active_ne_zero hpoly
  exact ⟨.schurA D.pair n hraw hsource⟩

private theorem PositiveTailExplicitBinaryClockData.transverseGeometry_of_tailOffDiagCoeff
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S)
    (n : ℕ)
    (hne : B.exactClock.tailSeries.offDiag.coeff n ≠ 0) :
    Nonempty (P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) := by
  rcases B.wholeFamilySchurProvenance with ⟨D⟩
  have hraw :
      B.exactClock.zeroSeries.series.offDiag.coeff
        (B.exactClock.firstOrder + n) ≠ 0 := by
    have ht :=
      B.exactClock.zeroSeries.offDiag_coeff_first_add_eq_tail
        B.exactClock.hasPositiveEntryLayer n
    change
      B.exactClock.zeroSeries.series.offDiag.coeff
          (B.exactClock.firstOrder + n) =
        B.exactClock.tailSeries.offDiag.coeff n at ht
    rw [ht]
    exact hne
  have hpoly : B.exactClock.zeroSeries.series.offDiag ≠ 0 := by
    intro hz
    apply hraw
    rw [hz]
    simp
  have hsource :
      (permutedPolynomialHessianFourBlock
        (D.pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurB ≠ 0 := by
    apply D.pair.sourceSchurB_ne_zero_of_familySchurB_ne_zero (P := P)
    exact D.schurB_ne_zero_of_offDiag_ne_zero hpoly
  exact ⟨.schurB D.pair n hraw hsource⟩

private theorem PositiveTailExplicitBinaryClockData.transverseGeometry_of_tailKernelCoeff
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S)
    (n : ℕ)
    (hne : B.exactClock.tailSeries.kernel.coeff n ≠ 0) :
    Nonempty (P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) := by
  rcases B.wholeFamilySchurProvenance with ⟨D⟩
  have hraw :
      B.exactClock.zeroSeries.series.kernel.coeff
        (B.exactClock.firstOrder + n) ≠ 0 := by
    have ht :=
      B.exactClock.zeroSeries.kernel_coeff_first_add_eq_tail
        B.exactClock.hasPositiveEntryLayer n
    change
      B.exactClock.zeroSeries.series.kernel.coeff
          (B.exactClock.firstOrder + n) =
        B.exactClock.tailSeries.kernel.coeff n at ht
    rw [ht]
    exact hne
  have hpoly : B.exactClock.zeroSeries.series.kernel ≠ 0 := by
    intro hz
    apply hraw
    rw [hz]
    simp
  have hsource :
      (permutedPolynomialHessianFourBlock
        (D.pair.sourcePerm kernelCoordinate) T.topKernelReesSource).schurC ≠ 0 := by
    apply D.pair.sourceSchurC_ne_zero_of_familySchurC_ne_zero (P := P)
    exact D.schurC_ne_zero_of_kernel_ne_zero hpoly
  exact ⟨.schurC D.pair n hraw hsource⟩

/-- Any nonzero transverse coefficient of the aligned final rank-one clock
comes from a coefficient of the raw binary tail and hence from an honest
represented-source Schur polynomial. -/
theorem PositiveTailExplicitRankOneClockData.transverseCoeff_representedSourceGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B)
    (n : ℕ)
    (htrans :
      R.exactRankOneClock.series.offDiag.coeff n ≠ 0 ∨
        R.exactRankOneClock.series.kernel.coeff n ≠ 0) :
    Nonempty (P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) := by
  cases R with
  | left hres pivot clock clock_eq =>
      rw [clock_eq] at htrans
      rcases htrans with hoff | hkernel
      · by_cases hA : B.exactClock.tailSeries.active.coeff n = 0
        · by_cases hB : B.exactClock.tailSeries.offDiag.coeff n = 0
          · exfalso
            apply hoff
            simp [ExactZeroSchurClock.toRankOneClockLeft,
              BinarySchurPolynomialSeries.alignLeft, hA, hB]
          · exact B.transverseGeometry_of_tailOffDiagCoeff n hB
        · exact B.transverseGeometry_of_tailActiveCoeff n hA
      · by_cases hA : B.exactClock.tailSeries.active.coeff n = 0
        · by_cases hB : B.exactClock.tailSeries.offDiag.coeff n = 0
          · by_cases hC : B.exactClock.tailSeries.kernel.coeff n = 0
            · exfalso
              apply hkernel
              simp [ExactZeroSchurClock.toRankOneClockLeft,
                BinarySchurPolynomialSeries.alignLeft, hA, hB, hC]
            · exact B.transverseGeometry_of_tailKernelCoeff n hC
          · exact B.transverseGeometry_of_tailOffDiagCoeff n hB
        · exact B.transverseGeometry_of_tailActiveCoeff n hA
  | right hres pivot clock clock_eq =>
      rw [clock_eq] at htrans
      rcases htrans with hoff | hkernel
      · have hB : B.exactClock.tailSeries.offDiag.coeff n ≠ 0 := by
          simpa [ExactZeroSchurClock.toRankOneClockRight,
            BinarySchurPolynomialSeries.alignRight] using hoff
        exact B.transverseGeometry_of_tailOffDiagCoeff n hB
      · have hA : B.exactClock.tailSeries.active.coeff n ≠ 0 := by
          simpa [ExactZeroSchurClock.toRankOneClockRight,
            BinarySchurPolynomialSeries.alignRight] using hkernel
        exact B.transverseGeometry_of_tailActiveCoeff n hA

/-- **First transverse source provenance.**

The canonical first transverse order of the final exact rank-one clock is
therefore not an auxiliary coefficient: it has an explicit physical
binary-clock coefficient and a nonzero Schur polynomial on the represented
determinant-one source. -/
theorem PositiveTailExplicitRankOneClockData.firstTransverse_representedSourceGeometry
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) :
    Nonempty (P.PositiveTailRankOneTransverseRepresentedSourceGeometry B) := by
  let C := R.exactRankOneClock
  have htrans :
      C.series.offDiag.coeff C.firstOrder ≠ 0 ∨
        C.series.kernel.coeff C.firstOrder ≠ 0 := by
    simpa [ExactRankOneSchurClockAt.firstOrder] using
      C.series.transverse_nonzero_at_first C.hasTransverse
  exact R.transverseCoeff_representedSourceGeometry C.firstOrder htrans

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
