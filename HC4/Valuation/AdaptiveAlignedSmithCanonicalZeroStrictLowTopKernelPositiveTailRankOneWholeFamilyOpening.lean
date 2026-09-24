import HC4.Newton.PolynomialFirstOpeningTransport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneSourceDeparture
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailWholeFamilySchurProvenance
import Mathlib.Tactic

/-!
# Exact whole-family first transverse opening for the positive rank-one tail

The positive three-Schur tail eventually reaches an exact rank-one binary
Schur clock.  The clock is obtained after two common parameter factors have
been removed:

* the common first 3x3 Schur order q; and
* the common first binary order e.

This file transports the final rank-one transverse opening back through both
normalisations and the retained scalar pivot.

For a left pivot, the honest whole-family transverse entries are the
projective combinations

    -b0 * SchurA + a0 * SchurB

and

    b0^2 * SchurA - 2*a0*b0*SchurB + a0^2*SchurC.

For a right-axis pivot they are simply SchurB and SchurA respectively.

In either orientation, multiplication by the retained first scalar pivot gives
exactly X^(2q+e) times the aligned rank-one transverse series.  Since that
pivot has nonzero constant coefficient, the first transverse coefficient of
the exact rank-one clock therefore becomes an exact first opening of an honest
whole-family polynomial at physical order 2q+e+r.
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

private theorem zeroActive_eq_X_pow_first_mul_tail
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K)) :
    E.zeroSeries.series.active =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ E.firstOrder *
        E.tailSeries.active := by
  simpa [ExactZeroSchurClock.firstOrder, ExactZeroSchurClock.tailSeries] using
    E.zeroSeries.active_eq_firstFactor_mul_tail E.hasPositiveEntryLayer

private theorem zeroOffDiag_eq_X_pow_first_mul_tail
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K)) :
    E.zeroSeries.series.offDiag =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ E.firstOrder *
        E.tailSeries.offDiag := by
  simpa [ExactZeroSchurClock.firstOrder, ExactZeroSchurClock.tailSeries] using
    E.zeroSeries.offDiag_eq_firstFactor_mul_tail E.hasPositiveEntryLayer

private theorem zeroKernel_eq_X_pow_first_mul_tail
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K)) :
    E.zeroSeries.series.kernel =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ E.firstOrder *
        E.tailSeries.kernel := by
  simpa [ExactZeroSchurClock.firstOrder, ExactZeroSchurClock.tailSeries] using
    E.zeroSeries.kernel_eq_firstFactor_mul_tail E.hasPositiveEntryLayer

/-- Physical base order before the final rank-one transverse movement. -/
def PositiveTailExplicitBinaryClockData.rankOnePhysicalBaseOrder
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) : ℕ :=
  2 * S.firstThreeSchurOrder + B.exactClock.firstOrder

/-- Left-pivot whole-family off-diagonal projective wedge. -/
noncomputable def PositiveTailBinaryWholeFamilySchurProvenance.leftTransverseOffDiag
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B) :
    Polynomial (MvPolynomial (Fin 4) K) :=
  -(Polynomial.C (B.exactClock.tailSeries.offDiag.coeff 0) *
      (D.pair.block P.threeSchurBlock).schurA) +
    Polynomial.C (B.exactClock.tailSeries.active.coeff 0) *
      (D.pair.block P.threeSchurBlock).schurB

/-- Left-pivot whole-family kernel projective quadratic. -/
noncomputable def PositiveTailBinaryWholeFamilySchurProvenance.leftTransverseKernel
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B) :
    Polynomial (MvPolynomial (Fin 4) K) :=
  let E := B.exactClock
  (Polynomial.C (E.tailSeries.offDiag.coeff 0)) ^ 2 *
      (D.pair.block P.threeSchurBlock).schurA -
    2 * Polynomial.C (E.tailSeries.active.coeff 0) *
      Polynomial.C (E.tailSeries.offDiag.coeff 0) *
      (D.pair.block P.threeSchurBlock).schurB +
    (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 *
      (D.pair.block P.threeSchurBlock).schurC

/-- Right-axis whole-family off-diagonal transverse entry. -/
noncomputable def PositiveTailBinaryWholeFamilySchurProvenance.rightTransverseOffDiag
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B) :
    Polynomial (MvPolynomial (Fin 4) K) :=
  (D.pair.block P.threeSchurBlock).schurB

/-- Right-axis whole-family kernel transverse entry after swapping axes. -/
noncomputable def PositiveTailBinaryWholeFamilySchurProvenance.rightTransverseKernel
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B) :
    Polynomial (MvPolynomial (Fin 4) K) :=
  (D.pair.block P.threeSchurBlock).schurA

private theorem nested_factor_eq
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.PositiveTailExplicitBinaryClockData S) :
    (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          S.firstThreeSchurOrder) ^ 2) *
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          B.exactClock.firstOrder =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
        B.rankOnePhysicalBaseOrder := by
  unfold PositiveTailExplicitBinaryClockData.rankOnePhysicalBaseOrder
  calc
    (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          S.firstThreeSchurOrder) ^ 2) *
        Polynomial.X ^ B.exactClock.firstOrder =
      Polynomial.X ^ (S.firstThreeSchurOrder * 2) *
        Polynomial.X ^ B.exactClock.firstOrder := by
          rw [← pow_mul]
    _ = Polynomial.X ^
        (S.firstThreeSchurOrder * 2 + B.exactClock.firstOrder) := by
          rw [pow_add]
    _ = Polynomial.X ^
        (2 * S.firstThreeSchurOrder + B.exactClock.firstOrder) := by
          congr 1
          omega

/-- Exact left-pivot whole-family off-diagonal identity. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.leftTransverseOffDiag_eq
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hleft : B.exactClock.tailSeries.LeftPivot) :
    D.firstPivot * D.leftTransverseOffDiag =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          B.rankOnePhysicalBaseOrder *
        (B.exactClock.tailSeries.alignLeft hleft).offDiag := by
  let E := B.exactClock
  let A := (D.pair.block P.threeSchurBlock).schurA
  let C := (D.pair.block P.threeSchurBlock).schurB
  have hA := zeroActive_eq_X_pow_first_mul_tail E
  have hC := zeroOffDiag_eq_X_pow_first_mul_tail E
  calc
    D.firstPivot * D.leftTransverseOffDiag =
        -Polynomial.C (E.tailSeries.offDiag.coeff 0) *
            (D.firstPivot * A) +
          Polynomial.C (E.tailSeries.active.coeff 0) *
            (D.firstPivot * C) := by
              simp [PositiveTailBinaryWholeFamilySchurProvenance.leftTransverseOffDiag,
                E, A, C]
              ring
    _ =
        -Polynomial.C (E.tailSeries.offDiag.coeff 0) *
            (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                S.firstThreeSchurOrder) ^ 2 *
              E.zeroSeries.series.active) +
          Polynomial.C (E.tailSeries.active.coeff 0) *
            (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                S.firstThreeSchurOrder) ^ 2 *
              E.zeroSeries.series.offDiag) := by
              rw [show D.firstPivot * A =
                    ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                      S.firstThreeSchurOrder) ^ 2 *
                      E.zeroSeries.series.active by simpa [E, A] using D.active_eq]
              rw [show D.firstPivot * C =
                    ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                      S.firstThreeSchurOrder) ^ 2 *
                      E.zeroSeries.series.offDiag by simpa [E, C] using D.offDiag_eq]
    _ =
        ((((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              S.firstThreeSchurOrder) ^ 2) *
            Polynomial.X ^ E.firstOrder) *
          (-Polynomial.C (E.tailSeries.offDiag.coeff 0) * E.tailSeries.active +
            Polynomial.C (E.tailSeries.active.coeff 0) * E.tailSeries.offDiag) := by
              rw [hA, hC]
              ring
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder *
          (-Polynomial.C (E.tailSeries.offDiag.coeff 0) * E.tailSeries.active +
            Polynomial.C (E.tailSeries.active.coeff 0) * E.tailSeries.offDiag) := by
              rw [B.nested_factor_eq]
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder *
          (E.tailSeries.alignLeft hleft).offDiag := by
              rfl

/-- Exact left-pivot whole-family kernel identity. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.leftTransverseKernel_eq
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hleft : B.exactClock.tailSeries.LeftPivot) :
    D.firstPivot * D.leftTransverseKernel =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          B.rankOnePhysicalBaseOrder *
        (B.exactClock.tailSeries.alignLeft hleft).kernel := by
  let E := B.exactClock
  let A := (D.pair.block P.threeSchurBlock).schurA
  let C := (D.pair.block P.threeSchurBlock).schurB
  let G := (D.pair.block P.threeSchurBlock).schurC
  have hA := zeroActive_eq_X_pow_first_mul_tail E
  have hC := zeroOffDiag_eq_X_pow_first_mul_tail E
  have hG := zeroKernel_eq_X_pow_first_mul_tail E
  calc
    D.firstPivot * D.leftTransverseKernel =
        (Polynomial.C (E.tailSeries.offDiag.coeff 0)) ^ 2 *
            (D.firstPivot * A) -
          2 * Polynomial.C (E.tailSeries.active.coeff 0) *
            Polynomial.C (E.tailSeries.offDiag.coeff 0) *
            (D.firstPivot * C) +
          (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 *
            (D.firstPivot * G) := by
              simp [PositiveTailBinaryWholeFamilySchurProvenance.leftTransverseKernel,
                E, A, C, G]
              ring
    _ =
        (Polynomial.C (E.tailSeries.offDiag.coeff 0)) ^ 2 *
            (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                S.firstThreeSchurOrder) ^ 2 * E.zeroSeries.series.active) -
          2 * Polynomial.C (E.tailSeries.active.coeff 0) *
            Polynomial.C (E.tailSeries.offDiag.coeff 0) *
            (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                S.firstThreeSchurOrder) ^ 2 * E.zeroSeries.series.offDiag) +
          (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 *
            (((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                S.firstThreeSchurOrder) ^ 2 * E.zeroSeries.series.kernel) := by
              rw [show D.firstPivot * A =
                    ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                      S.firstThreeSchurOrder) ^ 2 *
                      E.zeroSeries.series.active by simpa [E, A] using D.active_eq]
              rw [show D.firstPivot * C =
                    ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                      S.firstThreeSchurOrder) ^ 2 *
                      E.zeroSeries.series.offDiag by simpa [E, C] using D.offDiag_eq]
              rw [show D.firstPivot * G =
                    ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
                      S.firstThreeSchurOrder) ^ 2 *
                      E.zeroSeries.series.kernel by simpa [E, G] using D.kernel_eq]
    _ =
        ((((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              S.firstThreeSchurOrder) ^ 2) *
            Polynomial.X ^ E.firstOrder) *
          ((Polynomial.C (E.tailSeries.offDiag.coeff 0)) ^ 2 * E.tailSeries.active -
            2 * Polynomial.C (E.tailSeries.active.coeff 0) *
              Polynomial.C (E.tailSeries.offDiag.coeff 0) * E.tailSeries.offDiag +
            (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 * E.tailSeries.kernel) := by
              rw [hA, hC, hG]
              ring
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder *
          ((Polynomial.C (E.tailSeries.offDiag.coeff 0)) ^ 2 * E.tailSeries.active -
            2 * Polynomial.C (E.tailSeries.active.coeff 0) *
              Polynomial.C (E.tailSeries.offDiag.coeff 0) * E.tailSeries.offDiag +
            (Polynomial.C (E.tailSeries.active.coeff 0)) ^ 2 * E.tailSeries.kernel) := by
              rw [B.nested_factor_eq]
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder *
          (E.tailSeries.alignLeft hleft).kernel := by
              rfl

/-- Exact right-axis whole-family off-diagonal identity. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.rightTransverseOffDiag_eq
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hright : B.exactClock.tailSeries.RightAxisPivot) :
    D.firstPivot * D.rightTransverseOffDiag =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          B.rankOnePhysicalBaseOrder *
        (B.exactClock.tailSeries.alignRight hright).offDiag := by
  let E := B.exactClock
  have hC := zeroOffDiag_eq_X_pow_first_mul_tail E
  calc
    D.firstPivot * D.rightTransverseOffDiag =
        ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            S.firstThreeSchurOrder) ^ 2 * E.zeroSeries.series.offDiag := by
              simpa [PositiveTailBinaryWholeFamilySchurProvenance.rightTransverseOffDiag,
                E] using D.offDiag_eq
    _ =
        ((((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              S.firstThreeSchurOrder) ^ 2) *
            Polynomial.X ^ E.firstOrder) * E.tailSeries.offDiag := by
              rw [hC]
              ring
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder * E.tailSeries.offDiag := by
              rw [B.nested_factor_eq]
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder *
          (E.tailSeries.alignRight hright).offDiag := by
              rfl

/-- Exact right-axis whole-family kernel identity. -/
theorem PositiveTailBinaryWholeFamilySchurProvenance.rightTransverseKernel_eq
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
    (hright : B.exactClock.tailSeries.RightAxisPivot) :
    D.firstPivot * D.rightTransverseKernel =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          B.rankOnePhysicalBaseOrder *
        (B.exactClock.tailSeries.alignRight hright).kernel := by
  let E := B.exactClock
  have hA := zeroActive_eq_X_pow_first_mul_tail E
  calc
    D.firstPivot * D.rightTransverseKernel =
        ((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            S.firstThreeSchurOrder) ^ 2 * E.zeroSeries.series.active := by
              simpa [PositiveTailBinaryWholeFamilySchurProvenance.rightTransverseKernel,
                E] using D.active_eq
    _ =
        ((((Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              S.firstThreeSchurOrder) ^ 2) *
            Polynomial.X ^ E.firstOrder) * E.tailSeries.active := by
              rw [hA]
              ring
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder * E.tailSeries.active := by
              rw [B.nested_factor_eq]
    _ =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
            B.rankOnePhysicalBaseOrder *
          (E.tailSeries.alignRight hright).kernel := by
              rfl

/-- Exact first transverse opening on the honest whole reverse-Rees family. -/
inductive PositiveTailRankOneWholeFamilyFirstTransverseOpening
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) : Type (u + 1)
  | offDiag
      (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
      (whole : Polynomial (MvPolynomial (Fin 4) K))
      (order : ℕ)
      (order_eq :
        order = B.rankOnePhysicalBaseOrder + R.exactRankOneClock.firstOrder)
      (lower_zero : ∀ n : ℕ, n < order → whole.coeff n = 0)
      (opens : whole.coeff order ≠ 0)
  | kernel
      (D : P.PositiveTailBinaryWholeFamilySchurProvenance B)
      (whole : Polynomial (MvPolynomial (Fin 4) K))
      (order : ℕ)
      (order_eq :
        order = B.rankOnePhysicalBaseOrder + R.exactRankOneClock.firstOrder)
      (lower_zero : ∀ n : ℕ, n < order → whole.coeff n = 0)
      (opens : whole.coeff order ≠ 0)

/-- The exact rank-one clock's first transverse coefficient survives all the
way back to one exact first opening of an honest whole-family projective Schur
polynomial. -/
theorem PositiveTailExplicitRankOneClockData.wholeFamilyFirstTransverseOpening
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) :
    Nonempty (P.PositiveTailRankOneWholeFamilyFirstTransverseOpening R) := by
  rcases B.wholeFamilySchurProvenance with ⟨D⟩
  cases R with
  | left hres hleft clock hclock =>
      subst clock
      let C := B.exactClock.toRankOneClockLeft hres hleft
      rcases C.series.transverse_nonzero_at_first C.hasTransverse with hoff | hker
      · have htransport :=
          polynomial_firstOpening_of_mul_eq_X_pow_mul
            D.firstPivot_coeff_zero_ne_zero
            (D.leftTransverseOffDiag_eq hleft)
            (fun n hn => C.series.offDiag_coeff_eq_zero_of_lt_first C.hasTransverse hn)
            hoff
        exact ⟨.offDiag D D.leftTransverseOffDiag
          (B.rankOnePhysicalBaseOrder + C.firstOrder) rfl
          htransport.1 htransport.2⟩
      · have htransport :=
          polynomial_firstOpening_of_mul_eq_X_pow_mul
            D.firstPivot_coeff_zero_ne_zero
            (D.leftTransverseKernel_eq hleft)
            (fun n hn => C.series.kernel_coeff_eq_zero_of_lt_first C.hasTransverse hn)
            hker
        exact ⟨.kernel D D.leftTransverseKernel
          (B.rankOnePhysicalBaseOrder + C.firstOrder) rfl
          htransport.1 htransport.2⟩
  | right hres hright clock hclock =>
      subst clock
      let C := B.exactClock.toRankOneClockRight hres hright
      rcases C.series.transverse_nonzero_at_first C.hasTransverse with hoff | hker
      · have htransport :=
          polynomial_firstOpening_of_mul_eq_X_pow_mul
            D.firstPivot_coeff_zero_ne_zero
            (D.rightTransverseOffDiag_eq hright)
            (fun n hn => C.series.offDiag_coeff_eq_zero_of_lt_first C.hasTransverse hn)
            hoff
        exact ⟨.offDiag D D.rightTransverseOffDiag
          (B.rankOnePhysicalBaseOrder + C.firstOrder) rfl
          htransport.1 htransport.2⟩
      · have htransport :=
          polynomial_firstOpening_of_mul_eq_X_pow_mul
            D.firstPivot_coeff_zero_ne_zero
            (D.rightTransverseKernel_eq hright)
            (fun n hn => C.series.kernel_coeff_eq_zero_of_lt_first C.hasTransverse hn)
            hker
        exact ⟨.kernel D D.rightTransverseKernel
          (B.rankOnePhysicalBaseOrder + C.firstOrder) rfl
          htransport.1 htransport.2⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
