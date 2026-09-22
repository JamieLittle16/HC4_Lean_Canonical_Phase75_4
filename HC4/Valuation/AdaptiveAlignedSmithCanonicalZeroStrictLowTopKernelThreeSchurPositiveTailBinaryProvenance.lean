import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPositiveTailFrontier
import Mathlib.Tactic

/-!
# Explicit active-pivot provenance for the positive three-Schur tail

In the positive-tail tangent branch the normalised 3x3 tail has zero constant
kernel column.  If its active (0,1) principal minor is nonzero we already have
rank-two geometry.  Otherwise the constant matrix is nonzero, symmetric, has
zero kernel row/column, and its active 2x2 determinant vanishes.  Hence one of
the active diagonal entries 0 or 1 is nonzero.

This file keeps that actual pivot instead of passing through the generic
existential 3x3-to-binary constructor.  The resulting binary zero-Schur clock
is definitionally the cleared 1+2 Schur quotient using pivot 0 or pivot 1 of
the same normalised 3x3 tail.

That provenance is needed to transport the strictly later projected kernel
opening through the second Schur step without identifying an abstract repair
label with source geometry.
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

/-- Literal active-pivot binary clock retained from the positive normalised
3x3 tail. -/
inductive PositiveTailExplicitBinaryClockData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | pivot0
      (pivot_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 ≠ 0)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (series_eq :
        clock.zeroSeries.series =
          threePivot0BinarySchurSeries
            (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
              S.toExactZeroThreeSchurClock.hasPositiveEntryLayer))
      (defect_eq :
        clock.defect =
          S.toExactZeroThreeSchurClock.residualDefect)
  | pivot1
      (pivot_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 ≠ 0)
      (clock : ExactZeroSchurClock (MvPolynomial (Fin 4) K))
      (series_eq :
        clock.zeroSeries.series =
          threePivot1BinarySchurSeries
            (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
              S.toExactZeroThreeSchurClock.hasPositiveEntryLayer))
      (defect_eq :
        clock.defect =
          S.toExactZeroThreeSchurClock.residualDefect)

/-- Detailed positive-tail frontier: active rank two, or an exact binary clock
with literal active-pivot provenance. -/
inductive TopKernelThreeSchurPositiveTailDetailedFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | activeRankTwo
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (pivot01 :
        S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
            S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
              S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 ≠ 0)
  | binaryZeroSchur
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (binary : P.PositiveTailExplicitBinaryClockData S)

private noncomputable def explicitBinaryClockPivot0
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (hpivot :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 ≠ 0)
    (h01 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
          S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 = 0)
    (hcol :
      ∀ i : Fin 3,
        S.toExactZeroThreeSchurClock.tailConstantMatrix i 2 = 0) :
    ExactZeroSchurClock (MvPolynomial (Fin 4) K) := by
  let E := S.toExactZeroThreeSchurClock
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hsymmM : M.IsSymm := E.tailMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have hsymmC : E.tailConstantMatrix.IsSymm :=
    E.tailConstantMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  refine {
    zeroSeries := {
      series := threePivot0BinarySchurSeries M
      active_coeff_zero := ?_
      offDiag_coeff_zero := ?_
      kernel_coeff_zero := ?_
    }
    clearingFactor := M 0 0 * E.clearingFactor
    defect := E.residualDefect
    clearingFactor_coeff_zero_ne_zero := ?_
    determinantFactor := ?_
  }
  · have h10 :
        E.tailConstantMatrix 1 0 =
          E.tailConstantMatrix 0 1 := hsymmC 1 0
    simpa [threePivot0BinarySchurSeries, M,
      ExactZeroThreeSchurClock.tailConstantMatrix,
      Polynomial.coeff_zero_eq_eval_zero, h10] using h01
  · have h02 := hcol 0
    have h12 := hcol 1
    simpa [threePivot0BinarySchurSeries, M,
      ExactZeroThreeSchurClock.tailConstantMatrix,
      Polynomial.coeff_zero_eq_eval_zero, h02, h12]
  · have h02 := hcol 0
    have h22 := hcol 2
    simpa [threePivot0BinarySchurSeries, M,
      ExactZeroThreeSchurClock.tailConstantMatrix,
      Polynomial.coeff_zero_eq_eval_zero, h02, h22]
  · have hp :
        (M 0 0).coeff 0 ≠ 0 := by
      simpa [M, ExactZeroThreeSchurClock.tailConstantMatrix] using hpivot
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      mul_ne_zero hp E.clearingFactor_coeff_zero_ne_zero
  · rw [threePivot0BinarySchurSeries_determinant M hsymmM]
    rw [E.tail_determinantFactor]
    ring

private noncomputable def explicitBinaryClockPivot1
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (hpivot :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 ≠ 0)
    (h01 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
          S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 = 0)
    (hcol :
      ∀ i : Fin 3,
        S.toExactZeroThreeSchurClock.tailConstantMatrix i 2 = 0) :
    ExactZeroSchurClock (MvPolynomial (Fin 4) K) := by
  let E := S.toExactZeroThreeSchurClock
  let M := E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
  have hsymmM : M.IsSymm := E.tailMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have hsymmC : E.tailConstantMatrix.IsSymm :=
    E.tailConstantMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  refine {
    zeroSeries := {
      series := threePivot1BinarySchurSeries M
      active_coeff_zero := ?_
      offDiag_coeff_zero := ?_
      kernel_coeff_zero := ?_
    }
    clearingFactor := M 1 1 * E.clearingFactor
    defect := E.residualDefect
    clearingFactor_coeff_zero_ne_zero := ?_
    determinantFactor := ?_
  }
  · have h10 :
        E.tailConstantMatrix 1 0 =
          E.tailConstantMatrix 0 1 := hsymmC 1 0
    simpa [threePivot1BinarySchurSeries, M,
      ExactZeroThreeSchurClock.tailConstantMatrix,
      Polynomial.coeff_zero_eq_eval_zero, h10, mul_comm] using h01
  · have h02 := hcol 0
    have h12 := hcol 1
    simpa [threePivot1BinarySchurSeries, M,
      ExactZeroThreeSchurClock.tailConstantMatrix,
      Polynomial.coeff_zero_eq_eval_zero, h02, h12]
  · have h12 := hcol 1
    have h22 := hcol 2
    simpa [threePivot1BinarySchurSeries, M,
      ExactZeroThreeSchurClock.tailConstantMatrix,
      Polynomial.coeff_zero_eq_eval_zero, h12, h22]
  · have hp :
        (M 1 1).coeff 0 ≠ 0 := by
      simpa [M, ExactZeroThreeSchurClock.tailConstantMatrix] using hpivot
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      mul_ne_zero hp E.clearingFactor_coeff_zero_ne_zero
  · rw [threePivot1BinarySchurSeries_determinant M hsymmM]
    rw [E.tail_determinantFactor]
    ring

/-- If the active principal determinant vanishes while the constant kernel
column is zero, one of the two active diagonal entries is nonzero. -/
theorem activeDiagonal_ne_zero_of_positiveTail_rankOne
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentTailKernelOpeningData M)
    (hpos : 0 < D.relativeOrder)
    (h01 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 -
          S.toExactZeroThreeSchurClock.tailConstantMatrix 0 1 *
            S.toExactZeroThreeSchurClock.tailConstantMatrix 1 0 = 0) :
    S.toExactZeroThreeSchurClock.tailConstantMatrix 0 0 ≠ 0 ∨
      S.toExactZeroThreeSchurClock.tailConstantMatrix 1 1 ≠ 0 := by
  let E := S.toExactZeroThreeSchurClock
  let C := E.tailConstantMatrix
  have hcol : ∀ i : Fin 3, C i 2 = 0 := by
    intro i
    simpa [C, E] using D.tailConstant_kernelColumn_zero hpos i
  have hsymm : C.IsSymm := by
    simpa [C, E] using
      E.tailConstantMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
  have h10 : C 1 0 = C 0 1 := hsymm 1 0
  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨h00, h11⟩
  have h01sq : C 0 1 * C 0 1 = 0 := by
    have hz : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 0 := by
      simpa [C, E] using h01
    rw [h00, h11, h10] at hz
    simpa using neg_eq_zero.mp hz
  have h01z : C 0 1 = 0 :=
    (mul_self_eq_zero.mp h01sq)
  have h10z : C 1 0 = 0 := by rw [h10, h01z]
  have h20 : C 2 0 = 0 := by rw [hsymm 2 0, hcol 0]
  have h21 : C 2 1 = 0 := by rw [hsymm 2 1, hcol 1]
  have h22 : C 2 2 = 0 := hcol 2
  apply E.tailConstantMatrix_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [C]

/-- **Lossless positive-tail second Schur frontier.** -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailDetailedFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentTailKernelOpeningData M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty P.TopKernelThreeSchurPositiveTailDetailedFrontier S := by
  let E := S.toExactZeroThreeSchurClock
  have hcol :
      ∀ i : Fin 3, E.tailConstantMatrix i 2 = 0 := by
    intro i
    simpa [E] using D.tailConstant_kernelColumn_zero hpos i
  have hdet0 : E.tailConstantMatrix.det = 0 := by
    have hsymm : E.tailConstantMatrix.IsSymm :=
      E.tailConstantMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
    have h20 : E.tailConstantMatrix 2 0 = 0 := by
      rw [hsymm 2 0, hcol 0]
    have h21 : E.tailConstantMatrix 2 1 = 0 := by
      rw [hsymm 2 1, hcol 1]
    have h22 : E.tailConstantMatrix 2 2 = 0 := hcol 2
    simp [Matrix.det_fin_three, hcol 0, hcol 1, h22, h20, h21]

  have hres : 0 < E.residualDefect := by
    by_contra hnot
    have hz : E.residualDefect = 0 := by omega
    exact (E.tailConstantMatrix_det_ne_zero_of_residual_zero hz) hdet0

  by_cases h01 :
      E.tailConstantMatrix 0 0 * E.tailConstantMatrix 1 1 -
        E.tailConstantMatrix 0 1 * E.tailConstantMatrix 1 0 ≠ 0
  · exact ⟨.activeRankTwo hres h01⟩
  · have h01z :
        E.tailConstantMatrix 0 0 * E.tailConstantMatrix 1 1 -
          E.tailConstantMatrix 0 1 * E.tailConstantMatrix 1 0 = 0 :=
      not_ne_iff.mp h01
    rcases D.activeDiagonal_ne_zero_of_positiveTail_rankOne hpos h01z with
      h0 | h1
    · let clock :=
        explicitBinaryClockPivot0 (P := P) S h0 h01z hcol
      exact ⟨.binaryZeroSchur hres (.pivot0 h0 clock rfl rfl)⟩
    · let clock :=
        explicitBinaryClockPivot1 (P := P) S h1 h01z hcol
      exact ⟨.binaryZeroSchur hres (.pivot1 h1 clock rfl rfl)⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
