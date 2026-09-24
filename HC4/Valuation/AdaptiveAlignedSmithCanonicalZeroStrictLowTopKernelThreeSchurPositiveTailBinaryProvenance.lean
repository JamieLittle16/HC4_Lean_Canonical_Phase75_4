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
  · have hm := h01
    change
      (M 0 0).coeff 0 * (M 1 1).coeff 0 -
          (M 0 1).coeff 0 * (M 1 0).coeff 0 = 0 at hm
    have hM10 : M 1 0 = M 0 1 := by
      have h := congrArg
        (fun N : Matrix (Fin 3) (Fin 3)
            (Polynomial (MvPolynomial (Fin 4) K)) => N 0 1)
        hsymmM
      simpa using h
    have hs : (M 1 0).coeff 0 = (M 0 1).coeff 0 := by
      exact congrArg
        (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hM10
    rw [hs] at hm
    simpa [threePivot0BinarySchurSeries,
      Polynomial.coeff_zero_eq_eval_zero] using hm
  · have h02 := hcol 0
    have h12 := hcol 1
    change (M 0 2).coeff 0 = 0 at h02
    change (M 1 2).coeff 0 = 0 at h12
    change
      (M 0 0).coeff 0 * (M 1 2).coeff 0 -
        (M 0 1).coeff 0 * (M 0 2).coeff 0 = 0
    rw [h12, h02]
    ring
  · have h02 := hcol 0
    have h22 := hcol 2
    change (M 0 2).coeff 0 = 0 at h02
    change (M 2 2).coeff 0 = 0 at h22
    change
      (M 0 0).coeff 0 * (M 2 2).coeff 0 -
        (M 0 2).coeff 0 * (M 0 2).coeff 0 = 0
    rw [h22, h02]
    ring
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
  · have hm := h01
    change
      (M 0 0).coeff 0 * (M 1 1).coeff 0 -
          (M 0 1).coeff 0 * (M 1 0).coeff 0 = 0 at hm
    have hM10 : M 1 0 = M 0 1 := by
      have h := congrArg
        (fun N : Matrix (Fin 3) (Fin 3)
            (Polynomial (MvPolynomial (Fin 4) K)) => N 0 1)
        hsymmM
      simpa using h
    have hs : (M 1 0).coeff 0 = (M 0 1).coeff 0 := by
      exact congrArg
        (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hM10
    rw [hs] at hm
    simpa [threePivot1BinarySchurSeries,
      Polynomial.coeff_zero_eq_eval_zero, mul_comm] using hm
  · have h02 := hcol 0
    have h12 := hcol 1
    change (M 0 2).coeff 0 = 0 at h02
    change (M 1 2).coeff 0 = 0 at h12
    change
      (M 1 1).coeff 0 * (M 0 2).coeff 0 -
        (M 0 1).coeff 0 * (M 1 2).coeff 0 = 0
    rw [h02, h12]
    ring
  · have h12 := hcol 1
    have h22 := hcol 2
    change (M 1 2).coeff 0 = 0 at h12
    change (M 2 2).coeff 0 = 0 at h22
    change
      (M 1 1).coeff 0 * (M 2 2).coeff 0 -
        (M 1 2).coeff 0 * (M 1 2).coeff 0 = 0
    rw [h22, h12]
    ring
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
    (D : ThreeSchurTangentTailKernelOpeningData S M)
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
  have h10 : C 1 0 = C 0 1 := by
    have h := congrArg
      (fun N : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) => N 0 1)
      hsymm
    simpa using h
  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨h00, h11⟩
  have h00C : C 0 0 = 0 := by simpa [C, E] using h00
  have h11C : C 1 1 = 0 := by simpa [C, E] using h11
  have h01sq : C 0 1 * C 0 1 = 0 := by
    have hz : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 0 := by
      simpa [C, E] using h01
    rw [h00C, h11C, h10] at hz
    linear_combination -hz
  have h01z : C 0 1 = 0 :=
    (mul_self_eq_zero.mp h01sq)
  have h10z : C 1 0 = 0 := by rw [h10, h01z]
  have h20 : C 2 0 = 0 := by
    have hs20 : C 2 0 = C 0 2 := by
      have h := congrArg
        (fun N : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) => N 0 2)
        hsymm
      simpa using h
    rw [hs20, hcol 0]
  have h21 : C 2 1 = 0 := by
    have hs21 : C 2 1 = C 1 2 := by
      have h := congrArg
        (fun N : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) => N 1 2)
        hsymm
      simpa using h
    rw [hs21, hcol 1]
  have h22 : C 2 2 = 0 := hcol 2
  apply E.tailConstantMatrix_ne_zero
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [C]

/-- **Lossless positive-tail second Schur frontier.** -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailDetailedFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty (P.TopKernelThreeSchurPositiveTailDetailedFrontier S) := by
  let E := S.toExactZeroThreeSchurClock
  have hcol :
      ∀ i : Fin 3, E.tailConstantMatrix i 2 = 0 := by
    intro i
    simpa [E] using D.tailConstant_kernelColumn_zero hpos i
  have hdet0 : E.tailConstantMatrix.det = 0 := by
    have hsymm : E.tailConstantMatrix.IsSymm :=
      E.tailConstantMatrix_isSymm S.exactZeroThreeSchurClock_isSymm
    have h20 : E.tailConstantMatrix 2 0 = 0 := by
      have hs20 :
          E.tailConstantMatrix 2 0 = E.tailConstantMatrix 0 2 := by
        have h := congrArg
          (fun N : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) => N 0 2)
          hsymm
        simpa using h
      rw [hs20, hcol 0]
    have h21 : E.tailConstantMatrix 2 1 = 0 := by
      have hs21 :
          E.tailConstantMatrix 2 1 = E.tailConstantMatrix 1 2 := by
        have h := congrArg
          (fun N : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) => N 1 2)
          hsymm
        simpa using h
      rw [hs21, hcol 1]
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
    rcases activeDiagonal_ne_zero_of_positiveTail_rankOne D hpos h01z with
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
