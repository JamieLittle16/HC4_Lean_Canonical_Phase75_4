import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurTangentSplit
import HC4.Valuation.ReverseWeightedReesHessianTwoByTwoMinor
import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianRankSplit
import Mathlib.Tactic

/-!
# Source lift for the projected three-Schur first-break branch

The only pre-relative constructor left by the C/D assembly is
`ThreeSchurProjectedRankTwoAtFirstBreak`.  Its nonzero mixed quotient entry
is not merely quotient rank metadata: in each of the three scalar-pivot
orientations it is literally one coefficient of an arbitrary `2 x 2`
Hessian minor of the honest ordinary reverse-Rees family.

The generic reverse-Rees minor lift therefore carries that nonvanishing back
to the represented determinant-one source.  A nonzero arbitrary Hessian minor
rules out the finite special-Hessian `AllTwoByTwoMinorsZero` alternative, so
the existing finite rank split returns an honest
`AdaptiveAlignedSmithCanonicalExactActiveFourBlock`.  This is deliberately
slightly more general than an `ActualRankTwoHessianChart`: the exact-active
consumer already permits the determinant-one shear chart needed when the
nonzero source minor is not coordinate-principal.

No quotient matrix is identified with a source Hessian and no repair-only
conclusion is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Moving the parameter outside commutes with an arbitrary Hessian
`2 x 2` minor. -/
private theorem parameterFirstEquiv_familyHessianTwoByTwoMinor
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (i j k l : Fin 4) :
    parameterFirstEquiv K (familyHessianTwoByTwoMinor F i j k l) =
      parameterFirstHessian F i k * parameterFirstHessian F j l -
        parameterFirstHessian F i l * parameterFirstHessian F j k := by
  change
    parameterFirstEquiv K
        (HC4.Polynomial.hessian F i k * HC4.Polynomial.hessian F j l -
          HC4.Polynomial.hessian F i l * HC4.Polynomial.hessian F j k) =
      parameterFirstEquiv K (HC4.Polynomial.hessian F i k) *
          parameterFirstEquiv K (HC4.Polynomial.hessian F j l) -
        parameterFirstEquiv K (HC4.Polynomial.hessian F i l) *
          parameterFirstEquiv K (HC4.Polynomial.hessian F j k)
  rw [map_sub, map_mul, map_mul]

/-- Pivot-shaped form of the same identity.  Hessian symmetry puts the
second product in exactly the orientation used by the cleared 1+3 Schur
entries. -/
private theorem parameterFirstEquiv_familyHessianPivotMinor
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (pivot other kernel : Fin 4) :
    parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          F pivot other pivot kernel) =
      parameterFirstHessian F pivot pivot *
          parameterFirstHessian F other kernel -
        parameterFirstHessian F pivot other *
          parameterFirstHessian F pivot kernel := by
  rw [parameterFirstEquiv_familyHessianTwoByTwoMinor]
  rw [parameterFirstHessian_symmetric F other pivot]
  ring

/-- Row-commuted pivot form, matching the coordinate-1 and coordinate-2
cleared Schur orientations without asking simplification to orient Hessian
symmetry. -/
private theorem parameterFirstEquiv_familyHessianPivotMinor_commuted
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (pivot other kernel : Fin 4) :
    parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          F other pivot kernel pivot) =
      parameterFirstHessian F pivot pivot *
          parameterFirstHessian F other kernel -
        parameterFirstHessian F other pivot *
          parameterFirstHessian F pivot kernel := by
  rw [parameterFirstEquiv_familyHessianTwoByTwoMinor]
  rw [parameterFirstHessian_symmetric F pivot kernel]
  ring

/-- Same row-commuted minor with the cross entry oriented as
`H[pivot,other]`; used when the stored four-block names that symmetric entry
in the opposite triangular orientation. -/
private theorem parameterFirstEquiv_familyHessianPivotMinor_commuted_cross
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (pivot other kernel : Fin 4) :
    parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          F other pivot kernel pivot) =
      parameterFirstHessian F pivot pivot *
          parameterFirstHessian F other kernel -
        parameterFirstHessian F pivot other *
          parameterFirstHessian F pivot kernel := by
  rw [parameterFirstEquiv_familyHessianPivotMinor_commuted]
  rw [parameterFirstHessian_symmetric F other pivot]

/-- Any nonzero arbitrary Hessian minor on the special fibre forces the
existing exact-active finite rank split into its geometric branch. -/
theorem exactActiveFourBlock_of_specialFiber_twoByTwoMinor_ne_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (i j k l : Fin 4)
    (hminor :
      hessianTwoByTwoMinor
        (polynomialFamilySpecialFiber s.family) i j k l ≠ 0) :
    Nonempty (AdaptiveAlignedSmithCanonicalExactActiveFourBlock s) := by
  rcases scaleAwareHessian_exactActive_or_rankOne s with hactive | hrank
  · exact hactive
  · exfalso
    apply hminor
    have hz := hrank i k j l
    rw [scaleAwareSpecialHessianFourBlock_matrix] at hz
    simpa [hessianTwoByTwoMinor] using hz

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- A nonzero parameter-first coefficient of one arbitrary family Hessian
minor lifts all the way back to the represented source. -/
private theorem sourceTwoByTwoMinor_of_parameterFirst_coeff_ne_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (i j k l : Fin 4)
    (n : ℕ)
    (hcoeff :
      (parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          T.topKernelReverseReesFamily i j k l)).coeff n ≠ 0) :
    hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0 := by
  have hmapped :
      parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          T.topKernelReverseReesFamily i j k l) ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz]
    simp
  have hfamily :
      familyHessianTwoByTwoMinor
        T.topKernelReverseReesFamily i j k l ≠ 0 := by
    intro hz
    apply hmapped
    rw [hz]
    simp
  apply
    reverseWeightedReesFamily_sourceTwoByTwoMinor_of_familyMinor_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound i j k l
  simpa [topKernelReverseReesFamily] using hfamily

/-- Scalar-pivot slot used by one 1+3 Schur orientation in the
kernel-last coordinate chart. -/
def TopKernelThreeSchurClockData.pivotSlot
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Fin 4 := by
  cases S with
  | pivotA => exact 0
  | pivotD => exact 1
  | pivotX => exact 2

/-- The three non-pivot slots, in exactly the order used by the corresponding
cleared 1+3 Schur matrix. -/
def TopKernelThreeSchurClockData.quotientSlot
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Fin 3 → Fin 4 := by
  cases S with
  | pivotA => exact ![(1 : Fin 4), 2, 3]
  | pivotD => exact ![(0 : Fin 4), 2, 3]
  | pivotX => exact ![(0 : Fin 4), 1, 3]

/-- Every entry of the cleared 1+3 Schur matrix is literally an arbitrary
Hessian 2x2 minor of the honest reverse-Rees family, after the kernel-last
source permutation.  This generalises the two projected first-break entries
used below and is the source-lift needed by determinant closure. -/
set_option maxHeartbeats 1500000 in
theorem threeSchurEntry_eq_parameterFirst_familyMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData)
    (i j : Fin 3) :
    let rho := kernelLastPerm kernelCoordinate
    let pivot := rho S.pivotSlot
    let other := rho (S.quotientSlot i)
    let kernel := rho (S.quotientSlot j)
    S.toExactZeroThreeSchurClock.zeroSeries.matrix i j =
      parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          T.topKernelReverseReesFamily pivot other pivot kernel) := by
  let rho := kernelLastPerm kernelCoordinate
  cases S with
  | pivotA hpivot hzero hdet =>
      fin_cases i <;> fin_cases j <;>
        simp [TopKernelThreeSchurClockData.pivotSlot,
          TopKernelThreeSchurClockData.quotientSlot,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor,
          threeSchurBlock, rho, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrix,
          mul_comm, mul_left_comm, mul_assoc]
  | pivotD hpivot hzero hdet =>
      fin_cases i <;> fin_cases j <;>
        simp [TopKernelThreeSchurClockData.pivotSlot,
          TopKernelThreeSchurClockData.quotientSlot,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor,
          threeSchurBlock, rho, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixD,
          mul_comm, mul_left_comm, mul_assoc]
  | pivotX hpivot hzero hdet =>
      fin_cases i <;> fin_cases j <;>
        simp [TopKernelThreeSchurClockData.pivotSlot,
          TopKernelThreeSchurClockData.quotientSlot,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor,
          threeSchurBlock, rho, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixX,
          mul_comm, mul_left_comm, mul_assoc]

/-- Any nonzero coefficient of any cleared 1+3 Schur entry therefore lifts to
a genuine nonzero Hessian 2x2 minor of the represented determinant-one
source. -/
theorem sourceTwoByTwoMinor_of_threeSchurEntry_coeff_ne_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData)
    (i j : Fin 3)
    (n : ℕ)
    (hne :
      (S.toExactZeroThreeSchurClock.zeroSeries.matrix i j).coeff n ≠ 0) :
    ∃ a b c d : Fin 4,
      hessianTwoByTwoMinor T.topKernelReesSource a b c d ≠ 0 := by
  let rho := kernelLastPerm kernelCoordinate
  let pivot := rho S.pivotSlot
  let other := rho (S.quotientSlot i)
  let kernel := rho (S.quotientSlot j)
  have hcoeff :
      (parameterFirstEquiv K
        (familyHessianTwoByTwoMinor
          T.topKernelReverseReesFamily pivot other pivot kernel)).coeff n ≠ 0 := by
    rw [← P.threeSchurEntry_eq_parameterFirst_familyMinor S i j]
    exact hne
  exact ⟨pivot, other, pivot, kernel,
    P.sourceTwoByTwoMinor_of_parameterFirst_coeff_ne_zero
      pivot other pivot kernel n hcoeff⟩

set_option maxHeartbeats 800000 in
/-- The projected first-break quotient branch contains a genuine nonzero
arbitrary Hessian minor of the represented source. -/
theorem projectedRankTwo_sourceTwoByTwoMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
    (G : ThreeSchurProjectedRankTwoAtFirstBreak S M) :
    ∃ i j k l : Fin 4,
      hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0 := by
  rcases G with ⟨index, hopen, _hminor⟩
  let rho := kernelLastPerm kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have lift
      (i j k l : Fin 4)
      (h :
        (parameterFirstEquiv K
          (familyHessianTwoByTwoMinor
            T.topKernelReverseReesFamily i j k l)).coeff
              M.mixed.layer.order ≠ 0) :
      hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0 :=
    P.sourceTwoByTwoMinor_of_parameterFirst_coeff_ne_zero
      i j k l M.mixed.layer.order h
  cases S with
  | pivotA hpivot hzero hdet =>
      fin_cases index
      · refine ⟨rho 0, rho 1, rho 0, rho 3, lift _ _ _ _ ?_⟩
        simpa [threeSchurCoefficientMatrixAtFirstBreak,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor,
          threeSchurBlock, rho, B, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrix] using hopen
      · refine ⟨rho 0, rho 2, rho 0, rho 3, lift _ _ _ _ ?_⟩
        simpa [threeSchurCoefficientMatrixAtFirstBreak,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor,
          threeSchurBlock, rho, B, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrix] using hopen
  | pivotD hpivot hzero hdet =>
      fin_cases index
      · refine ⟨rho 0, rho 1, rho 3, rho 1, lift _ _ _ _ ?_⟩
        simpa [threeSchurCoefficientMatrixAtFirstBreak,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor_commuted,
          threeSchurBlock, rho, B, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixD,
          mul_comm] using hopen
      · refine ⟨rho 2, rho 1, rho 3, rho 1, lift _ _ _ _ ?_⟩
        simpa [threeSchurCoefficientMatrixAtFirstBreak,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor_commuted_cross,
          threeSchurBlock, rho, B, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixD,
          mul_comm] using hopen
  | pivotX hpivot hzero hdet =>
      fin_cases index
      · refine ⟨rho 0, rho 2, rho 3, rho 2, lift _ _ _ _ ?_⟩
        simpa [threeSchurCoefficientMatrixAtFirstBreak,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor_commuted,
          threeSchurBlock, rho, B, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixX,
          mul_comm] using hopen
      · refine ⟨rho 1, rho 2, rho 3, rho 2, lift _ _ _ _ ?_⟩
        simpa [threeSchurCoefficientMatrixAtFirstBreak,
          TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          parameterFirstEquiv_familyHessianPivotMinor_commuted,
          threeSchurBlock, rho, B, kernelLastFamilyHessianFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          kernelLastParameterFirstHessian,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixX,
          mul_comm] using hopen

/-- **Projected C/D seam closed at the represented source.**

The quotient mixed opening yields an honest exact-active Hessian chart of the
actual presented blocker state. -/
theorem projectedRankTwo_exactActiveFourBlock
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
    (G : ThreeSchurProjectedRankTwoAtFirstBreak S M) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalExactActiveFourBlock
        T.terminal.blocker.presented) := by
  rcases P.projectedRankTwo_sourceTwoByTwoMinor S M G with
    ⟨i, j, k, l, hminor⟩
  apply exactActiveFourBlock_of_specialFiber_twoByTwoMinor_ne_zero
    T.terminal.blocker.presented i j k l
  simpa [topKernelReesSource] using hminor

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
