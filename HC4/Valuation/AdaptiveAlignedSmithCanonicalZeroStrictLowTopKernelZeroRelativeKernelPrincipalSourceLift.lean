import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativeBinaryProvenance
import HC4.Valuation.ReverseWeightedReesHessianPrincipalMinor
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Represented-source kernel principal minor in the zero-relative branch

The canonical D3 pivot is the (2,2) diagonal entry of the normalised first
three-Schur tail.  Nonvanishing of its constant coefficient makes the raw
(2,2) first-Schur polynomial nonzero.  For the three possible first scalar
pivots this raw polynomial is exactly the parameter-first image of the
whole-family principal Hessian minor joining that pivot coordinate to the
kernel-last coordinate.

The existing whole-family reverse-Rees principal-minor lift then transports
that nonvanishing to the represented determinant-one source itself.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem parameterFirstEquiv_hessianPrincipalMinor_eq_square_zeroRelative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor P i j) =
      parameterFirstHessian P i i * parameterFirstHessian P j j -
        parameterFirstHessian P i j * parameterFirstHessian P i j := by
  have hsym :
      HC4.Polynomial.hessian P j i =
        HC4.Polynomial.hessian P i j := by
    change
      MvPolynomial.pderiv i (MvPolynomial.pderiv j P) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i P)
    exact pderiv_comm_commRing i j P
  unfold HC4.Polynomial.hessianPrincipalMinor
  simp only [map_sub, map_mul]
  rw [hsym]
  simp [parameterFirstHessian]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

private theorem familyKernelMinor0_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.threeSchurBlock.a * P.threeSchurBlock.z -
        P.threeSchurBlock.q * P.threeSchurBlock.q =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 0)
          (kernelLastPerm kernelCoordinate 3)) := by
  unfold TopFaceLinearPowerKernelData.threeSchurBlock
    kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square_zeroRelative
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate 0)
      (kernelLastPerm kernelCoordinate 3)).symm

private theorem familyKernelMinor1_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.threeSchurBlock.d * P.threeSchurBlock.z -
        P.threeSchurBlock.s * P.threeSchurBlock.s =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 1)
          (kernelLastPerm kernelCoordinate 3)) := by
  unfold TopFaceLinearPowerKernelData.threeSchurBlock
    kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square_zeroRelative
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate 1)
      (kernelLastPerm kernelCoordinate 3)).symm

private theorem familyKernelMinor2_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.threeSchurBlock.x * P.threeSchurBlock.z -
        P.threeSchurBlock.y * P.threeSchurBlock.y =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 2)
          (kernelLastPerm kernelCoordinate 3)) := by
  unfold TopFaceLinearPowerKernelData.threeSchurBlock
    kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square_zeroRelative
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate 2)
      (kernelLastPerm kernelCoordinate 3)).symm

/-- Honest represented-source principal Hessian minor obtained from the
zero-relative kernel-column opening. -/
inductive ZeroRelativeRepresentedSourceKernelMinorWitness
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Prop
  | minor0
      (hne :
        HC4.Polynomial.hessianPrincipalMinor T.topKernelReesSource
          (kernelLastPerm kernelCoordinate 0)
          (kernelLastPerm kernelCoordinate 3) ≠ 0)
  | minor1
      (hne :
        HC4.Polynomial.hessianPrincipalMinor T.topKernelReesSource
          (kernelLastPerm kernelCoordinate 1)
          (kernelLastPerm kernelCoordinate 3) ≠ 0)
  | minor2
      (hne :
        HC4.Polynomial.hessianPrincipalMinor T.topKernelReesSource
          (kernelLastPerm kernelCoordinate 2)
          (kernelLastPerm kernelCoordinate 3) ≠ 0)

private theorem TopKernelThreeSchurClockData.raw_pivot2_entry_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (h2 :
      S.toExactZeroThreeSchurClock.tailConstantMatrix 2 2 ≠ 0) :
    S.toExactZeroThreeSchurClock.zeroSeries.matrix 2 2 ≠ 0 := by
  let E := S.toExactZeroThreeSchurClock
  have htail :
      E.zeroSeries.tailMatrix E.hasPositiveEntryLayer 2 2 ≠ 0 := by
    intro hz
    apply h2
    change (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer 2 2).coeff 0 = 0
    rw [hz]
    simp
  rw [E.zeroSeries.entry_eq_firstFactor_mul_tail
    E.hasPositiveEntryLayer 2 2]
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) htail

private theorem sourceMinor0_of_raw_pivot2
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hpoly :
      P.threeSchurBlock.a * P.threeSchurBlock.z -
          P.threeSchurBlock.q * P.threeSchurBlock.q ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor T.topKernelReesSource
        (kernelLastPerm kernelCoordinate 0)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 0)
          (kernelLastPerm kernelCoordinate 3)) ≠ 0 := by
    rw [← P.familyKernelMinor0_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor T.topKernelReverseReesFamily
        (kernelLastPerm kernelCoordinate 0)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  apply reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
    T.topKernelReesSource_hasReverseWeightBound
    (kernelLastPerm kernelCoordinate 0)
    (kernelLastPerm kernelCoordinate 3)
  simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReverseReesFamily]
    using hfamily

private theorem sourceMinor1_of_raw_pivot2
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hpoly :
      P.threeSchurBlock.d * P.threeSchurBlock.z -
          P.threeSchurBlock.s * P.threeSchurBlock.s ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor T.topKernelReesSource
        (kernelLastPerm kernelCoordinate 1)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 1)
          (kernelLastPerm kernelCoordinate 3)) ≠ 0 := by
    rw [← P.familyKernelMinor1_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor T.topKernelReverseReesFamily
        (kernelLastPerm kernelCoordinate 1)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  apply reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
    T.topKernelReesSource_hasReverseWeightBound
    (kernelLastPerm kernelCoordinate 1)
    (kernelLastPerm kernelCoordinate 3)
  simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReverseReesFamily]
    using hfamily

private theorem sourceMinor2_of_raw_pivot2
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hpoly :
      P.threeSchurBlock.x * P.threeSchurBlock.z -
          P.threeSchurBlock.y * P.threeSchurBlock.y ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor T.topKernelReesSource
        (kernelLastPerm kernelCoordinate 2)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 2)
          (kernelLastPerm kernelCoordinate 3)) ≠ 0 := by
    rw [← P.familyKernelMinor2_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor T.topKernelReverseReesFamily
        (kernelLastPerm kernelCoordinate 2)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  apply reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
    T.topKernelReesSource_hasReverseWeightBound
    (kernelLastPerm kernelCoordinate 2)
    (kernelLastPerm kernelCoordinate 3)
  simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReverseReesFamily]
    using hfamily

/-- The canonical zero-relative pivot2 clock already carries a nonzero
principal Hessian minor on the represented determinant-one source. -/
theorem ZeroRelativeExplicitBinaryClockData.representedSourceKernelMinor
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.ZeroRelativeExplicitBinaryClockData S) :
    P.ZeroRelativeRepresentedSourceKernelMinorWitness := by
  have hraw := S.raw_pivot2_entry_ne_zero B.pivot2_ne_zero
  cases S with
  | pivotA hpivot hzero hdet =>
      have hpoly :
          P.threeSchurBlock.a * P.threeSchurBlock.z -
              P.threeSchurBlock.q * P.threeSchurBlock.q ≠ 0 := by
        simpa [TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          GeneralFourBlock.rankOneClearedThreeSchurMatrix] using hraw
      exact .minor0 (P.sourceMinor0_of_raw_pivot2 hpoly)
  | pivotD hpivot hzero hdet =>
      have hpoly :
          P.threeSchurBlock.d * P.threeSchurBlock.z -
              P.threeSchurBlock.s * P.threeSchurBlock.s ≠ 0 := by
        simpa [TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixD] using hraw
      exact .minor1 (P.sourceMinor1_of_raw_pivot2 hpoly)
  | pivotX hpivot hzero hdet =>
      have hpoly :
          P.threeSchurBlock.x * P.threeSchurBlock.z -
              P.threeSchurBlock.y * P.threeSchurBlock.y ≠ 0 := by
        simpa [TopKernelThreeSchurClockData.toExactZeroThreeSchurClock,
          GeneralFourBlock.rankOneClearedThreeSchurMatrixX] using hraw
      exact .minor2 (P.sourceMinor2_of_raw_pivot2 hpoly)


/-- Any represented-source kernel minor emitted by the zero-relative branch
already yields a nonempty actual rank-two Hessian chart on the literal
presented state.  The witness itself is a proposition, so we keep the
elimination target in Prop and choose the chart only afterwards. -/
theorem ZeroRelativeRepresentedSourceKernelMinorWitness.exists_actualRankTwoHessianChart
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (W : P.ZeroRelativeRepresentedSourceKernelMinorWitness) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  cases W with
  | minor0 hminor =>
      have hne :
          kernelLastPerm kernelCoordinate 0 ≠
            kernelLastPerm kernelCoordinate 3 := by
        intro h
        have h' : (0 : Fin 4) = 3 :=
          (kernelLastPerm kernelCoordinate).injective h
        have hval : (0 : Nat) = 3 := congrArg Fin.val h'
        norm_num at hval
      refine ⟨actualRankTwoHessianChart_of_specialFiber_minor hne ?_⟩
      simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReesSource]
        using hminor
  | minor1 hminor =>
      have hne :
          kernelLastPerm kernelCoordinate 1 ≠
            kernelLastPerm kernelCoordinate 3 := by
        intro h
        have h' : (1 : Fin 4) = 3 :=
          (kernelLastPerm kernelCoordinate).injective h
        have hval : (1 : Nat) = 3 := congrArg Fin.val h'
        norm_num at hval
      refine ⟨actualRankTwoHessianChart_of_specialFiber_minor hne ?_⟩
      simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReesSource]
        using hminor
  | minor2 hminor =>
      have hne :
          kernelLastPerm kernelCoordinate 2 ≠
            kernelLastPerm kernelCoordinate 3 := by
        intro h
        have h' : (2 : Fin 4) = 3 :=
          (kernelLastPerm kernelCoordinate).injective h
        have hval : (2 : Nat) = 3 := congrArg Fin.val h'
        norm_num at hval
      refine ⟨actualRankTwoHessianChart_of_specialFiber_minor hne ?_⟩
      simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReesSource]
        using hminor

/-- Chosen actual rank-two Hessian chart carried by a represented-source
kernel-minor witness. -/
noncomputable def ZeroRelativeRepresentedSourceKernelMinorWitness.actualRankTwoHessianChart
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (W : P.ZeroRelativeRepresentedSourceKernelMinorWitness) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented :=
  Classical.choice W.exists_actualRankTwoHessianChart

/-- The canonical zero-relative explicit binary packet therefore already
contains an actual represented-state rank-two Hessian chart. -/
noncomputable def ZeroRelativeExplicitBinaryClockData.actualRankTwoHessianChart
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.ZeroRelativeExplicitBinaryClockData S) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented :=
  B.representedSourceKernelMinor.actualRankTwoHessianChart

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
