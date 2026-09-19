import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitSchurSeries
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitRankThreeRoof
import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianSpecialFiber
import HC4.Newton.ZeroSchurFirstEntryClock
import Mathlib.Tactic

/-!
# Zero-Schur normalisation of the central total-deficit family

The complete source-honest total-deficit Hessian is ordered as
`(0,3 | 2,1)`.  Its layer-zero polynomial is the central monomial and has
zero exponents in source coordinates `1,2`.  Consequently the complete
constant cleared Schur block vanishes.

The two principal cleared Schur entries are, up to simultaneous permutation,
the honest first-deficit roof determinants on source coordinates
`(0,2,3)` and `(0,1,3)`.  The already-verified first-deficit rank-three
roof theorem therefore supplies a genuine positive Schur entry.

This is the exact input required by the generic `ZeroSchurSeries` first-entry
factorisation.  No determinant clock is introduced: the Schur determinant is
identically zero.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

@[simp] theorem centralDeficitSchurPerm_two :
    centralDeficitSchurPerm 2 = 2 := by decide

@[simp] theorem centralDeficitSchurPerm_three :
    centralDeficitSchurPerm 3 = 1 := by decide

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- Parameter-zero specialization of the reordered block. -/
private noncomputable def centralDeficitConstantBlock :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  parameterConstantCoeffFourBlock G.centralDeficitSchurBlock

/-- The constant block has no entries touching either deficit coordinate.
Only the honest `(0,3)` active block can survive. -/
private theorem centralDeficitConstantBlock_sparse
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (G.centralDeficitConstantBlock.p = 0 ∧
      G.centralDeficitConstantBlock.q = 0 ∧
      G.centralDeficitConstantBlock.r = 0 ∧
      G.centralDeficitConstantBlock.s = 0 ∧
      G.centralDeficitConstantBlock.x = 0 ∧
      G.centralDeficitConstantBlock.y = 0 ∧
      G.centralDeficitConstantBlock.z = 0) := by
  have hentry (i j : Fin 4)
      (hi : i = 1 ∨ i = 2 ∨ j = 1 ∨ j = 2) :
      (parameterFirstHessian P.centralDeficitFamily i j).coeff 0 = 0 := by
    rw [parameterFirstHessian_coeff,
      G.centralDeficitFamily_layer_zero_eq hthree houtThree]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [-standardTwoZero_pderiv_two_eq_A,
        -standardTwoZero_pderiv_three_eq_C,
        HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
        G.central_one_zero, G.central_two_zero]
  unfold centralDeficitConstantBlock parameterConstantCoeffFourBlock
    centralDeficitSchurBlock centralDeficitSchurBlockOf
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one,
    centralDeficitSchurPerm_two, centralDeficitSchurPerm_three]
  refine ⟨
    hentry 0 2 (Or.inr (Or.inr (Or.inr rfl))),
    hentry 0 1 (Or.inr (Or.inr (Or.inl rfl))),
    hentry 3 2 (Or.inr (Or.inr (Or.inr rfl))),
    hentry 3 1 (Or.inr (Or.inr (Or.inl rfl))),
    hentry 2 2 (Or.inr (Or.inl rfl)),
    hentry 2 1 (Or.inr (Or.inl rfl)),
    hentry 1 1 (Or.inl rfl)⟩

private theorem centralDeficitSchurBlock_schurA_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.schurA.coeff 0 = 0 := by
  rw [parameterConstantCoeffFourBlock_schurA]
  rcases G.centralDeficitConstantBlock_sparse hthree houtThree with
    ⟨hp, _hq, hr, _hs, hx, _hy, _hz⟩
  change G.centralDeficitConstantBlock.schurA = 0
  simp [GeneralFourBlock.schurA, GeneralFourBlock.activeDet, hp, hr, hx]

private theorem centralDeficitSchurBlock_schurB_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.schurB.coeff 0 = 0 := by
  rw [parameterConstantCoeffFourBlock_schurB]
  rcases G.centralDeficitConstantBlock_sparse hthree houtThree with
    ⟨hp, hq, hr, hs, _hx, hy, _hz⟩
  change G.centralDeficitConstantBlock.schurB = 0
  simp [GeneralFourBlock.schurB, GeneralFourBlock.activeDet,
    hp, hq, hr, hs, hy]

private theorem centralDeficitSchurBlock_schurC_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.schurC.coeff 0 = 0 := by
  rw [parameterConstantCoeffFourBlock_schurC]
  rcases G.centralDeficitConstantBlock_sparse hthree houtThree with
    ⟨_hp, hq, _hr, hs, _hx, _hy, hz⟩
  change G.centralDeficitConstantBlock.schurC = 0
  simp [GeneralFourBlock.schurC, GeneralFourBlock.activeDet, hq, hs, hz]
/-- The complete central Schur block is a genuine zero-constant Schur series. -/
noncomputable def centralDeficitZeroSchurSeries
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ZeroSchurSeries (MvPolynomial (Fin 4) K) where
  series := G.centralDeficitSchurBlock.polynomialSchurSeries
  active_coeff_zero := by
    simpa [GeneralFourBlock.polynomialSchurSeries] using
      G.centralDeficitSchurBlock_schurA_coeff_zero hthree houtThree
  offDiag_coeff_zero := by
    simpa [GeneralFourBlock.polynomialSchurSeries] using
      G.centralDeficitSchurBlock_schurB_coeff_zero hthree houtThree
  kernel_coeff_zero := by
    simpa [GeneralFourBlock.polynomialSchurSeries] using
      G.centralDeficitSchurBlock_schurC_coeff_zero hthree houtThree

/-- First principal cleared Schur entry equals the right roof determinant.
Both are the same `(0,3,2)` principal Hessian determinant with a simultaneous
row/column reordering. -/
theorem centralDeficitSchurA_eq_rightRoofDet :
    G.centralDeficitSchurBlock.schurA =
      G.firstDeficitRightActiveHessian.det := by
  rw [← GeneralFourBlock.firstThreeMinorMatrix_det]
  unfold GeneralFourBlock.firstThreeMinorMatrix
    firstDeficitRightActiveHessian centralDeficitSchurBlock centralDeficitSchurBlockOf
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one,
    centralDeficitSchurPerm_two, centralDeficitSchurPerm_three,
    firstDeficitRightActiveIndex]
  simp [Matrix.det_fin_three]
  have h20 := parameterFirstHessian_symmetric
    P.centralDeficitFamily (2 : Fin 4) 0
  have h23 := parameterFirstHessian_symmetric
    P.centralDeficitFamily (2 : Fin 4) 3
  have h30 := parameterFirstHessian_symmetric
    P.centralDeficitFamily (3 : Fin 4) 0
  rw [h20, h23, h30]
  ring

/-- Second principal cleared Schur entry equals the left roof determinant. -/
theorem centralDeficitSchurC_eq_leftRoofDet :
    G.centralDeficitSchurBlock.schurC =
      G.firstDeficitLeftActiveHessian.det := by
  rw [← GeneralFourBlock.secondThreeMinorMatrix_det]
  unfold GeneralFourBlock.secondThreeMinorMatrix
    firstDeficitLeftActiveHessian centralDeficitSchurBlock centralDeficitSchurBlockOf
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one,
    centralDeficitSchurPerm_two, centralDeficitSchurPerm_three,
    firstDeficitLeftActiveIndex]
  simp [Matrix.det_fin_three]
  have h10 := parameterFirstHessian_symmetric
    P.centralDeficitFamily (1 : Fin 4) 0
  have h13 := parameterFirstHessian_symmetric
    P.centralDeficitFamily (1 : Fin 4) 3
  have h30 := parameterFirstHessian_symmetric
    P.centralDeficitFamily (3 : Fin 4) 0
  rw [h10, h13, h30]
  ring

/-- The zero-Schur series genuinely moves at a positive parameter order. -/
theorem centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (G.centralDeficitZeroSchurSeries hthree houtThree).HasPositiveEntryLayer := by
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  have hroof := G.firstDeficit_activeRankThree hthree houtThree
  have hentry :
      Z.series.active ≠ 0 ∨ Z.series.kernel ≠ 0 := by
    rcases hroof with hleft | hright
    · right
      change G.centralDeficitSchurBlock.schurC ≠ 0
      rw [G.centralDeficitSchurC_eq_leftRoofDet]
      exact hleft
    · left
      change G.centralDeficitSchurBlock.schurA ≠ 0
      rw [G.centralDeficitSchurA_eq_rightRoofDet]
      exact hright
  by_contra hnone
  have hA := Z.active_eq_zero_of_not_hasPositiveEntryLayer hnone
  have hC := Z.kernel_eq_zero_of_not_hasPositiveEntryLayer hnone
  rcases hentry with hne | hne
  · exact hne hA
  · exact hne hC

/-- Since the complete Schur determinant is identically zero, removing the
first common positive Schur order leaves an identically determinant-zero
normalised tail. -/
theorem centralDeficitZeroSchurTail_determinant_eq_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    (Z.tailSeries hz).determinant = 0 := by
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  have hfactor := Z.determinant_eq_firstFactor_sq_mul_tail hz
  have hzero :
      Z.series.determinant = 0 := by
    simpa [Z, centralDeficitZeroSchurSeries] using
      G.centralDeficitSchurSeries_determinant_eq_zero
  rw [hzero] at hfactor
  have hX :
      (Polynomial.X ^ (2 * Z.firstPositiveEntryOrder hz) :
        Polynomial (MvPolynomial (Fin 4) K)) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  exact (mul_eq_zero.mp hfactor.symm).resolve_left hX

/-- The normalised first nonzero Schur layer is a nonzero determinant-zero
symmetric block, hence has a canonical left or right-axis rank-one pivot. -/
theorem centralDeficitZeroSchurTail_pivot
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    (Z.tailSeries hz).LeftPivot ∨ (Z.tailSeries hz).RightAxisPivot := by
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  have hdet := G.centralDeficitZeroSchurTail_determinant_eq_zero
    hthree houtThree
  have hcoeff : (Z.tailSeries hz).determinant.coeff 0 = 0 := by
    rw [hdet]
    simp
  have hrel :
      (Z.tailSeries hz).active.coeff 0 *
          (Z.tailSeries hz).kernel.coeff 0 =
        (Z.tailSeries hz).offDiag.coeff 0 *
          (Z.tailSeries hz).offDiag.coeff 0 := by
    have := hcoeff
    simpa [BinarySchurPolynomialSeries.determinant] using
      (sub_eq_zero.mp (by simpa [BinarySchurPolynomialSeries.determinant] using this))
  exact (Z.tailSeries hz).leftPivot_or_rightAxisPivot_of_constantBlock
    (Z.tailSeries_constantBlock_nonzero hz) hrel

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
