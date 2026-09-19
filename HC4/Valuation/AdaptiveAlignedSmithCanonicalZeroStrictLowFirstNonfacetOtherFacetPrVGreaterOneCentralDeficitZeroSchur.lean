import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitSchurSeries
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitRankThreeRoof
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
variable {K : Type u} [Field K]

variable [CharZero K] [IsAlgClosed K]
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

private theorem centralDeficit_p_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.p.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_p_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficit_q_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.q.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_q_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficit_r_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.r.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_r_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficit_s_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.s.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_s_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficit_x_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.x.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_x_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficit_y_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.y.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_y_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficit_z_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.z.coeff 0 = 0 := by
  unfold centralDeficitSchurBlock
  rw [centralDeficitSchurBlockOf_z_coeff_zero,
    G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero, G.central_two_zero,
    -standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C]

private theorem centralDeficitSchurBlock_schurA_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.schurA.coeff 0 = 0 := by
  change Polynomial.constantCoeff G.centralDeficitSchurBlock.schurA = 0
  rw [← GeneralFourBlock.schurA_map
    G.centralDeficitSchurBlock Polynomial.constantCoeff]
  simp only [GeneralFourBlock.map, GeneralFourBlock.schurA,
    GeneralFourBlock.activeDet, Polynomial.constantCoeff_apply]
  rw [G.centralDeficit_p_coeff_zero hthree houtThree,
    G.centralDeficit_r_coeff_zero hthree houtThree,
    G.centralDeficit_x_coeff_zero hthree houtThree]
  ring

private theorem centralDeficitSchurBlock_schurB_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.schurB.coeff 0 = 0 := by
  change Polynomial.constantCoeff G.centralDeficitSchurBlock.schurB = 0
  rw [← GeneralFourBlock.schurB_map
    G.centralDeficitSchurBlock Polynomial.constantCoeff]
  simp only [GeneralFourBlock.map, GeneralFourBlock.schurB,
    GeneralFourBlock.activeDet, Polynomial.constantCoeff_apply]
  rw [G.centralDeficit_p_coeff_zero hthree houtThree,
    G.centralDeficit_q_coeff_zero hthree houtThree,
    G.centralDeficit_r_coeff_zero hthree houtThree,
    G.centralDeficit_s_coeff_zero hthree houtThree,
    G.centralDeficit_y_coeff_zero hthree houtThree]
  ring

private theorem centralDeficitSchurBlock_schurC_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.schurC.coeff 0 = 0 := by
  change Polynomial.constantCoeff G.centralDeficitSchurBlock.schurC = 0
  rw [← GeneralFourBlock.schurC_map
    G.centralDeficitSchurBlock Polynomial.constantCoeff]
  simp only [GeneralFourBlock.map, GeneralFourBlock.schurC,
    GeneralFourBlock.activeDet, Polynomial.constantCoeff_apply]
  rw [G.centralDeficit_q_coeff_zero hthree houtThree,
    G.centralDeficit_s_coeff_zero hthree houtThree,
    G.centralDeficit_z_coeff_zero hthree houtThree]
  ring

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
  unfold centralDeficitSchurBlock
  rw [show
    (centralDeficitSchurBlockOf P.centralDeficitFamily).schurA =
      ((centralDeficitSchurBlockOf P.centralDeficitFamily).a *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).d -
        (centralDeficitSchurBlockOf P.centralDeficitFamily).b *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).b) *
        (centralDeficitSchurBlockOf P.centralDeficitFamily).x -
      ((centralDeficitSchurBlockOf P.centralDeficitFamily).d *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).p *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).p -
        2 * (centralDeficitSchurBlockOf P.centralDeficitFamily).b *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).p *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).r +
        (centralDeficitSchurBlockOf P.centralDeficitFamily).a *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).r *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).r) by
      rfl]
  simp only [centralDeficitSchurBlockOf,
    permutedFamilyHessianFourBlock_a, permutedFamilyHessianFourBlock_b,
    permutedFamilyHessianFourBlock_d, permutedFamilyHessianFourBlock_p,
    permutedFamilyHessianFourBlock_r, permutedFamilyHessianFourBlock_x,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one,
    centralDeficitSchurPerm_two]
  unfold firstDeficitRightActiveHessian
  rw [Matrix.det_fin_three]
  simp only [firstDeficitRightActiveIndex]
  rw [parameterFirstHessian_symmetric P.centralDeficitFamily (2 : Fin 4) 0,
    parameterFirstHessian_symmetric P.centralDeficitFamily (2 : Fin 4) 3,
    parameterFirstHessian_symmetric P.centralDeficitFamily (3 : Fin 4) 0]
  ring

/-- Second principal cleared Schur entry equals the left roof determinant. -/
theorem centralDeficitSchurC_eq_leftRoofDet :
    G.centralDeficitSchurBlock.schurC =
      G.firstDeficitLeftActiveHessian.det := by
  unfold centralDeficitSchurBlock
  rw [show
    (centralDeficitSchurBlockOf P.centralDeficitFamily).schurC =
      ((centralDeficitSchurBlockOf P.centralDeficitFamily).a *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).d -
        (centralDeficitSchurBlockOf P.centralDeficitFamily).b *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).b) *
        (centralDeficitSchurBlockOf P.centralDeficitFamily).z -
      ((centralDeficitSchurBlockOf P.centralDeficitFamily).d *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).q *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).q -
        2 * (centralDeficitSchurBlockOf P.centralDeficitFamily).b *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).q *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).s +
        (centralDeficitSchurBlockOf P.centralDeficitFamily).a *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).s *
          (centralDeficitSchurBlockOf P.centralDeficitFamily).s) by
      rfl]
  simp only [centralDeficitSchurBlockOf,
    permutedFamilyHessianFourBlock_a, permutedFamilyHessianFourBlock_b,
    permutedFamilyHessianFourBlock_d, permutedFamilyHessianFourBlock_q,
    permutedFamilyHessianFourBlock_s, permutedFamilyHessianFourBlock_z,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one,
    centralDeficitSchurPerm_three]
  unfold firstDeficitLeftActiveHessian
  rw [Matrix.det_fin_three]
  simp only [firstDeficitLeftActiveIndex]
  rw [parameterFirstHessian_symmetric P.centralDeficitFamily (1 : Fin 4) 0,
    parameterFirstHessian_symmetric P.centralDeficitFamily (1 : Fin 4) 3,
    parameterFirstHessian_symmetric P.centralDeficitFamily (3 : Fin 4) 0]
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
