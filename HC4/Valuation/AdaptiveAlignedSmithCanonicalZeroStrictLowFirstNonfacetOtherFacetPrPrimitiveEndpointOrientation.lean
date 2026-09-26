import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrQuotientFiber
import HC4.Polynomial.PrimitiveBinomialAffineMoment
import Mathlib.Tactic

/-!
# A19 source-honest PR primitive endpoint orientation

The highest `.pr` planar slice is already an exact affine-RR reconstruction of
the represented source, with coefficient support `{0,1}` and locked direction

    (1, -1, -alpha, -beta).

The state-free primitive-binomial Hessian theorem now applies directly to its
polynomial moment Hessian.  Since the highest pair level is greater than one,
the base pair coordinate is at least two.  The result is the exact two-way
orientation used by the paper closure:

* `(0,n,1,beta*n) -> (1,n-1,0,beta*(n-1))`, or
* its transverse swap `(0,n,alpha*n,1) -> (1,n-1,alpha*(n-1),0)`.

This theorem keeps the original source-honest affine-RR package and uses its
literal coefficients; no reconstructed carrier and no balance hypothesis is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **Source-honest primitive endpoint orientation.** -/
theorem QsOtherFacetPlanarAffineRRPackage.pr_primitive_endpoint_orientation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    (A : QsOtherFacetPlanarAffineRRPackage C .pr P S)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (D : QsPrLockedQuotientData C) :
    (A.ray.facetExponent 2 = D.alpha ∧ D.alpha = 1 ∧
        A.ray.facetExponent 3 = D.beta * A.ray.facetExponent 1) ∨
      (A.ray.facetExponent 3 = D.beta ∧ D.beta = 1 ∧
        A.ray.facetExponent 2 = D.alpha * A.ray.facetExponent 1) := by
  have hfacetMem : A.ray.facetExponent ∈ S.slice.support := by
    rw [← A.face_eq]
    exact A.ray.facet_mem_face
  have hfacet0 : A.ray.facetExponent (0 : Fin 4) = 0 :=
    A.ray.facet_coordinate_zero
  have hpair := (S.support_parent_and_pairLevel hfacetMem).2
  have hpairBase : (A.ray.facetExponent 1 : ℤ) = S.pairLevel := by
    simpa [qsOtherFacetPairDegree, hfacet0] using hpair
  have hnZ : (1 : ℤ) < (A.ray.facetExponent 1 : ℤ) := by
    rw [hpairBase]
    exact S.pairLevel_gt_one
  have hn : 2 ≤ A.ray.facetExponent 1 := by
    have hnNat : 1 < A.ray.facetExponent 1 := by exact_mod_cast hnZ
    omega

  have hphiSupp : A.ray.zeroCoefficientPolynomial.support = {0, 1} :=
    A.coefficient_support_eq_zero_one hthree
      (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have hphi0 : A.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    A.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hphi1 : A.ray.zeroCoefficientPolynomial.coeff 1 ≠ 0 := by
    apply Polynomial.mem_support_iff.mp
    rw [hphiSupp]
    simp

  have honeSupp : 1 ∈ A.ray.zeroCoefficientPolynomial.support := by
    rw [hphiSupp]
    simp
  rcases A.ray.exists_faceExponent_of_zeroCoefficientPolynomial_mem honeSupp with
    ⟨e1, he1Face, he10⟩
  have he1Mem : e1 ∈ S.slice.support := by
    rw [← A.face_eq]
    exact he1Face

  rcases D.direction_eq hthree houtThree with ⟨hd0, hd1, hd2, hd3⟩
  have hline2 := S.support_difference_parallel_ray
    hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
    he1Mem hfacetMem (2 : Fin 4)
  have hline3 := S.support_difference_parallel_ray
    hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
    he1Mem hfacetMem (3 : Fin 4)
  rw [he10, hfacet0, hd2] at hline2
  rw [he10, hfacet0, hd3] at hline3
  norm_num at hline2 hline3
  have hpEqZ :
      (A.ray.facetExponent 2 : ℤ) = (e1 2 : ℤ) + (D.alpha : ℤ) := by
    omega
  have hqEqZ :
      (A.ray.facetExponent 3 : ℤ) = (e1 3 : ℤ) + (D.beta : ℤ) := by
    omega
  have hpEq : A.ray.facetExponent 2 = e1 2 + D.alpha := by
    exact_mod_cast hpEqZ
  have hqEq : A.ray.facetExponent 3 = e1 3 + D.beta := by
    exact_mod_cast hqEqZ
  have hpLower : D.alpha ≤ A.ray.facetExponent 2 := by omega
  have hqLower : D.beta ≤ A.ray.facetExponent 3 := by omega

  have hs1 := A.slope_eq_locked (1 : Fin 4)
  have hs2 := A.slope_eq_locked (2 : Fin 4)
  have hs3 := A.slope_eq_locked (3 : Fin 4)
  rw [hd1] at hs1
  rw [hd2] at hs2
  rw [hd3] at hs3
  have hs1' : A.ray.zeroSlope (1 : Fin 4) = (-1 : K) := by
    simpa using hs1
  have hs2' : A.ray.zeroSlope (2 : Fin 4) = -(D.alpha : K) := by
    simpa using hs2
  have hs3' : A.ray.zeroSlope (3 : Fin 4) = -(D.beta : K) := by
    simpa using hs3

  have hlineDet :
      hessianDeterminant A.ray.zeroAffineLineData.polynomial = 0 :=
    A.ray.zeroAffineLineData_hessian_zero S.hessian_zero
  have hmoment :
      (rankThreeAffinePolynomialMomentHessian
        (A.ray.facetExponent 1)
        (A.ray.facetExponent 2)
        (A.ray.facetExponent 3) 1
        (A.ray.zeroSlope (1 : Fin 4))
        (A.ray.zeroSlope (2 : Fin 4))
        (A.ray.zeroSlope (3 : Fin 4))
        A.ray.zeroCoefficientPolynomial).det = 0 :=
    A.ray.zeroAffineLineData.polynomialMoment_det_zero_of_hessian_zero
      (by norm_num) hlineDet
  rw [hs1', hs2', hs3'] at hmoment

  exact primitiveBinomial_endpoint_orientation_of_affineMoment_det_zero
    hn D.alpha_pos D.beta_pos hpLower hqLower
    hphiSupp hphi0 hphi1 hmoment

/-- Direct highest-slice entry: every nontrivial source-honest `.pr` highest
slice carries one of the two exact primitive orientations. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.exists_pr_primitive_orientation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial : ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ (D : QsPrLockedQuotientData C)
        (A : QsOtherFacetPlanarAffineRRPackage C .pr P S),
      (A.ray.facetExponent 2 = D.alpha ∧ D.alpha = 1 ∧
          A.ray.facetExponent 3 = D.beta * A.ray.facetExponent 1) ∨
        (A.ray.facetExponent 3 = D.beta ∧ D.beta = 1 ∧
          A.ray.facetExponent 2 = D.alpha * A.ray.facetExponent 1) := by
  let D := C.qsPrLockedQuotientData hthree houtThree
  rcases S.primitive_of_nontrivial hthree
      (by decide : (.pr : ToricFacet) ≠ .qs) houtThree hnontrivial with
    ⟨A, _hsupp⟩
  exact ⟨D, A, A.pr_primitive_endpoint_orientation hthree houtThree D⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
