import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrQuotientFiber
import HC4.Polynomial.PrimitiveBinomialAffineMoment
import Mathlib.Tactic

/-!
# A19 source-honest PR primitive endpoint orientation

The highest nontrivial `.pr` planar slice is already known to be an exact
source-honest affine RR line with coefficient support `{0,1}`.  The locked
quotient direction is `(1,-1,-alpha,-beta)`.  This file feeds that *actual*
slice into the state-free primitive-binomial affine-moment classification.

The conclusion is geometric: one of the two positive transverse drops is
exactly one, and the boundary endpoint has the corresponding forced shape.
Thus the common locked direction of all planar quotient fibers is, up to the
symmetric orientation, `(1,-1,-1,-V)`.
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

/-- **Actual `.pr` primitive endpoint orientation.**

For every nontrivial highest pair slice, the source-honest affine RR package
has one of the two primitive endpoint shapes forced by its singular Hessian.
No balance hypothesis, generic JC2 input, copied coefficient polynomial, or
auxiliary defect identification is used. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_endpoint_orientation_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ (D : QsPrLockedQuotientData C)
        (A : QsOtherFacetPlanarAffineRRPackage C .pr P S),
      (A.ray.facetExponent 2 = D.alpha ∧
          D.alpha = 1 ∧
          A.ray.facetExponent 3 = D.beta * A.ray.facetExponent 1) ∨
        (A.ray.facetExponent 3 = D.beta ∧
          D.beta = 1 ∧
          A.ray.facetExponent 2 = D.alpha * A.ray.facetExponent 1) := by
  let D := C.qsPrLockedQuotientData hthree houtThree
  rcases S.affineRRPackage_of_nontrivial
      hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree hnontrivial with
    ⟨A⟩

  let phi := A.ray.zeroCoefficientPolynomial
  let L := A.ray.zeroAffineLineData

  have hsupp : phi.support = {0, 1} := by
    dsimp [phi]
    exact A.coefficient_support_eq_zero_one hthree
      (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have hphi0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    exact A.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have h1supp : 1 ∈ phi.support := by
    rw [hsupp]
    simp
  have hphi1 : phi.coeff 1 ≠ 0 :=
    Polynomial.mem_support_iff.mp h1supp

  have hbaseS : A.ray.facetExponent ∈ S.slice.support := by
    rw [← A.face_eq]
    exact A.ray.facet_mem_face
  have hpair :
      qsOtherFacetPairDegree .pr A.ray.facetExponent = S.pairLevel :=
    (S.support_parent_and_pairLevel hbaseS).2
  have hpairn :
      (A.ray.facetExponent 1 : ℤ) = S.pairLevel := by
    simpa [qsOtherFacetPairDegree, A.ray.facet_coordinate_zero] using hpair
  have hnZ : (1 : ℤ) < (A.ray.facetExponent 1 : ℤ) := by
    rw [hpairn]
    exact S.pairLevel_gt_one
  have hn : 2 ≤ A.ray.facetExponent 1 := by
    exact_mod_cast hnZ

  rcases A.ray.exists_faceExponent_of_zeroCoefficientPolynomial_mem h1supp with
    ⟨e1, he1face, he10⟩
  have he1S : e1 ∈ S.slice.support := by
    rw [← A.face_eq]
    exact he1face
  have hq := S.pr_quotient_eq_of_mem hthree houtThree D hbaseS he1S
  have hshape := primitive_pair_shape_of_quotient_eq_zero_one
    D.alpha D.beta A.ray.facetExponent e1 hq
    A.ray.facet_coordinate_zero he10
  have hpa : D.alpha ≤ A.ray.facetExponent 2 := by omega
  have hbq : D.beta ≤ A.ray.facetExponent 3 := by omega

  have hdir := D.direction_eq hthree houtThree
  have hs1 : A.ray.zeroSlope 1 = -(1 : K) := by
    rw [A.slope_eq_locked (1 : Fin 4), hdir.2.1]
    norm_num
  have hs2 : A.ray.zeroSlope 2 = -(D.alpha : K) := by
    rw [A.slope_eq_locked (2 : Fin 4), hdir.2.2.1]
    norm_num
  have hs3 : A.ray.zeroSlope 3 = -(D.beta : K) := by
    rw [A.slope_eq_locked (3 : Fin 4), hdir.2.2.2]
    norm_num

  have hLdet : hessianDeterminant L.polynomial = 0 := by
    dsimp [L]
    exact A.ray.zeroAffineLineData_hessian_zero S.hessian_zero
  have hmoment := L.polynomialMoment_det_zero_of_hessian_zero
    (by norm_num : 0 < (1 : ℕ)) hLdet
  change
      (rankThreeAffinePolynomialMomentHessian
        (A.ray.facetExponent 1) (A.ray.facetExponent 2)
        (A.ray.facetExponent 3) 1
        (A.ray.zeroSlope 1) (A.ray.zeroSlope 2) (A.ray.zeroSlope 3)
        phi).det = 0 at hmoment
  rw [hs1, hs2, hs3] at hmoment

  have horient :=
    primitiveBinomial_endpoint_orientation_of_affineMoment_det_zero
      (K := K)
      (n := A.ray.facetExponent 1)
      (p := A.ray.facetExponent 2)
      (q := A.ray.facetExponent 3)
      (alpha := D.alpha) (beta := D.beta) (phi := phi)
      hn D.alpha_pos D.beta_pos hpa hbq hsupp hphi0 hphi1 hmoment
  exact ⟨D, A, horient⟩

/-- The preceding endpoint classification fixes the *global* locked `.pr`
direction itself.  Since the quotient data comes from the original source ray,
the same `V` controls every later fixed-pair fiber, not only the highest slice. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_direction_primitive_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ V : ℕ, 0 < V ∧
      (((C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1 ∧
        (C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1 ∧
        (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1 ∧
        (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -(V : ℤ)) ∨
       ((C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1 ∧
        (C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1 ∧
        (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -(V : ℤ) ∧
        (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1)) := by
  rcases S.pr_endpoint_orientation_of_nontrivial
      hthree houtThree hnontrivial with ⟨D, A, horient⟩
  have hdir := D.direction_eq hthree houtThree
  rcases horient with hleft | hright
  · refine ⟨D.beta, D.beta_pos, Or.inl ⟨hdir.1, hdir.2.1, ?_, hdir.2.2.2⟩⟩
    simpa [hleft.2.1] using hdir.2.2.1
  · refine ⟨D.alpha, D.alpha_pos, Or.inr ⟨hdir.1, hdir.2.1, hdir.2.2.1, ?_⟩⟩
    simpa [hright.2.1] using hdir.2.2.2

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
