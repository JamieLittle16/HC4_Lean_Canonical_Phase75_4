import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitOppositeLayer
import HC4.Valuation.StaggeredSingularSecondKernelInteraction
import Mathlib.Tactic

/-!
# Second source-honest interaction after the primitive opposite opening

The first deficit layer opens one central direction at order `q`.  The least
later source monomial opening the opposite direction occurs at order `j>q`,
is unique in its exact layer, and is linear in the missing coordinate.  Its
specific mixed Hessian coefficient `s_j` is nonzero.

The state-free second-interaction theorem now applies to the complete honest
central-deficit Hessian.  The special fibre has the exact rank-two form needed
there: in the reordered active block its middle row/column vanishes, while the
outer `(0,3)` principal minor is the retained nonzero central minor.

Hence the missing diagonal remains zero strictly below `2*j-q` and is forced
nonzero at exactly `2*j-q`.

This file is only the source adapter.  No truncation, repair transition, or
identification with a Smith/blocker clock is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

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

private theorem centralParameterHessian_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (i j : Fin 4) :
    (parameterFirstHessian P.centralDeficitFamily i j).coeff 0 =
      HC4.Polynomial.hessian G.exposure.face i j := by
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree,
    G.exposure_face_eq]

private theorem left_base_b_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.b.coeff 0 = 0 := by
  unfold firstDeficitLeftStaggeredBlock firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitLeftStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree]
  rw [G.exposure_face_eq]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero]

private theorem left_base_d_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.d.coeff 0 = 0 := by
  unfold firstDeficitLeftStaggeredBlock firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitLeftStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree]
  rw [G.exposure_face_eq]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero]

private theorem left_base_r_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.r.coeff 0 = 0 := by
  unfold firstDeficitLeftStaggeredBlock firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitLeftStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree]
  rw [G.exposure_face_eq]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_one_zero]

private theorem right_base_b_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.b.coeff 0 = 0 := by
  unfold firstDeficitRightStaggeredBlock firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitRightStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree]
  rw [G.exposure_face_eq]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_two_zero]

private theorem right_base_d_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.d.coeff 0 = 0 := by
  unfold firstDeficitRightStaggeredBlock firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitRightStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree]
  rw [G.exposure_face_eq]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_two_zero]

private theorem right_base_r_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.r.coeff 0 = 0 := by
  unfold firstDeficitRightStaggeredBlock firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitRightStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree]
  rw [G.exposure_face_eq]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_monomial,
    G.central_two_zero]

/-- In either staggered orientation, the outer active constant minor is exactly
the retained central `(0,3)` principal Hessian minor. -/
private theorem left_base_outer_minor_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.a.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.x.coeff 0 -
        G.firstDeficitLeftStaggeredBlock.p.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.p.coeff 0 ≠ 0 := by
  unfold firstDeficitLeftStaggeredBlock firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitLeftStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree,
    G.centralParameterHessian_coeff_zero hthree houtThree,
    G.centralParameterHessian_coeff_zero hthree houtThree]
  simpa [HC4.Polynomial.hessianPrincipalMinor] using
    G.exposure_rankTwo_minor

private theorem right_base_outer_minor_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.a.coeff 0 *
          G.firstDeficitRightStaggeredBlock.x.coeff 0 -
        G.firstDeficitRightStaggeredBlock.p.coeff 0 *
          G.firstDeficitRightStaggeredBlock.p.coeff 0 ≠ 0 := by
  unfold firstDeficitRightStaggeredBlock firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitRightStaggeredPerm]
  rw [G.centralParameterHessian_coeff_zero hthree houtThree,
    G.centralParameterHessian_coeff_zero hthree houtThree,
    G.centralParameterHessian_coeff_zero hthree houtThree]
  simpa [HC4.Polynomial.hessianPrincipalMinor] using
    G.exposure_rankTwo_minor

private noncomputable def leftSecondInteractionData
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2 : 0 < opposite 2)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    StaggeredSingularFirstKernelBreakFourBlockData
      (MvPolynomial (Fin 4) K) := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  refine {
    block := G.firstDeficitLeftStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitLeftStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := ?_
    q_lower_zero := ?_
    s_lower_zero := ?_
    y_lower_zero := ?_
    z_lower_zero := ?_
    determinantCore_eq_zero :=
      G.firstDeficitLeftStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitLeftStaggeredBlock_kernel_break
        hop hop2 hstrict hfirstTwo
  }
  · rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq]
    exact G.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
  · intro n hn
    exact G.leftBlock_q_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.leftBlock_s_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.leftBlock_y_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.leftBlock_z_coeff_eq_zero_before hminimal hn

private noncomputable def rightSecondInteractionData
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1 : 0 < opposite 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    StaggeredSingularFirstKernelBreakFourBlockData
      (MvPolynomial (Fin 4) K) := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  refine {
    block := G.firstDeficitRightStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitRightStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := ?_
    q_lower_zero := ?_
    s_lower_zero := ?_
    y_lower_zero := ?_
    z_lower_zero := ?_
    determinantCore_eq_zero :=
      G.firstDeficitRightStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitRightStaggeredBlock_kernel_break
        hop hop1 hstrict hfirstTwo
  }
  · rw [G.firstDeficitRightStaggeredBlock_activeThree_eq]
    exact G.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
  · intro n hn
    exact G.rightBlock_q_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.rightBlock_s_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.rightBlock_y_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.rightBlock_z_coeff_eq_zero_before hminimal hn

/-- Provenance-rich second interaction forced by the zero full determinant. -/
inductive FirstDeficitSecondInteractionGeometry : Prop
  | left
      (first opposite : Fin 4 →₀ ℕ) (B : K)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = G.firstDeficitOrder)
      (first_two : first 2 = 0)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two : opposite 2 = 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 2 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)
      (coefficient_ne_zero : B ≠ 0)
      (layer_eq :
        familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2) =
          MvPolynomial.monomial opposite B)
      (mixed_coeff_ne_zero :
        G.firstDeficitLeftStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0)
      (second_diagonal_ne_zero :
        G.firstDeficitLeftStaggeredBlock.z.coeff
          (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) ≠ 0)
  | right
      (first opposite : Fin 4 →₀ ℕ) (B : K)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = G.firstDeficitOrder)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one : opposite 1 = 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 1 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)
      (coefficient_ne_zero : B ≠ 0)
      (layer_eq :
        familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2) =
          MvPolynomial.monomial opposite B)
      (mixed_coeff_ne_zero :
        G.firstDeficitRightStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0)
      (second_diagonal_ne_zero :
        G.firstDeficitRightStaggeredBlock.z.coeff
          (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) ≠ 0)

/-- **Second source-honest interaction.**  The determinant forces the missing
diagonal to open at exactly `2*j-q`. -/
theorem firstDeficit_secondInteractionGeometry
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitSecondInteractionGeometry := by
  rcases G.firstDeficit_oppositeLayerGeometry hthree houtThree with O
  cases O with
  | left first opposite B hfirst hfirst1 hfirst2 huniq
      hop hop2 hstrict hminimal hB hlayer hmixed =>
      let E := G.leftSecondInteractionData
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop (by omega) hstrict hminimal
      have hsj : E.block.s.coeff E.kernelOrder ≠ 0 := by
        change G.firstDeficitLeftStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0
        exact hmixed
      have hz :=
        E.kernelDiagonal_coeff_secondInteraction_ne_zero
          (G.left_base_b_zero hthree houtThree)
          (G.left_base_d_zero hthree houtThree)
          (G.left_base_r_zero hthree houtThree)
          (G.left_base_outer_minor_ne_zero hthree houtThree)
          hsj
      have hz' :
          G.firstDeficitLeftStaggeredBlock.z.coeff
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) ≠ 0 := by
        change E.block.z.coeff
          (2 * E.kernelOrder - E.activeOrder) ≠ 0
        exact hz
      exact .left first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop2
        hstrict hminimal hB hlayer hmixed hz'
  | right first opposite B hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal hB hlayer hmixed =>
      let E := G.rightSecondInteractionData
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop (by omega) hstrict hminimal
      have hsj : E.block.s.coeff E.kernelOrder ≠ 0 := by
        change G.firstDeficitRightStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0
        exact hmixed
      have hz :=
        E.kernelDiagonal_coeff_secondInteraction_ne_zero
          (G.right_base_b_zero hthree houtThree)
          (G.right_base_d_zero hthree houtThree)
          (G.right_base_r_zero hthree houtThree)
          (G.right_base_outer_minor_ne_zero hthree houtThree)
          hsj
      have hz' :
          G.firstDeficitRightStaggeredBlock.z.coeff
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) ≠ 0 := by
        change E.block.z.coeff
          (2 * E.kernelOrder - E.activeOrder) ≠ 0
        exact hz
      exact .right first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop1
        hstrict hminimal hB hlayer hmixed hz'

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
