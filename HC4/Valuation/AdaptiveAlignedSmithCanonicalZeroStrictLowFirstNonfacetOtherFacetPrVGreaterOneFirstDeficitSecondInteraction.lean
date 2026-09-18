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
      rcases G.exists_leftStaggeredBreakData
          hthree houtThree hfirst hfirst1 hfirst2 huniq
          hop (by omega) hstrict hminimal with
        ⟨E, hblock, hactive, hkernel⟩
      have hb0 : E.block.b.coeff 0 = 0 := by
        rw [hblock]
        exact G.left_base_b_zero hthree houtThree
      have hd0 : E.block.d.coeff 0 = 0 := by
        rw [hblock]
        exact G.left_base_d_zero hthree houtThree
      have hr0 : E.block.r.coeff 0 = 0 := by
        rw [hblock]
        exact G.left_base_r_zero hthree houtThree
      have houter :
          E.block.a.coeff 0 * E.block.x.coeff 0 -
              E.block.p.coeff 0 * E.block.p.coeff 0 ≠ 0 := by
        rw [hblock]
        exact G.left_base_outer_minor_ne_zero hthree houtThree
      have hsj : E.block.s.coeff E.kernelOrder ≠ 0 := by
        rw [hblock, hkernel]
        exact hmixed
      have hz :=
        E.kernelDiagonal_coeff_secondInteraction_ne_zero
          hb0 hd0 hr0 houter hsj
      have hz' :
          G.firstDeficitLeftStaggeredBlock.z.coeff
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) ≠ 0 := by
        rw [← hblock, ← hkernel, ← hactive]
        exact hz
      exact .left first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop2
        hstrict hminimal hB hlayer hmixed hz'
  | right first opposite B hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal hB hlayer hmixed =>
      rcases G.exists_rightStaggeredBreakData
          hthree houtThree hfirst hfirst1 hfirst2 huniq
          hop (by omega) hstrict hminimal with
        ⟨E, hblock, hactive, hkernel⟩
      have hb0 : E.block.b.coeff 0 = 0 := by
        rw [hblock]
        exact G.right_base_b_zero hthree houtThree
      have hd0 : E.block.d.coeff 0 = 0 := by
        rw [hblock]
        exact G.right_base_d_zero hthree houtThree
      have hr0 : E.block.r.coeff 0 = 0 := by
        rw [hblock]
        exact G.right_base_r_zero hthree houtThree
      have houter :
          E.block.a.coeff 0 * E.block.x.coeff 0 -
              E.block.p.coeff 0 * E.block.p.coeff 0 ≠ 0 := by
        rw [hblock]
        exact G.right_base_outer_minor_ne_zero hthree houtThree
      have hsj : E.block.s.coeff E.kernelOrder ≠ 0 := by
        rw [hblock, hkernel]
        exact hmixed
      have hz :=
        E.kernelDiagonal_coeff_secondInteraction_ne_zero
          hb0 hd0 hr0 houter hsj
      have hz' :
          G.firstDeficitRightStaggeredBlock.z.coeff
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) ≠ 0 := by
        rw [← hblock, ← hkernel, ← hactive]
        exact hz
      exact .right first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop1
        hstrict hminimal hB hlayer hmixed hz'

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
