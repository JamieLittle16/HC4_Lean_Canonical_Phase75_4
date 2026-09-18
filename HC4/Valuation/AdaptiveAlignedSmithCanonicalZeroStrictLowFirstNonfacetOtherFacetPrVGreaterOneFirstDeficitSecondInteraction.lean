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

private theorem generalFourBlock_baseFacts_of_activeSubmatrix
    {R : Type*} [CommRing R]
    (H : GeneralFourBlock (Polynomial R))
    (A : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsub :
      H.matrix.submatrix Fin.castSucc Fin.castSucc = A)
    (hmiddle :
      (A 0 1).coeff 0 = 0 ∧
      (A 1 1).coeff 0 = 0 ∧
      (A 1 2).coeff 0 = 0)
    (houter :
      (A 0 0).coeff 0 * (A 2 2).coeff 0 -
        (A 0 2).coeff 0 * (A 2 0).coeff 0 ≠ 0) :
    H.b.coeff 0 = 0 ∧
      H.d.coeff 0 = 0 ∧
      H.r.coeff 0 = 0 ∧
      (H.a.coeff 0 * H.x.coeff 0 -
        H.p.coeff 0 * H.p.coeff 0 ≠ 0) := by
  have h01 := congrFun (congrFun hsub (0 : Fin 3)) (1 : Fin 3)
  have h11 := congrFun (congrFun hsub (1 : Fin 3)) (1 : Fin 3)
  have h12 := congrFun (congrFun hsub (1 : Fin 3)) (2 : Fin 3)
  have h00 := congrFun (congrFun hsub (0 : Fin 3)) (0 : Fin 3)
  have h02 := congrFun (congrFun hsub (0 : Fin 3)) (2 : Fin 3)
  have h20 := congrFun (congrFun hsub (2 : Fin 3)) (0 : Fin 3)
  have h22 := congrFun (congrFun hsub (2 : Fin 3)) (2 : Fin 3)
  have hb : H.b = A 0 1 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h01
  have hd : H.d = A 1 1 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h11
  have hr : H.r = A 1 2 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h12
  have ha : H.a = A 0 0 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h00
  have hp02 : H.p = A 0 2 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h02
  have hp20 : H.p = A 2 0 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h20
  have hA20 : A 2 0 = A 0 2 :=
    hp20.symm.trans hp02
  have hx : H.x = A 2 2 := by
    simpa [Matrix.submatrix_apply, GeneralFourBlock.matrix] using h22
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hb]
    exact hmiddle.1
  · rw [hd]
    exact hmiddle.2.1
  · rw [hr]
    exact hmiddle.2.2
  · rw [hA20] at houter
    simpa [ha, hx, hp02] using houter

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
      (second_interaction_eq :
        G.firstDeficitLeftStaggeredBlock.d.coeff G.firstDeficitOrder *
            G.firstDeficitLeftStaggeredBlock.z.coeff
              (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) =
          G.firstDeficitLeftStaggeredBlock.s.coeff
              (opposite 1 + opposite 2) *
            G.firstDeficitLeftStaggeredBlock.s.coeff
              (opposite 1 + opposite 2))
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
      (second_interaction_eq :
        G.firstDeficitRightStaggeredBlock.d.coeff G.firstDeficitOrder *
            G.firstDeficitRightStaggeredBlock.z.coeff
              (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) =
          G.firstDeficitRightStaggeredBlock.s.coeff
              (opposite 1 + opposite 2) *
            G.firstDeficitRightStaggeredBlock.s.coeff
              (opposite 1 + opposite 2))

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
      have hsub :
          E.block.matrix.submatrix Fin.castSucc Fin.castSucc =
            G.firstDeficitLeftActiveHessian := by
        rw [hblock]
        exact G.firstDeficitLeftStaggeredBlock_activeSubmatrix_eq
      have hmiddle :=
        G.firstDeficitLeftActiveHessian_base_middle_zero
          hthree houtThree
      have houterRaw :=
        G.firstDeficitLeftActiveHessian_base_outer_minor_ne_zero
          hthree houtThree
      rcases generalFourBlock_baseFacts_of_activeSubmatrix
          E.block G.firstDeficitLeftActiveHessian
          hsub hmiddle houterRaw with
        ⟨hb0, hd0, hr0, houter⟩
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
      have hinteraction :=
        E.activeCoeff_mul_kernelDiagonal_secondInteraction_eq_outer_mul_mixed_sq
          hb0 hd0 hr0
      have hinteractionG := hinteraction
      rw [hblock, hactive, hkernel] at hinteractionG
      have houterG := houter
      rw [hblock] at houterG
      have hactiveFactor :
          (firstKernelBreakActiveThreeDet
              G.firstDeficitLeftStaggeredBlock).coeff
              G.firstDeficitOrder =
            (G.firstDeficitLeftStaggeredBlock.a.coeff 0 *
                G.firstDeficitLeftStaggeredBlock.x.coeff 0 -
              G.firstDeficitLeftStaggeredBlock.p.coeff 0 *
                G.firstDeficitLeftStaggeredBlock.p.coeff 0) *
              G.firstDeficitLeftStaggeredBlock.d.coeff
                G.firstDeficitOrder := by
        rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq,
          G.firstDeficitLeftActiveHessian_det_coeff_first_eq
            hthree houtThree]
        unfold firstDeficitLeftStaggeredBlock
          firstDeficitLeftStaggeredMatrix
          GeneralFourBlock.ofSymmetricMatrix
        simp only [Matrix.submatrix_apply]
        simp [firstDeficitLeftStaggeredPerm]
        repeat' rw [parameterFirstHessian_coeff]
        rw [G.layer_zero_eq_exposure hthree houtThree]
        rfl
      rw [hactiveFactor] at hinteractionG
      rw [mul_assoc] at hinteractionG
      have heq :
          G.firstDeficitLeftStaggeredBlock.d.coeff G.firstDeficitOrder *
              G.firstDeficitLeftStaggeredBlock.z.coeff
                (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) =
            G.firstDeficitLeftStaggeredBlock.s.coeff
                (opposite 1 + opposite 2) *
              G.firstDeficitLeftStaggeredBlock.s.coeff
                (opposite 1 + opposite 2) :=
        mul_left_cancel₀ houterG hinteractionG
      exact .left first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop2
        hstrict hminimal hB hlayer hmixed hz' heq
  | right first opposite B hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal hB hlayer hmixed =>
      rcases G.exists_rightStaggeredBreakData
          hthree houtThree hfirst hfirst1 hfirst2 huniq
          hop (by omega) hstrict hminimal with
        ⟨E, hblock, hactive, hkernel⟩
      have hsub :
          E.block.matrix.submatrix Fin.castSucc Fin.castSucc =
            G.firstDeficitRightActiveHessian := by
        rw [hblock]
        exact G.firstDeficitRightStaggeredBlock_activeSubmatrix_eq
      have hmiddle :=
        G.firstDeficitRightActiveHessian_base_middle_zero
          hthree houtThree
      have houterRaw :=
        G.firstDeficitRightActiveHessian_base_outer_minor_ne_zero
          hthree houtThree
      rcases generalFourBlock_baseFacts_of_activeSubmatrix
          E.block G.firstDeficitRightActiveHessian
          hsub hmiddle houterRaw with
        ⟨hb0, hd0, hr0, houter⟩
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
      have hinteraction :=
        E.activeCoeff_mul_kernelDiagonal_secondInteraction_eq_outer_mul_mixed_sq
          hb0 hd0 hr0
      have hinteractionG := hinteraction
      rw [hblock, hactive, hkernel] at hinteractionG
      have houterG := houter
      rw [hblock] at houterG
      have hactiveFactor :
          (firstKernelBreakActiveThreeDet
              G.firstDeficitRightStaggeredBlock).coeff
              G.firstDeficitOrder =
            (G.firstDeficitRightStaggeredBlock.a.coeff 0 *
                G.firstDeficitRightStaggeredBlock.x.coeff 0 -
              G.firstDeficitRightStaggeredBlock.p.coeff 0 *
                G.firstDeficitRightStaggeredBlock.p.coeff 0) *
              G.firstDeficitRightStaggeredBlock.d.coeff
                G.firstDeficitOrder := by
        rw [G.firstDeficitRightStaggeredBlock_activeThree_eq,
          G.firstDeficitRightActiveHessian_det_coeff_first_eq
            hthree houtThree]
        unfold firstDeficitRightStaggeredBlock
          firstDeficitRightStaggeredMatrix
          GeneralFourBlock.ofSymmetricMatrix
        simp only [Matrix.submatrix_apply]
        simp [firstDeficitRightStaggeredPerm]
        repeat' rw [parameterFirstHessian_coeff]
        rw [G.layer_zero_eq_exposure hthree houtThree]
        rfl
      rw [hactiveFactor] at hinteractionG
      rw [mul_assoc] at hinteractionG
      have heq :
          G.firstDeficitRightStaggeredBlock.d.coeff G.firstDeficitOrder *
              G.firstDeficitRightStaggeredBlock.z.coeff
                (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) =
            G.firstDeficitRightStaggeredBlock.s.coeff
                (opposite 1 + opposite 2) *
              G.firstDeficitRightStaggeredBlock.s.coeff
                (opposite 1 + opposite 2) :=
        mul_left_cancel₀ houterG hinteractionG
      exact .right first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop1
        hstrict hminimal hB hlayer hmixed hz' heq

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
