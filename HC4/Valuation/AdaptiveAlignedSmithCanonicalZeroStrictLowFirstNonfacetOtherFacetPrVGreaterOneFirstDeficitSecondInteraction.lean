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

private theorem generalFourBlock_d_coeff_eq_matrix_11_coeff
    {R : Type*} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) (n : ℕ) :
    H.d.coeff n = (H.matrix (1 : Fin 4) 1).coeff n := by
  rfl

private theorem generalFourBlock_s_coeff_eq_matrix_13_coeff
    {R : Type*} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) (n : ℕ) :
    H.s.coeff n = (H.matrix (1 : Fin 4) 3).coeff n := by
  rfl

private theorem generalFourBlock_z_coeff_eq_matrix_33_coeff
    {R : Type*} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) (n : ℕ) :
    H.z.coeff n = (H.matrix (3 : Fin 4) 3).coeff n := by
  rfl

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
      (mixed_hessian_ne_zero :
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))
          (1 : Fin 4) 2 ≠ 0)
      (second_diagonal_ne_zero :
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
          (2 : Fin 4) 2 ≠ 0)
      (second_interaction_identity :
        HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily G.firstDeficitOrder)
            (1 : Fin 4) 1 *
          HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily
              (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
            (2 : Fin 4) 2 =
          HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily
                (opposite 1 + opposite 2))
              (1 : Fin 4) 2 *
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily
                (opposite 1 + opposite 2))
              (1 : Fin 4) 2)
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
      (mixed_hessian_ne_zero :
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))
          (2 : Fin 4) 1 ≠ 0)
      (second_diagonal_ne_zero :
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
          (1 : Fin 4) 1 ≠ 0)
      (second_interaction_identity :
        HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily G.firstDeficitOrder)
            (2 : Fin 4) 2 *
          HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily
              (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
            (1 : Fin 4) 1 =
          HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily
                (opposite 1 + opposite 2))
              (2 : Fin 4) 1 *
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily
                (opposite 1 + opposite 2))
              (2 : Fin 4) 1)

/-- Left branch of the source-honest second interaction.  Kept opaque
separately so kernel checking does not accumulate the right-oriented proof
term in the same declaration. -/
private theorem firstDeficit_secondInteractionGeometry_left
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ} {B : K}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2 : opposite 2 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    (hB : B ≠ 0)
    (hlayer :
      familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2) =
        MvPolynomial.monomial opposite B)
    (hmixed :
      G.firstDeficitLeftStaggeredBlock.s.coeff
        (opposite 1 + opposite 2) ≠ 0) :
    G.FirstDeficitSecondInteractionGeometry := by

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
  have hactiveFactor :
      (firstKernelBreakActiveThreeDet E.block).coeff E.activeOrder =
        (E.block.a.coeff 0 * E.block.x.coeff 0 -
          E.block.p.coeff 0 * E.block.p.coeff 0) *
          E.block.d.coeff E.activeOrder := by
    rw [hblock, hactive]
    exact
      G.firstDeficitLeftStaggeredBlock_activeCoeff_eq_outer_mul_middle
        hthree houtThree
  have heq :=
    E.kernelDiagonal_secondInteraction_cancelled
      hb0 hd0 hr0 houter hactiveFactor
  have hz :=
    E.kernelDiagonal_coeff_secondInteraction_ne_zero
      hb0 hd0 hr0 houter hsj
  have hmatrix :
      E.block.matrix = G.firstDeficitLeftStaggeredMatrix := by
    calc
      E.block.matrix = G.firstDeficitLeftStaggeredBlock.matrix := by
        exact congrArg GeneralFourBlock.matrix hblock
      _ = G.firstDeficitLeftStaggeredMatrix :=
        G.firstDeficitLeftStaggeredBlock_matrix
  have hdMatrix :
      E.block.d.coeff E.activeOrder =
        (G.firstDeficitLeftStaggeredMatrix (1 : Fin 4) 1).coeff
          G.firstDeficitOrder := by
    calc
      E.block.d.coeff E.activeOrder =
          (E.block.matrix (1 : Fin 4) 1).coeff E.activeOrder :=
        generalFourBlock_d_coeff_eq_matrix_11_coeff E.block E.activeOrder
      _ = (G.firstDeficitLeftStaggeredMatrix
            (1 : Fin 4) 1).coeff E.activeOrder := by
        rw [hmatrix]
      _ = (G.firstDeficitLeftStaggeredMatrix
            (1 : Fin 4) 1).coeff G.firstDeficitOrder := by
        rw [hactive]
  have hsMatrix :
      E.block.s.coeff E.kernelOrder =
        (G.firstDeficitLeftStaggeredMatrix (1 : Fin 4) 3).coeff
          (opposite 1 + opposite 2) := by
    calc
      E.block.s.coeff E.kernelOrder =
          (E.block.matrix (1 : Fin 4) 3).coeff E.kernelOrder :=
        generalFourBlock_s_coeff_eq_matrix_13_coeff E.block E.kernelOrder
      _ = (G.firstDeficitLeftStaggeredMatrix
            (1 : Fin 4) 3).coeff E.kernelOrder := by
        rw [hmatrix]
      _ = (G.firstDeficitLeftStaggeredMatrix
            (1 : Fin 4) 3).coeff (opposite 1 + opposite 2) := by
        rw [hkernel]
  have hzMatrix :
      E.block.z.coeff (2 * E.kernelOrder - E.activeOrder) =
        (G.firstDeficitLeftStaggeredMatrix (3 : Fin 4) 3).coeff
          (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) := by
    calc
      E.block.z.coeff (2 * E.kernelOrder - E.activeOrder) =
          (E.block.matrix (3 : Fin 4) 3).coeff
            (2 * E.kernelOrder - E.activeOrder) :=
        generalFourBlock_z_coeff_eq_matrix_33_coeff E.block
          (2 * E.kernelOrder - E.activeOrder)
      _ = (G.firstDeficitLeftStaggeredMatrix
            (3 : Fin 4) 3).coeff
            (2 * E.kernelOrder - E.activeOrder) := by
        rw [hmatrix]
      _ = (G.firstDeficitLeftStaggeredMatrix
            (3 : Fin 4) 3).coeff
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) := by
        rw [hkernel, hactive]
  rw [G.firstDeficitLeftStaggeredMatrix_apply,
    firstDeficitLeftStaggeredPerm_one,
    parameterFirstHessian_coeff] at hdMatrix
  rw [G.firstDeficitLeftStaggeredMatrix_apply,
    firstDeficitLeftStaggeredPerm_one,
    firstDeficitLeftStaggeredPerm_three,
    parameterFirstHessian_coeff] at hsMatrix
  rw [G.firstDeficitLeftStaggeredMatrix_apply,
    firstDeficitLeftStaggeredPerm_three,
    parameterFirstHessian_coeff] at hzMatrix
  have hmixedSource :
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2))
        (1 : Fin 4) 2 ≠ 0 := by
    rw [← hsMatrix]
    exact hsj
  have hz' :
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily
          (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
        (2 : Fin 4) 2 ≠ 0 := by
    rw [← hzMatrix]
    exact hz
  have heq' :
      HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            G.firstDeficitOrder)
          (1 : Fin 4) 1 *
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
          (2 : Fin 4) 2 =
      HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))
          (1 : Fin 4) 2 *
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))
          (1 : Fin 4) 2 := by
    rw [← hdMatrix, ← hzMatrix, ← hsMatrix]
    exact heq
  exact .left first opposite B
    hfirst hfirst1 hfirst2 huniq hop hop2
    hstrict hminimal hB hlayer hmixedSource hz' heq'

/-- Right-oriented branch of the source-honest second interaction. -/
private theorem firstDeficit_secondInteractionGeometry_right
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ} {B : K}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1 : opposite 1 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    (hB : B ≠ 0)
    (hlayer :
      familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2) =
        MvPolynomial.monomial opposite B)
    (hmixed :
      G.firstDeficitRightStaggeredBlock.s.coeff
        (opposite 1 + opposite 2) ≠ 0) :
    G.FirstDeficitSecondInteractionGeometry := by

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
  have hactiveFactor :
      (firstKernelBreakActiveThreeDet E.block).coeff E.activeOrder =
        (E.block.a.coeff 0 * E.block.x.coeff 0 -
          E.block.p.coeff 0 * E.block.p.coeff 0) *
          E.block.d.coeff E.activeOrder := by
    rw [hblock, hactive]
    exact
      G.firstDeficitRightStaggeredBlock_activeCoeff_eq_outer_mul_middle
        hthree houtThree
  have heq :=
    E.kernelDiagonal_secondInteraction_cancelled
      hb0 hd0 hr0 houter hactiveFactor
  have hz :=
    E.kernelDiagonal_coeff_secondInteraction_ne_zero
      hb0 hd0 hr0 houter hsj
  have hmatrix :
      E.block.matrix = G.firstDeficitRightStaggeredMatrix := by
    calc
      E.block.matrix = G.firstDeficitRightStaggeredBlock.matrix := by
        exact congrArg GeneralFourBlock.matrix hblock
      _ = G.firstDeficitRightStaggeredMatrix :=
        G.firstDeficitRightStaggeredBlock_matrix
  have hdMatrix :
      E.block.d.coeff E.activeOrder =
        (G.firstDeficitRightStaggeredMatrix (1 : Fin 4) 1).coeff
          G.firstDeficitOrder := by
    calc
      E.block.d.coeff E.activeOrder =
          (E.block.matrix (1 : Fin 4) 1).coeff E.activeOrder :=
        generalFourBlock_d_coeff_eq_matrix_11_coeff E.block E.activeOrder
      _ = (G.firstDeficitRightStaggeredMatrix
            (1 : Fin 4) 1).coeff E.activeOrder := by
        rw [hmatrix]
      _ = (G.firstDeficitRightStaggeredMatrix
            (1 : Fin 4) 1).coeff G.firstDeficitOrder := by
        rw [hactive]
  have hsMatrix :
      E.block.s.coeff E.kernelOrder =
        (G.firstDeficitRightStaggeredMatrix (1 : Fin 4) 3).coeff
          (opposite 1 + opposite 2) := by
    calc
      E.block.s.coeff E.kernelOrder =
          (E.block.matrix (1 : Fin 4) 3).coeff E.kernelOrder :=
        generalFourBlock_s_coeff_eq_matrix_13_coeff E.block E.kernelOrder
      _ = (G.firstDeficitRightStaggeredMatrix
            (1 : Fin 4) 3).coeff E.kernelOrder := by
        rw [hmatrix]
      _ = (G.firstDeficitRightStaggeredMatrix
            (1 : Fin 4) 3).coeff (opposite 1 + opposite 2) := by
        rw [hkernel]
  have hzMatrix :
      E.block.z.coeff (2 * E.kernelOrder - E.activeOrder) =
        (G.firstDeficitRightStaggeredMatrix (3 : Fin 4) 3).coeff
          (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) := by
    calc
      E.block.z.coeff (2 * E.kernelOrder - E.activeOrder) =
          (E.block.matrix (3 : Fin 4) 3).coeff
            (2 * E.kernelOrder - E.activeOrder) :=
        generalFourBlock_z_coeff_eq_matrix_33_coeff E.block
          (2 * E.kernelOrder - E.activeOrder)
      _ = (G.firstDeficitRightStaggeredMatrix
            (3 : Fin 4) 3).coeff
            (2 * E.kernelOrder - E.activeOrder) := by
        rw [hmatrix]
      _ = (G.firstDeficitRightStaggeredMatrix
            (3 : Fin 4) 3).coeff
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder) := by
        rw [hkernel, hactive]
  rw [G.firstDeficitRightStaggeredMatrix_apply,
    firstDeficitRightStaggeredPerm_one,
    parameterFirstHessian_coeff] at hdMatrix
  rw [G.firstDeficitRightStaggeredMatrix_apply,
    firstDeficitRightStaggeredPerm_one,
    firstDeficitRightStaggeredPerm_three,
    parameterFirstHessian_coeff] at hsMatrix
  rw [G.firstDeficitRightStaggeredMatrix_apply,
    firstDeficitRightStaggeredPerm_three,
    parameterFirstHessian_coeff] at hzMatrix
  have hmixedSource :
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2))
        (2 : Fin 4) 1 ≠ 0 := by
    rw [← hsMatrix]
    exact hsj
  have hz' :
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily
          (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
        (1 : Fin 4) 1 ≠ 0 := by
    rw [← hzMatrix]
    exact hz
  have heq' :
      HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            G.firstDeficitOrder)
          (2 : Fin 4) 2 *
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (2 * (opposite 1 + opposite 2) - G.firstDeficitOrder))
          (1 : Fin 4) 1 =
      HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))
          (2 : Fin 4) 1 *
        HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))
          (2 : Fin 4) 1 := by
    rw [← hdMatrix, ← hzMatrix, ← hsMatrix]
    exact heq
  exact .right first opposite B
    hfirst hfirst1 hfirst2 huniq hop hop1
    hstrict hminimal hB hlayer hmixedSource hz' heq'

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
      exact G.firstDeficit_secondInteractionGeometry_left
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop hop2 hstrict hminimal hB hlayer hmixed
  | right first opposite B hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal hB hlayer hmixed =>
      exact G.firstDeficit_secondInteractionGeometry_right
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop hop1 hstrict hminimal hB hlayer hmixed

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
