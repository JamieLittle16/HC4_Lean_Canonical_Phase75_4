import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitOppositeOpening
import HC4.Valuation.StaggeredSingularFirstKernelBreakRankTwo
import Mathlib.Tactic

/-!
# Source-honest staggered four-block for the first-deficit branch

The first positive total-deficit layer opens one of the two central kernel
coordinates and gives an honest rank-three roof at order `q`.  The least
later source point opening the opposite deficit coordinate occurs at an order
`j > q`.

This file performs only the representation part of the staggered-break
adapter.  It reorders the complete parameter-first Hessian so that the
already-open rank-three roof occupies coordinates `0,1,2` and the missing
coordinate is `3`.  The resulting `GeneralFourBlock`

* is literally a simultaneous permutation of the complete honest Hessian;
* has identically zero determinant core;
* has active-three determinant exactly the already-certified first-deficit
  roof determinant.

No truncation, repair relabelling, or auxiliary clock identification occurs.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Coordinate order `(0,1,3 | 2)` for the branch whose first layer opens
source coordinate `1`. -/
def firstDeficitLeftStaggeredPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (2 : Fin 4) 3

@[simp] theorem firstDeficitLeftStaggeredPerm_zero :
    firstDeficitLeftStaggeredPerm 0 = 0 := by decide
@[simp] theorem firstDeficitLeftStaggeredPerm_one :
    firstDeficitLeftStaggeredPerm 1 = 1 := by decide
@[simp] theorem firstDeficitLeftStaggeredPerm_two :
    firstDeficitLeftStaggeredPerm 2 = 3 := by decide
@[simp] theorem firstDeficitLeftStaggeredPerm_three :
    firstDeficitLeftStaggeredPerm 3 = 2 := by decide

/-- Coordinate order `(0,2,3 | 1)` for the branch whose first layer opens
source coordinate `2`. -/
def firstDeficitRightStaggeredPerm : Equiv.Perm (Fin 4) where
  toFun i := ![(0 : Fin 4), (2 : Fin 4), (3 : Fin 4), (1 : Fin 4)] i
  invFun i := ![(0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)] i
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

@[simp] theorem firstDeficitRightStaggeredPerm_zero :
    firstDeficitRightStaggeredPerm 0 = 0 := by rfl
@[simp] theorem firstDeficitRightStaggeredPerm_one :
    firstDeficitRightStaggeredPerm 1 = 2 := by rfl
@[simp] theorem firstDeficitRightStaggeredPerm_two :
    firstDeficitRightStaggeredPerm 2 = 3 := by rfl
@[simp] theorem firstDeficitRightStaggeredPerm_three :
    firstDeficitRightStaggeredPerm 3 = 1 := by rfl

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

/-- Complete parameter-first source Hessian, reordered as `(0,1,3 | 2)`. -/
noncomputable def firstDeficitLeftStaggeredMatrix
    (_G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  (parameterFirstHessian P.centralDeficitFamily).submatrix
    firstDeficitLeftStaggeredPerm firstDeficitLeftStaggeredPerm

/-- Complete parameter-first source Hessian, reordered as `(0,2,3 | 1)`. -/
noncomputable def firstDeficitRightStaggeredMatrix
    (_G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  (parameterFirstHessian P.centralDeficitFamily).submatrix
    firstDeficitRightStaggeredPerm firstDeficitRightStaggeredPerm

/-- Four-block attached to the left-axis first-deficit branch. -/
noncomputable def firstDeficitLeftStaggeredBlock
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix G.firstDeficitLeftStaggeredMatrix

/-- Four-block attached to the right-axis first-deficit branch. -/
noncomputable def firstDeficitRightStaggeredBlock
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix G.firstDeficitRightStaggeredMatrix

theorem firstDeficitLeftStaggeredBlock_matrix :
    G.firstDeficitLeftStaggeredBlock.matrix =
      G.firstDeficitLeftStaggeredMatrix := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact parameterFirstHessian_symmetric
    P.centralDeficitFamily
    (firstDeficitLeftStaggeredPerm i)
    (firstDeficitLeftStaggeredPerm j)

theorem firstDeficitRightStaggeredBlock_matrix :
    G.firstDeficitRightStaggeredBlock.matrix =
      G.firstDeficitRightStaggeredMatrix := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact parameterFirstHessian_symmetric
    P.centralDeficitFamily
    (firstDeficitRightStaggeredPerm i)
    (firstDeficitRightStaggeredPerm j)

/-- The left staggered block is still the complete singular source Hessian. -/
theorem firstDeficitLeftStaggeredBlock_determinantCore_eq_zero :
    G.firstDeficitLeftStaggeredBlock.determinantCore = 0 := by
  calc
    G.firstDeficitLeftStaggeredBlock.determinantCore =
        G.firstDeficitLeftStaggeredBlock.matrix.det :=
      (GeneralFourBlock.matrix_det G.firstDeficitLeftStaggeredBlock).symm
    _ = G.firstDeficitLeftStaggeredMatrix.det := by
      rw [G.firstDeficitLeftStaggeredBlock_matrix]
    _ = (parameterFirstHessian P.centralDeficitFamily).det := by
      unfold firstDeficitLeftStaggeredMatrix
      rw [Matrix.det_submatrix_equiv_self]
    _ = 0 := by
      rw [parameterFirstHessian_det,
        P.centralDeficitFamily_hessian_zero]
      simp

/-- The right staggered block is still the complete singular source Hessian. -/
theorem firstDeficitRightStaggeredBlock_determinantCore_eq_zero :
    G.firstDeficitRightStaggeredBlock.determinantCore = 0 := by
  calc
    G.firstDeficitRightStaggeredBlock.determinantCore =
        G.firstDeficitRightStaggeredBlock.matrix.det :=
      (GeneralFourBlock.matrix_det G.firstDeficitRightStaggeredBlock).symm
    _ = G.firstDeficitRightStaggeredMatrix.det := by
      rw [G.firstDeficitRightStaggeredBlock_matrix]
    _ = (parameterFirstHessian P.centralDeficitFamily).det := by
      unfold firstDeficitRightStaggeredMatrix
      rw [Matrix.det_submatrix_equiv_self]
    _ = 0 := by
      rw [parameterFirstHessian_det,
        P.centralDeficitFamily_hessian_zero]
      simp

private theorem firstKernelBreakActiveThreeDet_eq_submatrix_det
    (H : GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K))) :
    firstKernelBreakActiveThreeDet H =
      (H.matrix.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold firstKernelBreakActiveThreeDet GeneralFourBlock.matrix
  simp [Matrix.det_fin_three]
  ring

/-- The active-three determinant of the left staggered block is exactly the
already-certified source roof determinant on coordinates `0,1,3`. -/
theorem firstDeficitLeftStaggeredBlock_activeThree_eq :
    firstKernelBreakActiveThreeDet G.firstDeficitLeftStaggeredBlock =
      G.firstDeficitLeftActiveHessian.det := by
  rw [firstKernelBreakActiveThreeDet_eq_submatrix_det,
    G.firstDeficitLeftStaggeredBlock_matrix]
  have hmatrix :
      G.firstDeficitLeftStaggeredMatrix.submatrix
          Fin.castSucc Fin.castSucc =
        G.firstDeficitLeftActiveHessian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstDeficitLeftStaggeredMatrix,
        firstDeficitLeftActiveHessian,
        firstDeficitLeftActiveIndex]
  exact congrArg Matrix.det hmatrix

/-- Symmetric active-three identification for coordinates `0,2,3`. -/
theorem firstDeficitRightStaggeredBlock_activeThree_eq :
    firstKernelBreakActiveThreeDet G.firstDeficitRightStaggeredBlock =
      G.firstDeficitRightActiveHessian.det := by
  rw [firstKernelBreakActiveThreeDet_eq_submatrix_det,
    G.firstDeficitRightStaggeredBlock_matrix]
  have hmatrix :
      G.firstDeficitRightStaggeredMatrix.submatrix
          Fin.castSucc Fin.castSucc =
        G.firstDeficitRightActiveHessian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstDeficitRightStaggeredMatrix,
        firstDeficitRightActiveHessian,
        firstDeficitRightActiveIndex]
  exact congrArg Matrix.det hmatrix

/-- Constant middle-row entries of the left staggered block, inherited
from the already-certified active roof base. -/
theorem firstDeficitLeftStaggeredBlock_base_b_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.b.coeff 0 = 0 := by
  change (G.firstDeficitLeftActiveHessian 0 1).coeff 0 = 0
  exact (G.firstDeficitLeftActiveHessian_base_middle_zero
    hthree houtThree).1

theorem firstDeficitLeftStaggeredBlock_base_d_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.d.coeff 0 = 0 := by
  change (G.firstDeficitLeftActiveHessian 1 1).coeff 0 = 0
  exact (G.firstDeficitLeftActiveHessian_base_middle_zero
    hthree houtThree).2.1

theorem firstDeficitLeftStaggeredBlock_base_r_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.r.coeff 0 = 0 := by
  change (G.firstDeficitLeftActiveHessian 1 2).coeff 0 = 0
  exact (G.firstDeficitLeftActiveHessian_base_middle_zero
    hthree houtThree).2.2

/-- Right-oriented middle-row base identities. -/
theorem firstDeficitRightStaggeredBlock_base_b_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.b.coeff 0 = 0 := by
  change (G.firstDeficitRightActiveHessian 0 1).coeff 0 = 0
  exact (G.firstDeficitRightActiveHessian_base_middle_zero
    hthree houtThree).1

theorem firstDeficitRightStaggeredBlock_base_d_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.d.coeff 0 = 0 := by
  change (G.firstDeficitRightActiveHessian 1 1).coeff 0 = 0
  exact (G.firstDeficitRightActiveHessian_base_middle_zero
    hthree houtThree).2.1

theorem firstDeficitRightStaggeredBlock_base_r_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.r.coeff 0 = 0 := by
  change (G.firstDeficitRightActiveHessian 1 2).coeff 0 = 0
  exact (G.firstDeficitRightActiveHessian_base_middle_zero
    hthree houtThree).2.2

/-- The staggered outer constant minor is the active roof outer minor. -/
theorem firstDeficitLeftStaggeredBlock_base_outer_minor_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.a.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.x.coeff 0 -
        G.firstDeficitLeftStaggeredBlock.p.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.p.coeff 0 ≠ 0 := by
  change
    (G.firstDeficitLeftActiveHessian 0 0).coeff 0 *
          (G.firstDeficitLeftActiveHessian 2 2).coeff 0 -
        (G.firstDeficitLeftActiveHessian 0 2).coeff 0 *
          (G.firstDeficitLeftActiveHessian 0 2).coeff 0 ≠ 0
  have houter :=
    G.firstDeficitLeftActiveHessian_base_outer_minor_ne_zero
      hthree houtThree
  have hsym :
      (G.firstDeficitLeftActiveHessian 2 0).coeff 0 =
        (G.firstDeficitLeftActiveHessian 0 2).coeff 0 := by
    apply congrArg (fun p => p.coeff 0)
    unfold firstDeficitLeftActiveHessian
    exact parameterFirstHessian_symmetric
      P.centralDeficitFamily 3 0
  rw [hsym] at houter
  exact houter

theorem firstDeficitRightStaggeredBlock_base_outer_minor_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.a.coeff 0 *
          G.firstDeficitRightStaggeredBlock.x.coeff 0 -
        G.firstDeficitRightStaggeredBlock.p.coeff 0 *
          G.firstDeficitRightStaggeredBlock.p.coeff 0 ≠ 0 := by
  change
    (G.firstDeficitRightActiveHessian 0 0).coeff 0 *
          (G.firstDeficitRightActiveHessian 2 2).coeff 0 -
        (G.firstDeficitRightActiveHessian 0 2).coeff 0 *
          (G.firstDeficitRightActiveHessian 0 2).coeff 0 ≠ 0
  have houter :=
    G.firstDeficitRightActiveHessian_base_outer_minor_ne_zero
      hthree houtThree
  have hsym :
      (G.firstDeficitRightActiveHessian 2 0).coeff 0 =
        (G.firstDeficitRightActiveHessian 0 2).coeff 0 := by
    apply congrArg (fun p => p.coeff 0)
    unfold firstDeficitRightActiveHessian
    exact parameterFirstHessian_symmetric
      P.centralDeficitFamily 3 0
  rw [hsym] at houter
  exact houter

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
