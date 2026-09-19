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


/-- On the active three coordinates, the left staggered permutation is
exactly the left active-index embedding. -/
private theorem firstDeficitLeftStaggeredPerm_castSucc
    (i : Fin 3) :
    firstDeficitLeftStaggeredPerm (Fin.castSucc i) =
      firstDeficitLeftActiveIndex i := by
  fin_cases i <;> decide

/-- On the active three coordinates, the right staggered permutation is
exactly the right active-index embedding. -/
private theorem firstDeficitRightStaggeredPerm_castSucc
    (i : Fin 3) :
    firstDeficitRightStaggeredPerm (Fin.castSucc i) =
      firstDeficitRightActiveIndex i := by
  fin_cases i <;> rfl

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

/-- The leading three coordinates of the left staggered block are
literally the already-certified active roof matrix. -/
theorem firstDeficitLeftStaggeredBlock_activeSubmatrix_eq :
    G.firstDeficitLeftStaggeredBlock.matrix.submatrix
        Fin.castSucc Fin.castSucc =
      G.firstDeficitLeftActiveHessian := by
  rw [G.firstDeficitLeftStaggeredBlock_matrix]
  ext i j
  change
    parameterFirstHessian P.centralDeficitFamily
        (firstDeficitLeftStaggeredPerm (Fin.castSucc i))
        (firstDeficitLeftStaggeredPerm (Fin.castSucc j)) =
      parameterFirstHessian P.centralDeficitFamily
        (firstDeficitLeftActiveIndex i)
        (firstDeficitLeftActiveIndex j)
  rw [firstDeficitLeftStaggeredPerm_castSucc,
    firstDeficitLeftStaggeredPerm_castSucc]

/-- Right-oriented active-submatrix identification. -/
theorem firstDeficitRightStaggeredBlock_activeSubmatrix_eq :
    G.firstDeficitRightStaggeredBlock.matrix.submatrix
        Fin.castSucc Fin.castSucc =
      G.firstDeficitRightActiveHessian := by
  rw [G.firstDeficitRightStaggeredBlock_matrix]
  ext i j
  change
    parameterFirstHessian P.centralDeficitFamily
        (firstDeficitRightStaggeredPerm (Fin.castSucc i))
        (firstDeficitRightStaggeredPerm (Fin.castSucc j)) =
      parameterFirstHessian P.centralDeficitFamily
        (firstDeficitRightActiveIndex i)
        (firstDeficitRightActiveIndex j)
  rw [firstDeficitRightStaggeredPerm_castSucc,
    firstDeficitRightStaggeredPerm_castSucc]

/-- The active-three determinant of the left staggered block is exactly the
already-certified source roof determinant on coordinates `0,1,3`. -/
theorem firstDeficitLeftStaggeredBlock_activeThree_eq :
    firstKernelBreakActiveThreeDet G.firstDeficitLeftStaggeredBlock =
      G.firstDeficitLeftActiveHessian.det := by
  rw [firstKernelBreakActiveThreeDet_eq_submatrix_det,
    G.firstDeficitLeftStaggeredBlock_activeSubmatrix_eq]

/-- Symmetric active-three identification for coordinates `0,2,3`. -/
theorem firstDeficitRightStaggeredBlock_activeThree_eq :
    firstKernelBreakActiveThreeDet G.firstDeficitRightStaggeredBlock =
      G.firstDeficitRightActiveHessian.det := by
  rw [firstKernelBreakActiveThreeDet_eq_submatrix_det,
    G.firstDeficitRightStaggeredBlock_activeSubmatrix_eq]


/-- The leading active-three coefficient factors through the nonzero outer
constant principal minor and the first opening of the middle diagonal. -/
theorem firstDeficitLeftStaggeredBlock_activeCoeff_eq_outer_mul_middle
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (firstKernelBreakActiveThreeDet
        G.firstDeficitLeftStaggeredBlock).coeff G.firstDeficitOrder =
      (G.firstDeficitLeftStaggeredBlock.a.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.x.coeff 0 -
        G.firstDeficitLeftStaggeredBlock.p.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.p.coeff 0) *
        G.firstDeficitLeftStaggeredBlock.d.coeff G.firstDeficitOrder := by
  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a := H0 (0 : Fin 4) 0
  let b := H0 (0 : Fin 4) 3
  let c0 := H0 (3 : Fin 4) 0
  let d := H0 (3 : Fin 4) 3
  have hbase : ∀ r s,
      (G.firstDeficitLeftActiveHessian r s).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase a b c0 d r s := by
    intro r s
    simpa [a, b, c0, d, H0] using
      G.firstDeficitLeftActiveHessian_coeff_zero_eq_rankTwoRoofBase
        hthree houtThree r s
  have hcoeff :=
    HC4.Polynomial.coeff_det_polynomialMatrix3_gap
      G.firstDeficitOrder_pos
      G.firstDeficitLeftActiveHessian
      (fun r s => G.leftActive_gap r s)
      a b c0 d hbase
  have hsub := G.firstDeficitLeftStaggeredBlock_activeSubmatrix_eq
  have ha :
      G.firstDeficitLeftStaggeredBlock.a =
        G.firstDeficitLeftActiveHessian 0 0 := by
    have h := congrFun (congrFun hsub (0 : Fin 3)) (0 : Fin 3)
    change G.firstDeficitLeftStaggeredBlock.a =
      G.firstDeficitLeftActiveHessian 0 0 at h
    exact h
  have hp02 :
      G.firstDeficitLeftStaggeredBlock.p =
        G.firstDeficitLeftActiveHessian 0 2 := by
    have h := congrFun (congrFun hsub (0 : Fin 3)) (2 : Fin 3)
    change G.firstDeficitLeftStaggeredBlock.p =
      G.firstDeficitLeftActiveHessian 0 2 at h
    exact h
  have hp20 :
      G.firstDeficitLeftStaggeredBlock.p =
        G.firstDeficitLeftActiveHessian 2 0 := by
    have h := congrFun (congrFun hsub (2 : Fin 3)) (0 : Fin 3)
    change G.firstDeficitLeftStaggeredBlock.p =
      G.firstDeficitLeftActiveHessian 2 0 at h
    exact h
  have hx :
      G.firstDeficitLeftStaggeredBlock.x =
        G.firstDeficitLeftActiveHessian 2 2 := by
    have h := congrFun (congrFun hsub (2 : Fin 3)) (2 : Fin 3)
    change G.firstDeficitLeftStaggeredBlock.x =
      G.firstDeficitLeftActiveHessian 2 2 at h
    exact h
  have hd :
      G.firstDeficitLeftStaggeredBlock.d =
        G.firstDeficitLeftActiveHessian 1 1 := by
    have h := congrFun (congrFun hsub (1 : Fin 3)) (1 : Fin 3)
    change G.firstDeficitLeftStaggeredBlock.d =
      G.firstDeficitLeftActiveHessian 1 1 at h
    exact h
  have ha0 :
      G.firstDeficitLeftStaggeredBlock.a.coeff 0 = a := by
    rw [ha]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 0 0
  have hp0b :
      G.firstDeficitLeftStaggeredBlock.p.coeff 0 = b := by
    rw [hp02]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 0 2
  have hp0c :
      G.firstDeficitLeftStaggeredBlock.p.coeff 0 = c0 := by
    rw [hp20]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 2 0
  have hx0 :
      G.firstDeficitLeftStaggeredBlock.x.coeff 0 = d := by
    rw [hx]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 2 2
  have hdq :
      G.firstDeficitLeftStaggeredBlock.d.coeff G.firstDeficitOrder =
        (G.firstDeficitLeftActiveHessian 1 1).coeff G.firstDeficitOrder := by
    rw [hd]
  rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq]
  rw [hcoeff]
  rw [← ha0, ← hx0, ← hp0b, ← hp0c, ← hdq]

/-- Right-oriented version of the same active-coefficient factorisation. -/
theorem firstDeficitRightStaggeredBlock_activeCoeff_eq_outer_mul_middle
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (firstKernelBreakActiveThreeDet
        G.firstDeficitRightStaggeredBlock).coeff G.firstDeficitOrder =
      (G.firstDeficitRightStaggeredBlock.a.coeff 0 *
          G.firstDeficitRightStaggeredBlock.x.coeff 0 -
        G.firstDeficitRightStaggeredBlock.p.coeff 0 *
          G.firstDeficitRightStaggeredBlock.p.coeff 0) *
        G.firstDeficitRightStaggeredBlock.d.coeff G.firstDeficitOrder := by
  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a := H0 (0 : Fin 4) 0
  let b := H0 (0 : Fin 4) 3
  let c0 := H0 (3 : Fin 4) 0
  let d := H0 (3 : Fin 4) 3
  have hbase : ∀ r s,
      (G.firstDeficitRightActiveHessian r s).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase a b c0 d r s := by
    intro r s
    simpa [a, b, c0, d, H0] using
      G.firstDeficitRightActiveHessian_coeff_zero_eq_rankTwoRoofBase
        hthree houtThree r s
  have hcoeff :=
    HC4.Polynomial.coeff_det_polynomialMatrix3_gap
      G.firstDeficitOrder_pos
      G.firstDeficitRightActiveHessian
      (fun r s => G.rightActive_gap r s)
      a b c0 d hbase
  have hsub := G.firstDeficitRightStaggeredBlock_activeSubmatrix_eq
  have ha :
      G.firstDeficitRightStaggeredBlock.a =
        G.firstDeficitRightActiveHessian 0 0 := by
    have h := congrFun (congrFun hsub (0 : Fin 3)) (0 : Fin 3)
    change G.firstDeficitRightStaggeredBlock.a =
      G.firstDeficitRightActiveHessian 0 0 at h
    exact h
  have hp02 :
      G.firstDeficitRightStaggeredBlock.p =
        G.firstDeficitRightActiveHessian 0 2 := by
    have h := congrFun (congrFun hsub (0 : Fin 3)) (2 : Fin 3)
    change G.firstDeficitRightStaggeredBlock.p =
      G.firstDeficitRightActiveHessian 0 2 at h
    exact h
  have hp20 :
      G.firstDeficitRightStaggeredBlock.p =
        G.firstDeficitRightActiveHessian 2 0 := by
    have h := congrFun (congrFun hsub (2 : Fin 3)) (0 : Fin 3)
    change G.firstDeficitRightStaggeredBlock.p =
      G.firstDeficitRightActiveHessian 2 0 at h
    exact h
  have hx :
      G.firstDeficitRightStaggeredBlock.x =
        G.firstDeficitRightActiveHessian 2 2 := by
    have h := congrFun (congrFun hsub (2 : Fin 3)) (2 : Fin 3)
    change G.firstDeficitRightStaggeredBlock.x =
      G.firstDeficitRightActiveHessian 2 2 at h
    exact h
  have hd :
      G.firstDeficitRightStaggeredBlock.d =
        G.firstDeficitRightActiveHessian 1 1 := by
    have h := congrFun (congrFun hsub (1 : Fin 3)) (1 : Fin 3)
    change G.firstDeficitRightStaggeredBlock.d =
      G.firstDeficitRightActiveHessian 1 1 at h
    exact h
  have ha0 :
      G.firstDeficitRightStaggeredBlock.a.coeff 0 = a := by
    rw [ha]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 0 0
  have hp0b :
      G.firstDeficitRightStaggeredBlock.p.coeff 0 = b := by
    rw [hp02]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 0 2
  have hp0c :
      G.firstDeficitRightStaggeredBlock.p.coeff 0 = c0 := by
    rw [hp20]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 2 0
  have hx0 :
      G.firstDeficitRightStaggeredBlock.x.coeff 0 = d := by
    rw [hx]
    simpa [HC4.Polynomial.rankTwoRoofZeroKernelBase] using hbase 2 2
  have hdq :
      G.firstDeficitRightStaggeredBlock.d.coeff G.firstDeficitOrder =
        (G.firstDeficitRightActiveHessian 1 1).coeff G.firstDeficitOrder := by
    rw [hd]
  rw [G.firstDeficitRightStaggeredBlock_activeThree_eq]
  rw [hcoeff]
  rw [← ha0, ← hx0, ← hp0b, ← hp0c, ← hdq]

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
