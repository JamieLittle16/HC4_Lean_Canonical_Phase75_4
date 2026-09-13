import HC4.Valuation.CoordinateMaxKernelOpeningReverseRees
import HC4.Valuation.SingularFirstKernelBreakSelector
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-!
# Rank frontier for an honest coordinate-max kernel opening

This module composes the source-honest A19.55 opening ingredients.

For one `CanonicalCoordinateMaxKernelOpeningData`, form its singular bounded
reverse-Rees family and move the stored kernel coordinate to slot `3` by a
simultaneous row/column permutation of the parameter-first Hessian.  The
special-fibre kernel makes the fourth row constant coefficient zero, while
recovery at parameter `1` and nonlinear source support make that row a
nonzero polynomial series.

We then split on the determinant of the complementary `3 x 3` block at the
special fibre.

* If it is nonzero, the canonical first-row selector and
  `SingularFirstKernelBreakRankTwo` give an explicit nonzero principal
  `2 x 2` minor at the first opening layer.
* If it is zero, we retain that exact lower-rank equation for the next finite
  rank split.

No repair transition is attached here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- Simultaneous matrix permutation which moves the actual kernel coordinate
to canonical slot `3`. -/
def kernelLastPerm (k : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.swap k (3 : Fin 4)

@[simp] theorem kernelLastPerm_last (k : Fin 4) :
    kernelLastPerm k (3 : Fin 4) = k := by
  simp [kernelLastPerm]

/-- Parameter-first Hessian with the chosen kernel coordinate moved to slot
`3`. -/
noncomputable def kernelLastParameterFirstHessian
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (k : Fin 4) :
    Matrix (Fin 4) (Fin 4) (Polynomial (MvPolynomial (Fin 4) K)) :=
  (parameterFirstHessian P).submatrix (kernelLastPerm k) (kernelLastPerm k)

/-- Canonical four-block of the reindexed parameter-first Hessian. -/
noncomputable def kernelLastFamilyHessianFourBlock
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (k : Fin 4) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix (kernelLastParameterFirstHessian P k)

/-- Displaying the reindexed four-block recovers the reindexed Hessian. -/
theorem kernelLastFamilyHessianFourBlock_matrix
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (k : Fin 4) :
    (kernelLastFamilyHessianFourBlock P k).matrix =
      kernelLastParameterFirstHessian P k := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  simp [kernelLastParameterFirstHessian,
    parameterFirstHessian_symmetric]

/-- Simultaneous reindexing does not change the determinant, so an identically
singular family gives an identically singular kernel-last four-block. -/
theorem kernelLastFamilyHessianFourBlock_determinantCore_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (k : Fin 4)
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    (kernelLastFamilyHessianFourBlock P k).determinantCore = 0 := by
  calc
    (kernelLastFamilyHessianFourBlock P k).determinantCore =
        (kernelLastFamilyHessianFourBlock P k).matrix.det :=
      (GeneralFourBlock.matrix_det _).symm
    _ = (kernelLastParameterFirstHessian P k).det := by
      rw [kernelLastFamilyHessianFourBlock_matrix]
    _ = (parameterFirstHessian P).det := by
      unfold kernelLastParameterFirstHessian
      rw [Matrix.det_submatrix_equiv_self]
    _ = parameterFirstEquiv K (HC4.Polynomial.hessianDeterminant P) :=
      parameterFirstHessian_det P
    _ = 0 := by rw [hdet]; simp

end
end HC4.Valuation

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

/-- Parameter layer zero of the honest reverse-Rees family is exactly the
stored child. -/
theorem reverseReesFamily_layer_zero_eq_child :
    familyParameterLayer D.reverseReesFamily 0 = D.child := by
  rw [← D.specialFiber_reverseReesFamily_eq_child]
  unfold reverseReesFamily
  exact
    (polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
      (coordinateMaxNatWeight D.extractionCoordinate)
      D.extractionLevel D.parent D.hasReverseWeightBound).symm

/-- Every parameter-first Hessian entry in the stored kernel row has zero
constant coefficient. -/
theorem parameterFirstHessian_kernelRow_coeff_zero
    (i : Fin 4) :
    (parameterFirstHessian D.reverseReesFamily D.kernelCoordinate i).coeff 0 = 0 := by
  rw [parameterFirstHessian_coeff]
  rw [D.reverseReesFamily_layer_zero_eq_child]
  have h := congrArg (MvPolynomial.pderiv i) D.child_kernel
  simpa [HC4.Polynomial.hessian_apply] using h

/-- The kernel-last four-block therefore has zero constant coefficient in all
four fourth-row entries. -/
theorem kernelLastBlock_kernelRow_coeff_zero :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.q.coeff 0 = 0 ∧ B.s.coeff 0 = 0 ∧
      B.y.coeff 0 = 0 ∧ B.z.coeff 0 = 0 := by
  let rho := kernelLastPerm D.kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    D.reverseReesFamily D.kernelCoordinate
  have hentry (j : Fin 4) :
      (parameterFirstHessian D.reverseReesFamily (rho j) (rho 3)).coeff 0 = 0 := by
    rw [show rho 3 = D.kernelCoordinate by simp [rho]]
    rw [parameterFirstHessian_symmetric]
    exact D.parameterFirstHessian_kernelRow_coeff_zero (rho j)
  dsimp [B]
  constructor
  · change
      (parameterFirstHessian D.reverseReesFamily (rho 0) (rho 3)).coeff 0 = 0
    exact hentry 0
  constructor
  · change
      (parameterFirstHessian D.reverseReesFamily (rho 1) (rho 3)).coeff 0 = 0
    exact hentry 1
  constructor
  · change
      (parameterFirstHessian D.reverseReesFamily (rho 2) (rho 3)).coeff 0 = 0
    exact hentry 2
  · change
      (parameterFirstHessian D.reverseReesFamily (rho 3) (rho 3)).coeff 0 = 0
    exact hentry 3

/-- Nonlinear source support makes the reindexed fourth row a genuinely
nonzero polynomial series. -/
theorem kernelLastBlock_kernelRow_ne_zero
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0 := by
  rcases D.exists_parameterFirstHessian_kernelRow_ne_zero hnonlinear with ⟨i, hi⟩
  let rho := kernelLastPerm D.kernelCoordinate
  let j : Fin 4 := rho.symm i
  have hrhoj : rho j = i := by simp [j]
  have hlast : rho (3 : Fin 4) = D.kernelCoordinate := by simp [rho]
  have hi' :
      parameterFirstHessian D.reverseReesFamily (rho j) (rho 3) ≠ 0 := by
    rw [hrhoj, hlast]
    intro hzero
    apply hi
    rw [parameterFirstHessian_symmetric]
    exact hzero
  fin_cases j
  · exact Or.inl (by
      change parameterFirstHessian D.reverseReesFamily (rho 0) (rho 3) ≠ 0
      exact hi')
  · exact Or.inr (Or.inl (by
      change parameterFirstHessian D.reverseReesFamily (rho 1) (rho 3) ≠ 0
      exact hi'))
  · exact Or.inr (Or.inr (Or.inl (by
      change parameterFirstHessian D.reverseReesFamily (rho 2) (rho 3) ≠ 0
      exact hi')))
  · exact Or.inr (Or.inr (Or.inr (by
      change parameterFirstHessian D.reverseReesFamily (rho 3) (rho 3) ≠ 0
      exact hi'))

/-- Honest finite rank split for one canonical coordinate-max opening. -/
inductive RankFrontier
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) : Type
  | activeThree
      (active_ne_zero :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        (firstKernelBreakActiveThreeDet B).coeff 0 ≠ 0)
      (firstLayerMinor :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        let hrow := D.kernelLastBlock_kernelRow_ne_zero hnonlinear
        let hzero := D.kernelLastBlock_kernelRow_coeff_zero
        let E := singularFirstKernelBreakData_of_kernelRow B hrow
          hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
          active_ne_zero
          (kernelLastFamilyHessianFourBlock_determinantCore_eq_zero
            D.reverseReesFamily D.kernelCoordinate
            D.reverseReesFamily_hessianDeterminant_eq_zero)
        (E.block.a.coeff E.order * E.block.z.coeff E.order -
            E.block.q.coeff E.order * E.block.q.coeff E.order ≠ 0) ∨
        (E.block.d.coeff E.order * E.block.z.coeff E.order -
            E.block.s.coeff E.order * E.block.s.coeff E.order ≠ 0) ∨
        (E.block.x.coeff E.order * E.block.z.coeff E.order -
            E.block.y.coeff E.order * E.block.y.coeff E.order ≠ 0))
  | activeDegenerate
      (active_eq_zero :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        (firstKernelBreakActiveThreeDet B).coeff 0 = 0)

/-- **Coordinate-max kernel-opening rank frontier.** -/
noncomputable def rankFrontier
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    D.RankFrontier hnonlinear := by
  let B := kernelLastFamilyHessianFourBlock
    D.reverseReesFamily D.kernelCoordinate
  let hrow := D.kernelLastBlock_kernelRow_ne_zero hnonlinear
  let hzero := D.kernelLastBlock_kernelRow_coeff_zero
  have hdet : B.determinantCore = 0 := by
    dsimp [B]
    exact kernelLastFamilyHessianFourBlock_determinantCore_eq_zero
      D.reverseReesFamily D.kernelCoordinate
      D.reverseReesFamily_hessianDeterminant_eq_zero
  by_cases hactive : (firstKernelBreakActiveThreeDet B).coeff 0 = 0
  · exact .activeDegenerate (by simpa [B] using hactive)
  · let E := singularFirstKernelBreakData_of_kernelRow B hrow
      hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2 hactive hdet
    exact .activeThree (by simpa [B] using hactive)
      (by simpa [B, hrow, hzero, E] using E.exists_nonzero_principalMinor_at_order)

end CanonicalCoordinateMaxKernelOpeningData

end
end HC4.Newton
