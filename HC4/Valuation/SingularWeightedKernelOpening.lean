import HC4.Valuation.CoordinateMaxKernelOpeningRankFrontier
import Mathlib.Tactic

/-!
# Generic singular weighted kernel opening

The coordinate-max kernel-opening stack contains a weight-independent core:
once an exact child initial form of a Hessian-singular parent has a literal
coordinate kernel which is absent on the parent, an honest bounded reverse-Rees
family has

* exact special fibre equal to that child,
* exact recovery of the parent at parameter one,
* identically singular Hessian determinant,
* zero constant coefficient in the kernel row, and
* a genuinely nonzero kernel-row series.

The first nonzero row order therefore feeds the existing singular first-break
selector.  This file packages that core without requiring the exposing weight
to be coordinate-max.  It is intended for exact nested Newton faces such as the
first-contact cross-facet child.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- Exact source-honest data for the first appearance of a coordinate kernel
under an arbitrary bounded natural weighted initial-form extraction from a
Hessian-singular parent. -/
structure SingularWeightedKernelOpeningData
    (parent : MvPolynomial (Fin 4) K) where
  child : MvPolynomial (Fin 4) K
  weight : Fin 4 → ℕ
  level : ℕ
  kernelCoordinate : Fin 4
  weight_bound : HasReverseWeightBound weight level parent
  initialForm_eq_child :
    HC4.Polynomial.initialForm
        (fun i => (weight i : ℤ)) (level : ℤ) parent = child
  parent_hessian_zero :
    HC4.Polynomial.hessianDeterminant parent = 0
  child_kernel :
    MvPolynomial.pderiv kernelCoordinate child = 0
  parent_kernel_ne :
    MvPolynomial.pderiv kernelCoordinate parent ≠ 0
  parent_support_degree_ge_three :
    ∀ d ∈ parent.support, 3 ≤ ordinaryDegree4 d

namespace SingularWeightedKernelOpeningData

variable {parent : MvPolynomial (Fin 4) K}
variable (D : SingularWeightedKernelOpeningData parent)

/-- Honest bounded reverse-Rees family attached to the weighted opening. -/
noncomputable def reverseReesFamily :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily D.weight D.level parent D.weight_bound

/-- The special fibre is exactly the retained child initial form. -/
theorem specialFiber_reverseReesFamily_eq_child :
    polynomialFamilySpecialFiber D.reverseReesFamily = D.child := by
  rw [reverseReesFamily]
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  exact D.initialForm_eq_child

/-- Evaluation at parameter one recovers the singular parent exactly. -/
theorem map_evalOne_reverseReesFamily :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K)) D.reverseReesFamily =
      parent := by
  ext d
  rw [MvPolynomial.coeff_map]
  rw [reverseReesFamily, reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ parent.support
  · simp [hd]
  · have hc : MvPolynomial.coeff d parent = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hc]

/-- Because the parent is Hessian-singular, the complete reverse-Rees family
is Hessian-singular identically in the parameter. -/
theorem reverseReesFamily_hessianDeterminant_eq_zero :
    HC4.Polynomial.hessianDeterminant D.reverseReesFamily = 0 := by
  rw [reverseReesFamily]
  exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
    D.weight D.level parent D.weight_bound D.parent_hessian_zero

/-- A nonzero first derivative on a nonlinear parent forces a nonzero Hessian
entry in the same row. -/
theorem exists_parent_hessianRow_entry_ne_zero :
    ∃ i : Fin 4,
      HC4.Polynomial.hessian parent D.kernelCoordinate i ≠ 0 := by
  rcases
      exists_hessian_entry_ne_zero_of_pderiv_ne_zero_of_support_degree_ge_three
        D.kernelCoordinate parent
        D.parent_support_degree_ge_three
        D.parent_kernel_ne with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [HC4.Polynomial.hessian_apply] using hi

/-- Hence at least one parameter-first Hessian entry in the kernel row is a
nonzero polynomial series. -/
theorem exists_parameterFirstHessian_kernelRow_ne_zero :
    ∃ i : Fin 4,
      parameterFirstHessian D.reverseReesFamily D.kernelCoordinate i ≠ 0 := by
  rcases D.exists_parent_hessianRow_entry_ne_zero with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  intro hzero
  have hfamilyEntry :
      HC4.Polynomial.hessian D.reverseReesFamily D.kernelCoordinate i = 0 := by
    apply (parameterFirstEquiv K).injective
    change
      parameterFirstHessian D.reverseReesFamily D.kernelCoordinate i =
        parameterFirstEquiv K 0
    simpa using hzero
  have hrecovered := congrArg
    (fun P : MvPolynomial (Fin 4) K =>
      HC4.Polynomial.hessian P D.kernelCoordinate i)
    D.map_evalOne_reverseReesFamily
  have hleft :
      HC4.Polynomial.hessian
          (MvPolynomial.map (Polynomial.evalRingHom (1 : K))
            D.reverseReesFamily)
          D.kernelCoordinate i = 0 := by
    have hmap :=
      congrArg
        (MvPolynomial.map (Polynomial.evalRingHom (1 : K)))
        hfamilyEntry
    simpa [HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_map] using hmap
  change
    HC4.Polynomial.hessian
        (MvPolynomial.map (Polynomial.evalRingHom (1 : K))
          D.reverseReesFamily)
        D.kernelCoordinate i =
      HC4.Polynomial.hessian parent D.kernelCoordinate i at hrecovered
  rw [hleft] at hrecovered
  exact hi hrecovered.symm

/-- Parameter layer zero is exactly the child. -/
theorem reverseReesFamily_layer_zero_eq_child :
    familyParameterLayer D.reverseReesFamily 0 = D.child := by
  rw [← D.specialFiber_reverseReesFamily_eq_child]
  unfold reverseReesFamily
  exact
    (polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
      D.weight D.level parent D.weight_bound).symm

/-- Every entry in the stored kernel row has zero constant coefficient. -/
theorem parameterFirstHessian_kernelRow_coeff_zero
    (i : Fin 4) :
    (parameterFirstHessian D.reverseReesFamily
      D.kernelCoordinate i).coeff 0 = 0 := by
  rw [parameterFirstHessian_coeff]
  rw [D.reverseReesFamily_layer_zero_eq_child]
  have h := congrArg (MvPolynomial.pderiv i) D.child_kernel
  simpa [HC4.Polynomial.hessian_apply] using h

/-- After moving the actual kernel coordinate to slot three, the whole fourth
row has zero constant coefficient. -/
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

/-- The reindexed kernel row is genuinely nonzero. -/
theorem kernelLastBlock_kernelRow_ne_zero :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0 := by
  rcases D.exists_parameterFirstHessian_kernelRow_ne_zero with ⟨i, hi⟩
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
  by_cases hj0 : j = (0 : Fin 4)
  · exact Or.inl (by
      change parameterFirstHessian D.reverseReesFamily (rho 0) (rho 3) ≠ 0
      simpa [hj0] using hi')
  by_cases hj1 : j = (1 : Fin 4)
  · exact Or.inr (Or.inl (by
      change parameterFirstHessian D.reverseReesFamily (rho 1) (rho 3) ≠ 0
      simpa [hj1] using hi'))
  by_cases hj2 : j = (2 : Fin 4)
  · exact Or.inr (Or.inr (Or.inl (by
      change parameterFirstHessian D.reverseReesFamily (rho 2) (rho 3) ≠ 0
      simpa [hj2] using hi')))
  have hj0v : j.val ≠ 0 := by
    intro h
    apply hj0
    apply Fin.ext
    simpa using h
  have hj1v : j.val ≠ 1 := by
    intro h
    apply hj1
    apply Fin.ext
    simpa using h
  have hj2v : j.val ≠ 2 := by
    intro h
    apply hj2
    apply Fin.ext
    simpa using h
  have hj3 : j = (3 : Fin 4) := by
    apply Fin.ext
    simp
    omega
  exact Or.inr (Or.inr (Or.inr (by
    change parameterFirstHessian D.reverseReesFamily (rho 3) (rho 3) ≠ 0
    simpa [hj3] using hi')))

/-- Finite first-break rank frontier for an arbitrary weighted kernel opening. -/
inductive RankFrontier : Type
  | activeThree
      (active_ne_zero :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        (firstKernelBreakActiveThreeDet B).coeff 0 ≠ 0)
      (firstLayerMinor :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        let hrow := D.kernelLastBlock_kernelRow_ne_zero
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

/-- Canonical rank split at the first row-opening layer. -/
noncomputable def rankFrontier : D.RankFrontier := by
  let B := kernelLastFamilyHessianFourBlock
    D.reverseReesFamily D.kernelCoordinate
  let hrow := D.kernelLastBlock_kernelRow_ne_zero
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
      (by simpa [B, hrow, hzero, E] using
        E.exists_nonzero_principalMinor_at_order)

end SingularWeightedKernelOpeningData

end

end HC4.Valuation
