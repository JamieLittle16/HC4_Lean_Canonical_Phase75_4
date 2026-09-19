import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseRees
import HC4.Valuation.CoordinateMaxKernelOpeningRankFrontier
import HC4.Valuation.SingularFirstKernelBreakSelector
import Mathlib.Tactic

/-!
# Honest kernel-row opening for the A19.55 top-face kernel

The auxiliary ordinary reverse-Rees family starts at the literal A19 top face
and ends at the represented determinant-one special fibre.  Therefore a
coordinate kernel present on the top face cannot persist for the entire
family: if its complete Hessian row vanished as a polynomial series, the same
row would vanish after evaluation at parameter `1`, forcing the source Hessian
determinant to be zero.

This file packages that genuine row break and the corresponding order-zero
vanishing.  The parameter order remains an auxiliary Rees order only.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state)

/-- The zero parameter layer of the honest top-kernel reverse Rees family is
exactly the stored top face. -/
theorem topKernelReverseRees_layer_zero_eq_topFace :
    familyParameterLayer T.topKernelReverseReesFamily 0 = T.topFace.face := by
  rw [← T.topKernelReverseRees_specialFiber_eq_topFace]
  exact (polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
    T.topKernelReesSource_hasReverseWeightBound).symm

/-- A kernel row on the top face must genuinely open somewhere in the honest
ordinary reverse-Rees family, because the represented endpoint has Hessian
determinant one. -/
theorem exists_topKernelReverseRees_parameterFirstHessian_row_ne_zero
    (kernelCoordinate : Fin 4) :
    ∃ i : Fin 4,
      parameterFirstHessian T.topKernelReverseReesFamily kernelCoordinate i ≠ 0 := by
  by_contra hnone
  push_neg at hnone

  have hfamilyRow :
      ∀ i : Fin 4,
        HC4.Polynomial.hessian T.topKernelReverseReesFamily
          kernelCoordinate i = 0 := by
    intro i
    apply (parameterFirstEquiv K).injective
    change
      parameterFirstHessian T.topKernelReverseReesFamily kernelCoordinate i =
        parameterFirstEquiv K 0
    simpa using hnone i

  have hsourceRow :
      ∀ i : Fin 4,
        HC4.Polynomial.hessian T.topKernelReesSource kernelCoordinate i = 0 := by
    intro i
    rw [← T.topKernelReverseRees_evalOne_eq_source]
    rw [HC4.Polynomial.hessian_apply]
    rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]
    have hfamily := hfamilyRow i
    rw [HC4.Polynomial.hessian_apply] at hfamily
    rw [hfamily]
    simp

  have hdetZero :
      HC4.Polynomial.hessianDeterminant T.topKernelReesSource = 0 := by
    unfold HC4.Polynomial.hessianDeterminant
    exact Matrix.det_eq_zero_of_row_eq_zero kernelCoordinate hsourceRow
  rw [T.topKernelReesSource_hessianDeterminant_eq_one] at hdetZero
  exact one_ne_zero hdetZero

/-- After moving the stored kernel coordinate to slot `3`, the polynomial
four-block kernel row is genuinely nonzero. -/
theorem topKernelLastBlock_kernelRow_ne_zero
    (kernelCoordinate : Fin 4) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0 := by
  rcases T.exists_topKernelReverseRees_parameterFirstHessian_row_ne_zero
      kernelCoordinate with ⟨i, hi⟩
  let rho := kernelLastPerm kernelCoordinate
  let j : Fin 4 := rho.symm i
  have hrhoj : rho j = i := by simp [j]
  have hlast : rho (3 : Fin 4) = kernelCoordinate := by simp [rho]
  have hi' :
      parameterFirstHessian T.topKernelReverseReesFamily
        (rho j) (rho 3) ≠ 0 := by
    rw [hrhoj, hlast]
    intro hzero
    apply hi
    rw [parameterFirstHessian_symmetric]
    exact hzero
  by_cases hj0 : j = (0 : Fin 4)
  · exact Or.inl (by
      change
        parameterFirstHessian T.topKernelReverseReesFamily
          (rho 0) (rho 3) ≠ 0
      simpa [hj0] using hi')
  by_cases hj1 : j = (1 : Fin 4)
  · exact Or.inr (Or.inl (by
      change
        parameterFirstHessian T.topKernelReverseReesFamily
          (rho 1) (rho 3) ≠ 0
      simpa [hj1] using hi'))
  by_cases hj2 : j = (2 : Fin 4)
  · exact Or.inr (Or.inr (Or.inl (by
      change
        parameterFirstHessian T.topKernelReverseReesFamily
          (rho 2) (rho 3) ≠ 0
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
    change
      parameterFirstHessian T.topKernelReverseReesFamily
        (rho 3) (rho 3) ≠ 0
    simpa [hj3] using hi')))
/-- If the stored top face has the coordinate kernel, then the entire
kernel-last row vanishes at parameter order zero. -/
theorem topKernelLastBlock_kernelRow_coeff_zero
    (kernelCoordinate : Fin 4)
    (hkernel : MvPolynomial.pderiv kernelCoordinate T.topFace.face = 0) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.q.coeff 0 = 0 ∧ B.s.coeff 0 = 0 ∧
      B.y.coeff 0 = 0 ∧ B.z.coeff 0 = 0 := by
  let rho := kernelLastPerm kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have hrow :
      ∀ j : Fin 4,
        HC4.Polynomial.hessian T.topFace.face kernelCoordinate j = 0 := by
    intro j
    have h := congrArg (MvPolynomial.pderiv j) hkernel
    simpa [HC4.Polynomial.hessian_apply] using h
  have hentry (j : Fin 4) :
      (parameterFirstHessian T.topKernelReverseReesFamily
        (rho j) (rho 3)).coeff 0 = 0 := by
    rw [show rho 3 = kernelCoordinate by simp [rho]]
    rw [parameterFirstHessian_symmetric]
    rw [parameterFirstHessian_coeff]
    rw [T.topKernelReverseRees_layer_zero_eq_topFace]
    exact hrow (rho j)
  dsimp [B]
  constructor
  · change
      (parameterFirstHessian T.topKernelReverseReesFamily
        (rho 0) (rho 3)).coeff 0 = 0
    exact hentry 0
  constructor
  · change
      (parameterFirstHessian T.topKernelReverseReesFamily
        (rho 1) (rho 3)).coeff 0 = 0
    exact hentry 1
  constructor
  · change
      (parameterFirstHessian T.topKernelReverseReesFamily
        (rho 2) (rho 3)).coeff 0 = 0
    exact hentry 2
  · change
      (parameterFirstHessian T.topKernelReverseReesFamily
        (rho 3) (rho 3)).coeff 0 = 0
    exact hentry 3

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
