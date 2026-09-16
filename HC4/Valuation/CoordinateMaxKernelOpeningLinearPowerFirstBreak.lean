import HC4.Valuation.CoordinateMaxKernelOpeningPureAxisHessian
import HC4.Valuation.CoordinateMaxKernelOpeningRankFrontier
import HC4.Valuation.RankOneSpecialFiberFirstBreak
import Mathlib.Tactic

/-!
# Rank-two first break from the pure-axis linear-power opening

The degenerate coordinate-max child is now known to be a pure extraction-axis
power.  Its Hessian therefore has a nonzero diagonal entry on that axis.  The
stored kernel coordinate is distinct from the extraction coordinate.

Move the kernel coordinate to slot `3` in the honest reverse-Rees Hessian.  The
extraction axis lands in one of active slots `0,1,2`, so one of the active
special-fibre diagonal coefficients `a_0,d_0,x_0` is nonzero.  The generic
rank-one-special-fibre first-break theorem then gives concrete rank-two
geometry at the first actual opening of the kernel row:

* either a principal `2 x 2` minor of the full polynomial Hessian series has a
  nonzero coefficient at that order; or
* the coefficient Hessian matrix of the breaking layer has a nonzero
  principal `2 x 2` minor.

No determinant defect or blocker clock is used.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

namespace ChildLinearPowerData

variable {m : ℕ}
variable (P : D.ChildLinearPowerData m)

/-- After moving the actual kernel coordinate to slot `3`, the pure extraction
axis supplies a nonzero constant coefficient on one of the three active
Hessian diagonals. -/
theorem kernelLastBlock_activeDiagonal_coeff_zero_ne_zero
    (hm : 3 ≤ m) :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
  let rho := kernelLastPerm D.kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    D.reverseReesFamily D.kernelCoordinate
  let j : Fin 4 := rho.symm D.extractionCoordinate

  have hrhoj : rho j = D.extractionCoordinate := by
    simp [j]
  have hne : D.extractionCoordinate ≠ D.kernelCoordinate :=
    P.extractionCoordinate_ne_kernelCoordinate (by omega)
  have hjne : j ≠ (3 : Fin 4) := by
    intro hj
    have h := hrhoj
    rw [hj, kernelLastPerm_last] at h
    exact hne h.symm

  have hentry :
      (parameterFirstHessian D.reverseReesFamily
        D.extractionCoordinate D.extractionCoordinate).coeff 0 ≠ 0 := by
    rw [parameterFirstHessian_coeff]
    rw [D.reverseReesFamily_layer_zero_eq_child]
    exact P.extraction_hessian_ne_zero hm

  have hentry' :
      (parameterFirstHessian D.reverseReesFamily
        (rho j) (rho j)).coeff 0 ≠ 0 := by
    simpa [hrhoj] using hentry

  dsimp [B]
  fin_cases j
  · exact Or.inl (by
      change
        (parameterFirstHessian D.reverseReesFamily (rho 0) (rho 0)).coeff 0 ≠ 0
      exact hentry')
  · exact Or.inr (Or.inl (by
      change
        (parameterFirstHessian D.reverseReesFamily (rho 1) (rho 1)).coeff 0 ≠ 0
      exact hentry'))
  · exact Or.inr (Or.inr (by
      change
        (parameterFirstHessian D.reverseReesFamily (rho 2) (rho 2)).coeff 0 ≠ 0
      exact hentry'))
  · exact (hjne rfl).elim

/-- **Linear-power first-opening closure.**  The exact source-honest Rees
family attached to a pure-axis linear-power child necessarily produces
concrete rank-two geometry at its first actual kernel-row opening. -/
noncomputable def firstBreakRankTwoOutcome
    (hm : 3 ≤ m)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    let hrow := D.kernelLastBlock_kernelRow_ne_zero hnonlinear
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  let B := kernelLastFamilyHessianFourBlock
    D.reverseReesFamily D.kernelCoordinate
  let hrow := D.kernelLastBlock_kernelRow_ne_zero hnonlinear
  have hzero := D.kernelLastBlock_kernelRow_coeff_zero
  have hactive :
      B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
    dsimp [B]
    exact P.kernelLastBlock_activeDiagonal_coeff_zero_ne_zero hm
  exact rankOneSpecialFiber_firstKernelRowBreak_rankTwo
    B hrow hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2 hactive

end ChildLinearPowerData

end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
