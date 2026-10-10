import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseRees
import HC4.Newton.MixedDegreeAxisCollision
import HC4.Valuation.QuadraticTransverseCapAdjugateSchur
import Mathlib.Tactic

/-!
# Exact represented-source quadratic-axis marked collision

The actual represented determinant-one source already has the marked
gradient collision at zero and e₀. The existing longitudinal-coefficient
library therefore gives the endpoint equality for its THREE genuine
transverse-linear coefficient polynomials, without evaluation of any
invented source, or asserting a collision on a singular special fibre.

This is the collision hypothesis required by the rank-two polynomial
adjugate kernel endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The actual represented source has equal transverse-linear
longitudinal coefficients at the two collision points. No quadratic
cap or rank hypothesis is required for this equality. -/
theorem topKernelReesSource_transverseLinearMarkedCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (j : Fin 3) :
    Polynomial.eval (1 : K)
        (longitudinalCoefficientPolynomialAt
          (Finsupp.single j 1) T.topKernelReesSource) =
      Polynomial.eval (0 : K)
        (longitudinalCoefficientPolynomialAt
          (Finsupp.single j 1) T.topKernelReesSource) := by
  have hzero :
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext i
    fin_cases i <;> rfl
  have hright :
      (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    fin_cases i <;> simp [coordinateAxisPoint]
  have hcoll :
      HasExactGradientCollision T.topKernelReesSource
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    rw [hzero, hright]
    exact T.topKernelReesSource_exactCollision
  exact longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision
    j T.topKernelReesSource hcoll

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
