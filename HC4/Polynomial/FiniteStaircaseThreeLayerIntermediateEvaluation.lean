import HC4.Polynomial.FiniteStaircaseThreeLayerEvaluation
import HC4.Polynomial.FiniteStaircaseThreeLayerIntermediateVariation
import Mathlib.Tactic

/-!
# Evaluated intermediate endpoint variation

Longitudinal evaluation preserves the exact three parameter layers and
singularity.  Combining that with the intermediate-gap jet gives the endpoint
first variation after evaluation.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K]

/-- **Evaluated intermediate endpoint first variation vanishes.** -/
theorem snd_det_endpointDualPencil_eval_eq_zero
    (x : K)
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (q N : ℕ)
    (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q)
    (hdet : (parameterThreeLayerMatrix A B C q N).det = 0) :
    TrivSqZeroExt.snd
      (endpointDualPencil
        (evalPolynomialMatrix x A)
        (evalPolynomialMatrix x C)).det = 0 := by
  have hdetE := det_parameterThreeLayerMatrix_eval_eq_zero
    x A B C q N hdet
  exact snd_det_endpointDualPencil_eq_zero_of_threeLayer_det_zero
    (evalPolynomialMatrix x A)
    (evalPolynomialMatrix x B)
    (evalPolynomialMatrix x C)
    q N hq hqN hN2q hdetE

end

end HC4.Polynomial
