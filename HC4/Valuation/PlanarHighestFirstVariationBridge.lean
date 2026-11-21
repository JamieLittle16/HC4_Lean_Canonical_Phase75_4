import HC4.Valuation.PlanarContactFirstVariationBridge
import HC4.Polynomial.HighestBinomialParallelFirstVariation
import Mathlib.Tactic

/-!
# First actual layer from a primitive highest binomial

This is the top-end companion of `PlanarContactFirstVariationBridge`.
For a Hessian-singular polynomial family whose special fibre is the primitive
highest rank-three binomial and whose first positive actual layer is a parallel
staircase fibre, the existing generic parameter-gap dual jet identifies the
nilpotent determinant coefficient with the first variation.  The state-free
highest-binomial factorisation then yields the dual affine two-root Euler
operator, with roots `j,j+1`.

No A19 data or extra filtration is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Highest-end first-variation moment bridge.**  Exact moment
identification of the primitive highest special fibre and first actual lower
staircase layer turns family singularity into the dual affine two-root Euler
equation. -/
theorem affineTwoRootEulerOperator_eq_zero_of_firstActual_highest_moment_identification
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (hdet : HC4.Polynomial.hessianDeterminant P = 0)
    (V n k j : ℕ)
    (hV : 0 < V) (hn : 2 ≤ n)
    (c d : K) (hc : c ≠ 0) (hd : d ≠ 0)
    (phi : Polynomial K)
    (hzero :
      (fun r s =>
        HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer P 0) r s)) =
        HC4.Polynomial.highestBinomialMomentHessian V n c d)
    (hfirst :
      (fun r s =>
        HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer P
              (firstPositiveActualParameterOrder P h)) r s)) =
        HC4.Polynomial.parallelStaircaseMomentHessian V k j phi) :
    HC4.Polynomial.affineTwoRootEulerOperator
      (c * (n : K)) (d * ((n - 1 : ℕ) : K)) j phi = 0 := by
  have hjet :
      firstActualSpecialisedEulerDualJet P h =
        HC4.Polynomial.highestParallelFirstVariationDualPencil
          V n k j c d phi := by
    apply Matrix.ext
    intro r s
    rw [firstActualSpecialisedEulerDualJet_apply]
    have hz := congrFun (congrFun hzero r) s
    have hf := congrFun (congrFun hfirst r) s
    change (_, _) = (_, _)
    exact Prod.ext hz hf
  have hnil := firstActualSpecialisedEulerDualJet_det_snd_eq_zero P h hdet
  rw [hjet] at hnil
  exact
    HC4.Polynomial.affineTwoRootEulerOperator_eq_zero_of_highestParallel_snd_det_eq_zero
      V n k j hV hn c d hc hd phi hnil

end

end HC4.Valuation
