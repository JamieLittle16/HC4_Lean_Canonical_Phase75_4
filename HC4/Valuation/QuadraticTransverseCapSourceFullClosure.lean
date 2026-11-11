import HC4.Valuation.QuadraticTransverseCapSourceRankThreeMixedClosure
import HC4.Valuation.QuadraticTransverseCapSourceSingularClosure
import Mathlib.Tactic

/-!
# Unconditional quadratic-transverse-cap marked collision exclusion

The actual source transverse Hessian determinant has two exhaustive cases.
The singular case was closed by the source-honest seven-section Schur
kernel drift theorem; the nonzero determinant case is closed by the
source-honest polynomial inverse, mixed Riccati, and longitudinal drift
argument.  Neither case adds a rank, Riccati, or endpoint assumption.

This is a theorem about the source F itself, not an abstract chart or
a specialization of the represented family's leading term.
-/

namespace HC4.Valuation
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A genuine four-variable determinant-one Hessian polynomial,
with reverse marked-axis weight at most two, cannot have an
exact collision of the gradient at 0 and the unit marked-axis
point.  The transverse determinant can be zero or nonzero; both
possibilities are eliminated using the *same actual source*. -/
theorem quadraticTransverseCap_two_source_markedCollision_impossible
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0))) :
    False := by
  by_cases hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore = 0
  · apply quadraticTransverseCap_two_singularSource_impossible
      F hbound hdet hCdet
    intro i
    change Polynomial.eval (1 : K)
        (longitudinalCoefficientPolynomialAt (Finsupp.single i 1) F) =
      Polynomial.eval (0 : K)
        (longitudinalCoefficientPolynomialAt (Finsupp.single i 1) F)
    exact longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision
      i F hcoll
  · exact quadraticTransverseCap_two_rankThree_source_impossible
      F hbound hdet hCdet hcoll

end
end HC4.Valuation
