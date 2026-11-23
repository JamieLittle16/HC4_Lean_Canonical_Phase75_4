import HC4.Valuation.QuadraticTransverseCapSourceRegularGradient
import HC4.Valuation.QuadraticTransverseCapSourceSingularClosure
import Mathlib.Tactic

/-!
# Source-level quadratic-cap marked collision obstruction

The regular case has an actual bijective gradient; the singular
case already has the seven-section adjugate kernel obstruction
to the transverse-linear marked collision.

Combining these two proved routes rules out the original marked
axis collision under the whole-source quadratic cap and Hessian
determinant one, without a generic rank or endpoint assumption.

This is not a claim of full singular-branch gradient bijectivity.
It is the rank-independent obstruction required for a marked
collision on the represented quadratic-cap source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- No determinant-one transverse-quadratic source can have an
exact gradient collision between the marked points (0,0) and (1,0).
Both possible transverse determinant cases are covered. -/
theorem quadraticTransverseCapSource_markedCollision_impossible
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hcoll : HasExactGradientCollision F
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (Fin.cons (1 : K) (fun _ : Fin 3 => 0))) :
    False := by
  classical
  by_cases hs : (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore = 0
  · apply quadraticTransverseCap_two_singularSource_impossible F hcap hdet hs
    intro i
    exact longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision
      i F hcoll
  · have hinj :=
      (quadraticTransverseCapSource_regularGradient_bijective F hcap hdet hs).injective
    have heq := exactGradientCollision_eq_of_injective F
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) hinj hcoll
    have h01 : (0 : K) = 1 := congrFun heq (0 : Fin 4)
    exact zero_ne_one h01

end

end HC4.Valuation
