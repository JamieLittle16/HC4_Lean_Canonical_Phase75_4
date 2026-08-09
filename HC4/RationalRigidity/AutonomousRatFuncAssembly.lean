import HC4.RationalRigidity.RegularRatFuncEvaluation
import HC4.RationalRigidity.AutonomousDenominatorRemoval
import Mathlib.Tactic

/-!
# RatFunc assembly for autonomous denominator removal

Phase 82 removed the denominator of a reduced autonomous target from
pointwise finite/infinity cleared identities.  This file supplies the missing
bridge from a *single rational-function identity*

    A(rho) = eta * B(rho)

to those finite-chart scalar identities.

The only analytic-looking input is replaced by a purely algebraic regularity
hypothesis: whenever the reduced source `rho` is regular at a finite point,
so is `eta`.  Phase 85 proves precisely this for `eta = E(rho)` attached to
`rho = E(phi)/phi`.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A rational autonomous identity with regular left-hand side on the finite
source chart gives the pointwise cleared identity required by Phase 82. -/
theorem finite_cleared_identity_of_ratFunc_identity
    {rho eta : RatFunc K} {A B : Polynomial K}
    (hEtaRegular :
      ∀ x : K, RatFuncRegularAt x rho → RatFuncRegularAt x eta)
    (hCross :
      Polynomial.aeval rho A = eta * Polynomial.aeval rho B) :
    ∀ x : K, rho.denom.eval x ≠ 0 →
      A.eval (rho.num.eval x / rho.denom.eval x) =
        RatFunc.eval (RingHom.id K) x eta *
          B.eval (rho.num.eval x / rho.denom.eval x) := by
  intro x hD
  have hrho : RatFuncRegularAt x rho := hD
  have heta : RatFuncRegularAt x eta := hEtaRegular x hrho
  have hBreg : RatFuncRegularAt x (Polynomial.aeval rho B) :=
    ratFuncRegularAt_aeval hrho B
  have hEval := congrArg (RatFunc.eval (RingHom.id K) x) hCross
  rw [ratFunc_eval_aeval hrho A] at hEval
  rw [RatFunc.eval_mul (RingHom.id K) x
    (by simpa using heta) (by simpa using hBreg)] at hEval
  rw [ratFunc_eval_aeval hrho B] at hEval
  rw [ratFunc_eval_eq_num_div_denom] at hEval
  exact hEval

/-- Full algebraic pole-removal assembly for an autonomous identity in
`RatFunc K`.

The finite chart is extracted automatically from `hCross`.  The sole
remaining infinity datum is one cleared scalar identity at the exceptional
source value. -/
theorem constant_target_denominator_of_ratFunc_identity
    {rho eta : RatFunc K} {A B : Polynomial K}
    (hRhoDegree : 0 < rho.denom.natDegree)
    (hTargetCoprime : IsCoprime A B)
    (hEtaRegular :
      ∀ x : K, RatFuncRegularAt x rho → RatFuncRegularAt x eta)
    (hCross :
      Polynomial.aeval rho A = eta * Polynomial.aeval rho B)
    (etaInfinity : K)
    (hInfinityClear :
      A.eval (rationalInfinityValue rho.num rho.denom) =
        etaInfinity *
          B.eval (rationalInfinityValue rho.num rho.denom)) :
    ∃ b : K, b ≠ 0 ∧ B = Polynomial.C b := by
  apply constant_target_denominator_of_reduced_source_cover
    (RatFunc.isCoprime_num_denom rho)
    (RatFunc.denom_ne_zero rho)
    hRhoDegree
    hTargetCoprime
    (fun x => RatFunc.eval (RingHom.id K) x eta)
    etaInfinity
  · exact finite_cleared_identity_of_ratFunc_identity hEtaRegular hCross
  · exact hInfinityClear

end

end HC4.RationalRigidity
