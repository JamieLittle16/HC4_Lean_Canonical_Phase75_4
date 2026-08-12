import HC4.Valuation.RigidClosingFirstKernelStage
import HC4.Newton.FirstSchurLayerLinearization

/-!
# Focused Schur/restart signature probe

Temporary.  No theorem, axiom, or proof dependency is introduced.
-/

open Lean Elab Command

#check HC4.Newton.ExactZeroSchurClock
#check HC4.Newton.ExactZeroSchurClock.hasPositiveEntryLayer
#check HC4.Newton.ExactZeroSchurClock.firstOrder
#check HC4.Newton.ExactZeroSchurClock.firstOrder_pos
#check HC4.Newton.ExactZeroSchurFourBlockData
#check HC4.Newton.ExactZeroSchurFourBlockData.toClock
#check HC4.Valuation.HasIntegralRigidClosingFirstKernelStage
#check HC4.Valuation.integralFirstKernelStage_to_strictRestart

private def relevantFirstSchurName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "HC4.Newton.FirstSchur" ||
  s.startsWith "HC4.Newton.firstSchur" ||
  s.startsWith "HC4.Newton.ExactZeroSchur" ||
  s.startsWith "HC4.Newton.exactZeroSchur"

run_cmd do
  let env ← getEnv
  logInfo "===== focused first-Schur / zero-Schur names ====="
  for (n, _ci) in env.constants.toList do
    if relevantFirstSchurName n then
      logInfo m!"{n}"
  logInfo "===== end focused names ====="
