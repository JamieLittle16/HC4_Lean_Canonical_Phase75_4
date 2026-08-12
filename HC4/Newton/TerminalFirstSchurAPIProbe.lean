import HC4.Newton.TerminalConformalWeight
import HC4.Newton.TerminalAssociatedGradedEndpoint
import HC4.Newton.FirstSchurLayerLinearization

/-!
# Temporary API probe v2

This file adds no theorem and no axiom. It prints only relevant declaration
names. This avoids depending on pretty-printer APIs inside `run_cmd`.

Delete after use.
-/

open Lean Elab Command

private def relevantHC4Name (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "HC4.Newton.Terminal" ||
  s.startsWith "HC4.Newton.terminal" ||
  s.startsWith "HC4.Newton.FirstSchur" ||
  s.startsWith "HC4.Newton.firstSchur" ||
  s.startsWith "HC4.Newton.ExactZeroSchur" ||
  s.startsWith "HC4.Newton.exactZeroSchur"

run_cmd do
  let env ← getEnv
  logInfo "===== HC4 terminal / first-Schur declaration names ====="
  for (n, _ci) in env.constants.toList do
    if relevantHC4Name n then
      logInfo m!"{n}"
  logInfo "===== end API names ====="
