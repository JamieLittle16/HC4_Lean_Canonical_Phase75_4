import HC4.Newton.TerminalConformalWeight
import HC4.Newton.TerminalAssociatedGradedEndpoint
import HC4.Newton.FirstSchurLayerLinearization

/-!
# Temporary terminal / Schur signature probe

Delete after use.  No theorem, axiom, or definition relevant to HC4 is added.
-/

open Lean Elab Command

#check HC4.Newton.terminalActualHessian_hasConformalQuadraticWeight
#check HC4.Newton.terminalConformalFace_dichotomy
#check HC4.Newton.terminalDirectRankJump_collision_forces_residual
#check HC4.Newton.terminalDirectRankJump_collision_forces_opposite_pair
#check HC4.Newton.terminalDirectRankJump_injective_or_residual
#check HC4.Newton.TerminalAssociatedGradedCollisionData
#check HC4.Newton.TerminalAssociatedGradedCollisionData.impossible_of_JC2
#check HC4.Newton.TerminalAssociatedGradedCollisionData.endpoint
#check HC4.Newton.TerminalAssociatedGradedCollisionData.exactCollision

private def hasSchur (n : Name) : Bool :=
  n.toString.contains "Schur" || n.toString.contains "schur"

run_cmd do
  let env ← getEnv
  logInfo "===== declarations containing Schur/schur ====="
  for (n, _ci) in env.constants.toList do
    if hasSchur n then
      logInfo m!"{n}"
  logInfo "===== end Schur names ====="
