import HC4.Valuation.ActualParameterLayer
import HC4.Newton.GeneralFourBlockSchur

/-!
# Temporary family-series / four-block API source probe

No theorem or axiom is added.  This prints the two small implementation files
needed to construct the adaptive block from the honest polynomial family
without guessing the coefficient-swap API.

Delete after use.
-/

open Lean Elab Command

private def printSource (path : System.FilePath) : CommandElabM Unit := do
  let txt ← IO.FS.readFile path
  logInfo m!"===== {path} ====="
  let lines := txt.splitOn "\n"
  for h : i in [0:lines.length] do
    logInfo m!"{i + 1}: {lines[i]}"
  logInfo m!"===== end {path} ====="

run_cmd do
  printSource "HC4/Valuation/ActualParameterLayer.lean"
  printSource "HC4/Newton/GeneralFourBlockSchur.lean"
