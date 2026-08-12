import HC4.Valuation.FirstSchurDepartureBridge

/-!
# Temporary source probe for `FirstSchurDepartureBridge`

This file proves nothing and introduces no proof axiom.  It simply reads the
current source file from the local HC4 checkout and prints it with line
numbers.  This is preferable here to guessing theorem names: we need to
distinguish source-coordinate longitudinal order from parameter/valuation
Schur order before writing the final blocker adapter.

Delete after use.
-/

open Lean Elab Command

run_cmd do
  let path := "HC4/Valuation/FirstSchurDepartureBridge.lean"
  let txt ← IO.FS.readFile path
  logInfo m!"===== {path} ====="
  let lines := txt.splitOn "\n"
  for h : i in [0:lines.length] do
    let line := lines[i]
    logInfo m!"{i + 1}: {line}"
  logInfo "===== end source ====="
