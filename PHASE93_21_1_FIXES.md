# Phase 93.21.1 — redundant tactic cleanup

Affected file:

    HC4/Newton/MixedDepartureAdapter.lean

The only Phase 93.21 build failure was

    No goals to be solved

at the final `omega` in
`preterminal_mixedPivot_strictly_lowers_repairMeasure`.

The preceding `simp` already proves the strict measure inequality exactly,
so the redundant `omega` line has been removed.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
