# Phase 75.3 — Defect-retaining departure-frontier compile repair

Prepared against `HC4_Lean_Canonical_Phase75_2_Current.zip`.

Changed source:
- `HC4/Valuation/DefectRetainingDepartureFrontier.lean`

Repairs:
1. Rename the reserved Lean keyword `local` when it was being used as a structure field/local binding to `lossless`.
   This repairs the intended `CanonicalSmithDepartureFrontier` declaration and should remove the parser / invalid-`K`
   / unknown-constant cascade caused by the malformed declaration.
2. `firstPositiveParameterOrder_pos`: project positivity directly from `Finset.mem_filter`.
3. `firstPositiveParameterOrder_realised`: project image membership directly from `Finset.mem_filter`.
4. `firstPositiveParameterOrder_le`: construct filtered-image membership explicitly via `Finset.mem_filter.mpr`
   and `Finset.mem_image.mpr`.
5. Update `MANIFEST.sha256` for the changed Lean source while preserving the other manifest entries.

No theorem statement is weakened and no `sorry`, `admit`, `axiom`, or `unsafe` escape hatch is introduced.
