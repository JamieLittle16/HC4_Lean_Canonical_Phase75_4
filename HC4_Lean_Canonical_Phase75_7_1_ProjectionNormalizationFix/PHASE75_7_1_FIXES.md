# Phase 75.7.1 — Projection normalisation fix

This is a compile-only repair of the green-intended Phase 75.7 exact Schur clock collapse.

It changes no definitions, theorem statements, or mathematical hypotheses.

Two proofs in `HC4/Valuation/FirstSchurDepartureBridge.lean` were relying on `rw` to recognise definitionally equal but syntactically different projections:

1. `preterminal_source_zero` now specialises `firstSchurData.determinant_coeff_order_eq_linearSource` to the exact `S.series`/`S.firstOrder`/`S.firstPotential` expression with `simpa`, then closes by `calc` using the already-proved determinant coefficient vanishing.
2. `closing_transverse_nonzero` now normalises `firstPositiveTransverseOrder S.hasTransverse` to `S.firstOrder` first, then substitutes the closing equality `S.firstOrder = f.defect`.

No `sorry`, `admit`, or `unsafe` is introduced.
