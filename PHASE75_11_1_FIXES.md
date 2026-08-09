# Phase 75.11.1 — Divisibility parser fix

This patch fixes the three parser errors in `HC4/Newton/ZeroSchurFirstEntryClock.lean`.

The theorem statements for the common first Schur factor accidentally used ASCII `|` instead of Lean's divisibility symbol `∣`. Because those declarations did not parse, all later `firstFactor_dvd_*` field-resolution errors were cascades.

No theorem statements are mathematically changed, and no proof assumptions are added.
