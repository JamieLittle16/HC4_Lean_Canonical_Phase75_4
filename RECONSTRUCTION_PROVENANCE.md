# Reconstruction provenance

This clean project was reconstructed on 2026-08-07 from two user-provided
archives:

- `Grading.zip` — contained the cumulative `HC4/` Lean source tree.
- `all.zip` — contained the project infrastructure/history (`HC4.lean`,
  `NegativeControl.lean`, pinned Lake/toolchain files, verification scripts,
  audit logs, and phase notes), but its `HC4/` source directories were empty.

The Phase 75.2 manifest in `all.zip` recorded SHA-256 hashes for:

- `HC4/Audit.lean`
- `HC4/Polynomial.lean`
- `HC4/Polynomial/ComplementaryEdgeRigidity.lean`

The corresponding files extracted from `Grading.zip` matched those hashes
exactly. This establishes that the two archives describe the same cumulative
Phase 75.2 checkpoint for the files changed by that phase.

Historical phase notes are distributed separately in
`HC4_Lean_Phase_History_Through75_2.zip` so the canonical working tree remains
clean.
