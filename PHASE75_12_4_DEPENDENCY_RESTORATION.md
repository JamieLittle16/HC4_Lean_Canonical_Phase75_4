# Phase 75.12.4 — Dependency restoration and umbrella verification

This patch fixes a packaging omission in Phase 75.12:

* adds `HC4/Valuation/SmithFrontierFourBlockExtraction.lean`, which
  `RigidPacketZeroSchurBridge.lean` imports but which was not shipped in the
  earlier archive;
* updates `HC4.lean` so the complete Phase 75.9–75.12 chain is part of the
  default HC4 library target and therefore covered by `./verify.sh`.

No mathematical theorem statement is weakened and no proof escape hatch is
introduced.
