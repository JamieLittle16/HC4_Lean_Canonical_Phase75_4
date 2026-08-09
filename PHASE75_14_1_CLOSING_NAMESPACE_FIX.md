# Phase 75.14.1 — Closing predicate namespace fix

This patch fixes the Phase 75.14 closing-certificate predicate without changing any mathematical statement.

`RigidPacketZeroSchurBridge.lean` is in `namespace HC4.Valuation`, so the declaration
`ExactZeroSchurFourBlockData.HasClosingOutcome` was registered on the valuation namespace rather than
on the Newton namespace of the type.  Consequently field notation `B.HasClosingOutcome` searched for
`HC4.Newton.ExactZeroSchurFourBlockData.HasClosingOutcome` and failed.

The predicate is now the unambiguous valuation-level definition
`ExactZeroSchurClosingOutcome B`, and all three uses have been updated accordingly.

No theorem hypotheses or conclusions are strengthened, and no `sorry`, `admit`, `unsafe`, or axiom is added.
