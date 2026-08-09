# Phase 93.27.2 — doubling cancellation direction repair

Affected file:

    HC4/PlanarDoublingInjectivity.lean

The only remaining Phase 93.27 build failure was in the fibre-recovery
step.  The pointwise equality has the form

    vecMul v (J u) i + dD u i
      =
    vecMul v' (J u) i + dD u i.

The common summand is on the right, so the correct cancellation theorem is

    add_right_cancel

rather than `add_left_cancel`.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
