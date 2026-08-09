# Phase 91.11.1 — explicit amplitude lambda repair

Affected file:

    HC4/Newton/LinearPowerPacketNormalForm.lean

Phase 91.11 attempted to construct the amplitude function using placeholder
notation:

    transverseSliceAmplitude u F · i j n

Lean 4.24 does not accept this occurrence of `·`, and consequently tried
to infer the wrong function type and field instance.

Phase 91.11.1 replaces it by the explicit function

    fun r => transverseSliceAmplitude u F r i j n

No theorem statement or mathematical content is changed.

The reported `hleft` message is only an unused-variable linter warning and
does not affect verification.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
