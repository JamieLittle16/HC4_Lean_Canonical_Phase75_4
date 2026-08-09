# Phase 93.28.2 — name the shifted exponent in the support-to-derivative proof

Affected module:

    HC4/Newton/TerminalTwoZeroSupport.lean

The pinned elaborator failed on the inline application

    (m + Finsupp.single i 1) i

inside the proof that support-level independence of a variable forces its
formal partial derivative to vanish.

This repair introduces

    mPlus : Fin 4 →₀ ℕ := m + Finsupp.single i 1

and proves explicitly

    mPlus i = m i + 1,

hence `mPlus i != 0`.

If `coeff mPlus P` were nonzero, the support hypothesis would force
`mPlus i = 0`, a contradiction.  The backported coefficient formula for
`pderiv` then simplifies to zero exactly as before.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
