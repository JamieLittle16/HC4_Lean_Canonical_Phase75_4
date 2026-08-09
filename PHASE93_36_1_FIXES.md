# Phase 93.36.1 — recursive fibre-derivative rewriting

Affected module:

    HC4/Newton/TerminalOneZeroPlanarFibre.lean

The Phase 93.36 build accepted:

* the constant transverse determinant theorem;
* the one-zero fibre construction;
* both first-order derivative/specialisation commutation lemmas.

The only failure was in the planar Jacobian identity.

After the original four one-shot rewrites, two nested derivative terms
remained:

    pderiv 1 (oneZeroFibreSpecialise c (pderiv 2 F))
    pderiv 0 (oneZeroFibreSpecialise c (pderiv 3 F)).

These are exactly further instances of the same two already-proved
commutation lemmas.

## Repair

Replace the four one-shot `rw` calls with

    simp_rw [pderiv_zero_oneZeroFibreSpecialise,
      pderiv_one_oneZeroFibreSpecialise]

so the specialisation/derivative identities are applied recursively at
every derivative depth occurring in the planar Jacobian expression.

The final algebraic simplification is unchanged.

No theorem statement, hypothesis, mathematical argument, or heartbeat
setting changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
