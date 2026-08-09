# Phase 93.11.2 — deterministic support decomposition repair

Affected file:

    HC4/Newton/ExactCollisionFirstWall.lean

## Support decomposition

The previous proof used

    rw [F.as_sum]

in a goal where `F` also occurred inside the right-hand-side support
contributions.  That rewrite was too broad and did not leave the intended
linear finite-sum expression.

The repair applies `congrArg` to `F.as_sum` with the exact map

    P |-> eval point (pderiv i P).

This changes only the polynomial being differentiated/evaluated.  The
resulting finite sum is then discharged by the additive-map simp lemmas.

## Homogeneous derivative degree

After `hp.coeff_eq_zero`, the required fact is `0 != D-1`.  We now first
prove

    0 < D-1

from `2 <= D`, and pass the correctly oriented inequality via

    simpa using (ne_of_lt hpos).

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
