# Phase 91.8.1 — binomial cast-normalisation repair

Affected file:

    HC4/Newton/LinearPowerRecurrence.lean

The natural-number binomial identity itself was accepted:

    choose n (k+1) * (k+1) = choose n k * (n-k).

Only `exact_mod_cast` failed to normalise the resulting equality in the
coefficient field `K` all the way from casts of products to products of
casts.

Phase 91.8.1 replaces that tactic call by the explicit route:

    congrArg (fun t : ℕ => (t : K)) hchooseNat

followed by

    simpa only [Nat.cast_mul]

This is purely a coercion/elaboration repair. The theorem statement,
binomial identity, and recurrence proof are unchanged.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
