# Phase 93.6.1 — Smith balance arithmetic repair

Affected file:

    HC4/Newton/SmithExtremeBalance.lean

Two proof-engineering issues are repaired.

## Rational product -> natural product

The previous proof ran

    norm_num at hq ⊢

before `exact_mod_cast`.  On the natural-number goal `k*l = 1`, this
simplification decomposed the target farther than intended.

The repair first constructs the explicit casted equality

    (((k*l : ℕ) : ℚ)) = 1

using `Nat.cast_mul`, and only then applies `exact_mod_cast`.

## First-quadrant separator positivity

The previous proof asked `linarith` to handle products such as

    k*a
    (k*l + 1)*b.

Those are nonlinear from the tactic's point of view.

The repair instead proves:

* both separator coefficients are positive;
* in each branch one summand is positive;
* the other summand is nonnegative;

and concludes with `add_pos_of_pos_of_nonneg` or
`add_pos_of_nonneg_of_pos`.

This uses only ordered-ring monotonicity and is insensitive to nonlinear
arithmetic tactic behaviour.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
