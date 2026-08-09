# Phase 93.12.3 — explicit weight-single and factorwise nonzero repair

Affected file:

    HC4/Newton/SmithFirstWallTransverse.lean

## Homogeneous weight

After rewriting the contributor shape, the pinned simplifier leaves

    weight 1 (single x (d x)) + weight 1 (single i 1) = D.

The repair explicitly enables the pinned theorem

    Finsupp.weight_single

so these two terms reduce to `d x` and `1`.

## Blocker contribution

The previous final simplification exposed the nonzero product as a
conjunction rather than collapsing it to the coefficient hypothesis.

The repair follows that structure directly. It proves separately:

1. the blocker coefficient is nonzero from support membership;
2. its transverse exponent is exactly `1`, hence its cast is nonzero;
3. after differentiation, the remaining pure-axis exponent evaluates to
   `1` at the coordinate-axis point.

The three factors are combined using `mul_ne_zero`.

The unused hypothesis `1 <= D` is removed from the contribution lemma;
it was not mathematically needed.

No theorem statement used downstream is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
