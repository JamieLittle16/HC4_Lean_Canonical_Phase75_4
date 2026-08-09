# Phase 93.18.1 — rewrite-scope repair for exact packet collision

Affected file:

    HC4/Newton/RankOnePacketExactCollision.lean

The Phase 93.18 failures had one common cause: global `rw` rewrote the
original polynomial `F` not only in the polynomial being transformed, but
also inside the coefficient accessors on the right-hand side.

That changed expressions such as

    rankOnePacketCoeffYY ... F

into coefficients of the model polynomial itself.

The repair removes those global rewrites.

## Algebraic model equality

`rankOnePersistentPacket_eq_algebraicModel` now uses an explicit `calc`:

    F = rankOnePacketMonomialModel ... F
      = rankOnePacketAlgebraicModel ... F.

Thus the coefficient parameter remains the original `F`.

## Evaluated gradients

The y- and z-gradient lemmas now use `congrArg` to transform only the
polynomial argument of `mvGradientComponentAt`.

The model's coefficient accessors therefore remain attached to the
original `F`, while the left-hand polynomial is replaced by the algebraic
normal form.

After this controlled rewrite, simplification computes the evaluated
derivatives and `ring_nf` normalises the resulting scalar identities.

No mathematical hypothesis or theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
