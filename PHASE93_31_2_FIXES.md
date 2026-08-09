# Phase 93.31.2 — robust positive-weight arithmetic

Affected modules:

    HC4/Newton/PositiveWeightTriangularSupport.lean
    HC4/Newton/TerminalPositiveWeightTriangularReduction.lean

The Phase 93.31.1 build reached the genuinely new triangular-support module.

## Arithmetic repair

The original proof asked `linarith`/`nlinarith` to reason directly with
products

    (m i : Z) * lambda i.

This was brittle and caused both failed contradictions and heartbeat
exhaustion.

The repaired proof separates the nonlinear facts into small order lemmas:

* a nonzero exponent gives

      lambda i <= (m i : Z) * lambda i;

* a zero weighted term and positive weight forces `m i = 0`;

* equality

      (m i : Z) * lambda i = lambda i

  with nonzero exponent and positive weight forces `m i = 1`.

After these facts are established, all four-coordinate arguments are purely
linear comparisons between the weighted summands and their total.

No heartbeat or recursion limit is increased.

## Corrected minimum-weight statement

The helper theorem

    minimumPositiveWeight_support_is_linear

requires `0 < t`.

That hypothesis is mathematically necessary: `P = 1` at weighted degree
`t = 0` is otherwise a counterexample.

In the actual terminal application `t = lambda i`, so the hypothesis is
immediately supplied by `hpos i`.  No terminal theorem loses strength.

## Minor cleanup

The explicit finite weighted-degree expansion no longer runs `ring` after
`simp` has already closed the goal.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
