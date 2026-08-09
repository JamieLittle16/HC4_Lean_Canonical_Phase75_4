# Phase 93.76.1 — proposition wrapper fix

The first Phase 93.76 build exposed one structural Lean mistake.

`CanonicalSmithLosslessFrontier` is deliberately a rich data structure in
`Type`, because the final first-departure/rank-two proof needs to inspect
its retained family, marked sections and Smith certificates.  The first
draft mistakenly used that data type directly as if it were a proposition.

This patch introduces:

    HasCanonicalSmithLosslessFrontier D complexity : Prop :=
      Nonempty (CanonicalSmithLosslessFrontier D complexity)

The rich structure is unchanged.

All theorem-facing local dispatchers and well-founded exhaustion results now
return the proposition wrapper.  Consequently:

- theorem codomains are propositions;
- `Or` and conjunctions are well-typed;
- the no-wall existential can be eliminated into the frontier proposition;
- the generic final implication unpacks the actual frontier object only
  where `CanonicalLosslessSmithFrontierExhaustionUnderJC2` consumes it.

A compatibility theorem
`hasLosslessFrontier_supplies_compactFrontier` forgets the proposition-level
lossless frontier to the old compact local predicate.

No mathematical assumption or geometric theorem is changed.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
