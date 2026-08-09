# Phase 93.1 — finite repair termination engine

## New module

    HC4/Newton/FiniteRepairTermination.lean

With the rank-one re-entry certificate green, Phase 93 begins the
termination layer.

A `RepairState` stores:

* active transverse rank, constrained to `1 <= rank <= 3`;
* a natural-valued Rees/Newton complexity.

`RepairProgress s t` means either:

1. `t.complexity < s.complexity`; or
2. complexities are equal and `s.rank < t.rank`.

The finite measure is

    3 * complexity + (3 - rank).

Because the rank defect is at most two, lowering complexity by one beats
every possible rank-defect change; at fixed complexity, increasing rank
strictly lowers the defect.

Lean proves:

    repairState_measure_lt_of_progress

and then the quantitative chain bound

    measure(states n) + n <= measure(states 0).

Consequently:

    no_infinite_strictRepairChain

rules out an infinite sequence of genuine repairs.

This phase deliberately proves only the well-founded combinatorial engine.
The substantive next bridge is to show that every actual nonterminal
Rees/Newton repair constructed by the HC4 argument satisfies
`RepairProgress`.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
