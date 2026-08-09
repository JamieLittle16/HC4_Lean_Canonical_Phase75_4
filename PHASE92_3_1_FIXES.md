# Phase 92.3.1 — re-entry proposition parenthesisation repair

Affected file:

    HC4/Newton/RankOnePacketReentry.lean

The intended zero-discriminant branch is

    discriminant = 0 ∧ (left-square-geometry ∨ right-axis-geometry).

Because the inner disjunction was not enclosed as a whole, Lean parsed the
proposition as

    (discriminant = 0 ∧ left-square-geometry) ∨ right-axis-geometry,

before the outer re-entry disjunction.  Consequently, the proof command

    refine ⟨hdisc, ?_⟩

was asked to construct an `Or` rather than an `And`.

Phase 92.3.1 adds the missing parentheses around the geometry disjunction.
The existing proof then matches the intended proposition directly.

No theorem statement in the mathematical sense is changed: this repair
makes the formal predicate match the stated/documented intended grouping.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
