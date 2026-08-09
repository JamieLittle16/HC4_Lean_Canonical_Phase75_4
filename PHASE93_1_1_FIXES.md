# Phase 93.1.1 — explicit rank-bound repair

Affected file:

    HC4/Newton/FiniteRepairTermination.lean

`omega` did not automatically extract the dependent structure fields

    1 <= s.rank
    s.rank <= 3

when reasoning about

    3 - s.rank.

Consequently it treated the rank as unconstrained and could not prove the
rank-defect bounds.

Phase 93.1.1 explicitly names the stored rank bounds before invoking
`omega` in:

    RepairState.rankDefect_le_two
    RepairState.rankDefect_lt_of_rank_lt

No theorem statement, repair measure, or mathematical argument is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
