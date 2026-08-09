# Phase 93.9.1 — denominator-clearing tactic repair

Affected file:

    HC4/Newton/SmithPoleMinimality.lean

The Phase 93.9 build reached the denominator-clearing identity and
`field_simp [hDne]` closed the goal completely.  The following `ring`
therefore produced Lean's

    No goals to be solved

error.

The redundant `ring` is removed.

The only warning in the same file came from deprecated

    (mul_lt_mul_left hDposQ).2 h

and is replaced by the already-supported

    mul_lt_mul_of_pos_left h hDposQ.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
