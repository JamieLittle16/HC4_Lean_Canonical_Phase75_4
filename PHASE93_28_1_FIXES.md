# Phase 93.28.1 — avoid dependent `fin_cases` on let-bound permutation images

Affected module:

    HC4/Newton/TerminalTwoZeroPattern.lean

The Phase 93.28 proof introduced

    a : Fin 4 := π 0
    b : Fin 4 := π 1

and then attempted `fin_cases a` / `fin_cases b`.

On the pinned Lean version this causes dependent-elimination failures because
`a` and `b` are let-bound to permutation images.

The repair avoids dependent case splitting entirely.

From

    a != 0, a != 1, a.val < 4

the proof derives with `omega`

    a.val = 2 OR a.val = 3,

and similarly for `b`.  `Fin.ext` converts these value equalities back to
equalities in `Fin 4`.  Since `a != b`, the only possibilities are

    (a,b) = (2,3)  or  (3,2).

The existing weight equations `lambda a = d` and `lambda b = d` then give

    lambda 2 = d AND lambda 3 = d.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
