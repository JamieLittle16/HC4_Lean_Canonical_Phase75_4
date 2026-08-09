# Phase 92.1.1 — nested support case-split repair

Affected file:

    HC4/Newton/RankOnePersistentPacket.lean

The `YZ` and `ZZ` support-identification proofs had a tactic-branch
indentation error.

After splitting on `t = y`, the split on `t = z` must occur inside the
`t ≠ y` branch.  Phase 92.1 accidentally began it as a sibling bullet,
so the final "other variable" branch did not have the needed `t ≠ z`
hypothesis and Lean left the equality unsolved.

Phase 92.1.1 nests those two `by_cases htz : t = z` blocks correctly.

The harmless unused `Finsupp.single_apply` simp argument in the `YY` proof
is also removed.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
