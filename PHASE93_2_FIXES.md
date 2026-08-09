# Phase 93.2 — rank-one classification to repair progress

## New module

    HC4/Newton/RankOneRepairProgress.lean

This phase is the first concrete bridge from the green local packet
classification into the Phase 93.1 finite termination state.

It introduces canonical repair states of rank 1, 2 and 3 at a fixed
Rees/Newton complexity.

Lean proves:

    rankOne_to_rankTwo_repairProgress
    rankTwo_to_rankThree_repairProgress

and the corresponding exact one-unit drops in the Phase 93.1 measure.

The Phase 92.3 re-entry alternatives are named as:

    HasRigidRankOnePacket
    HasRankTwoPacketEscalation.

The key theorem is

    rankOnePersistentPacket_rigid_or_rankTwoProgress.

Starting only from:

    persistent-packet support
    F != 0

it proves either:

1. the discriminant-zero square/axis rigid certificate; or
2. the discriminant-nonzero/trivial-kernel certificate together with the
   actual termination-state transition

       (rank 1, complexity c) -> (rank 2, complexity c)

   satisfying `RepairProgress`.

Thus a non-rigid rank-one persistent packet now feeds directly into the
well-founded measure, rather than merely being described informally as
"rank two".

This does NOT yet prove that every HC4/Rees repair satisfies progress.
The next bridge must connect the rank-two and rank-three local outcomes to
either terminality or complexity decrease/rank increase.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
