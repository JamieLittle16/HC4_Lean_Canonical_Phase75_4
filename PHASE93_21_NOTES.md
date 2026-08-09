# Phase 93.21 — mixed departure adapter to the existing repair measure

## New module

    HC4/Newton/MixedDepartureAdapter.lean

Phase 93.20 is green and proves the universal preterminal dichotomy.

This phase performs the thin adapter requested by the v5/v6 restart audit.
It does not introduce a new termination formalism.

A genuine mixed pivot is mapped to the existing `RepairProgress` relation
by the concrete rank promotion

    rank 1 -> rank 2

at unchanged finite complexity.

The adapter preserves the Phase 93.20 exact source

    det Hess_(U,V) P = -(P_UV)^2 != 0.

The complementary branch remains explicitly

    IsPreterminalAffineSeparatedChannel.

Main theorem:

    preterminal_departure_repairProgress_or_affineSeparated.

The file also proves directly that the mixed rank promotion strictly lowers
the existing `RepairState.measure`.

This closes the algebraic matching requested by `MixedDepartureAdapter`.
The next step is the actual well-founded restart assembly: show each global
restart event is either this preterminal adapter, a previously classified
affine/separated endpoint, a rank-three/terminal endpoint, or a strict
complexity-lowering restart.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
