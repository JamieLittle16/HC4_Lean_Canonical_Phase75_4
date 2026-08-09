# Phase 93.46 — Canonical repair exhaustion

Built directly against the exact green Phase 93.45 repair checkpoint.

## Main advances

### 1. One repair relation, exactly measured
`RepairProgress s t` is now proved equivalent to

    t.measure < s.measure.

The relation is also proved transitive.

### 2. Canonical rank ladder is finite
At fixed complexity:

    rank 1 -> rank 2 -> rank 3

are the only possible rank promotions.

From rank two, any repair either lowers complexity or reaches rank three.
From rank three, every further repair must lower complexity.
The two promotions consume exactly two units of the repair measure.

### 3. Rank-two local closure
A nonzero rank-two Schur entry under the existing Phase 91 hypotheses now has
a single restart-facing dichotomy:

    rigid determinant-zero terminal
    OR
    determinant-nonzero rank 2 -> rank 3 strict repair.

The nonterminal branch also carries the fact that every subsequent repair
from rank three lowers complexity.

### 4. Mixed and Smith branches share identical repair states
The preterminal mixed-departure states are proved definitionally equal to
the canonical `rankOneRepairState` / `rankTwoRepairState`.

Canonical-state mixed-departure wrappers are added.

### 5. Smith nonsquare branch exhausts the fixed-complexity rank ladder
The canonical Smith restriction now returns either:

    `HasRigidRankOnePacket`

or

    `HasRankTwoPacketEscalation`
    + canonical rank 1 -> rank 2 progress
    + strict measure decrease.

In the non-rigid branch, any later rank-two repair either lowers complexity
or reaches rank three, and after rank three every repair lowers complexity.

## Scope boundary

This closes the abstract finite-rank repair ladder and the local rank-two
determinant dichotomy.  A global `RestartClassification` theorem must still
show that each concrete geometric restart supplies one of these already
formalised local repair events or an endpoint.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
