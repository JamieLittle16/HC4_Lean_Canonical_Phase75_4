# Phase 91.12 — orientation-independent rank-two packet classification

## New module

    HC4/Newton/RankTwoHomogeneousPacketClassification.lean

Phase 91.11 proves the generic `b ≠ 0` left-pivot packet normal form.

Phase 91.12 closes the remaining pivot orientations.

### Left pivot with `b = 0`

The canonical kernel direction `(-b,a)` becomes `(0,a)`. Since a left
pivot has `a ≠ 0`, vanishing of this directional derivative gives

    pderiv j F = 0.

Phase 91.5 then forces pure left-axis transverse support.

### Right-axis pivot

The kernel is `(1,0)`. Phase 91.4 gives vanishing directional derivative,
and Phase 91.5 forces pure right-axis transverse support.

### Unified theorem

The predicate

    HasRankTwoHomogeneousPacketClassification

records the three possible rigid outcomes:

1. generic coefficientwise linear-power normal form;
2. pure left-axis normal form;
3. pure right-axis normal form.

The theorem

    rankTwoHomogeneousPacketClassification

starts only from a nonzero determinant-zero binary Schur block plus the
appropriate Hessian-kernel/homogeneous derivative hypotheses and performs
the entire orientation split internally.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
