# Phase 93.45 — Smith strict-repair integration

Built against the exact green Phase 93.44 Smith source and Phase 93.41 mixed-departure source.

## Purpose

Turn the certificate-free Smith re-entry dichotomy into the exact existing finite-repair language.

The patch introduces restart-facing predicates:

- `HasSmithSquareOrAxisPacket`
- `HasSmithRankTwoEscape`
- `HasSmithStrictRepairOutcome`
- `HasSmithFirstWallRepairOutcome`

and proves that exact homogeneous axis collision + Smith pole minimality + attainment gives:

    explicit square/axis packet
    OR
    genuine rank-two escape
      + RepairProgress(rank 1, rank 2)
      + strict decrease of RepairState.measure.

The canonical rank promotion lowers the measure by exactly one.

## Main theorem

`homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_firstWallRepair`

This retains:
- nonempty canonical Smith subface;
- persistent-packet support;
- nonzero canonical Smith polynomial;
- the square-or-strict-repair restart outcome.

Companion theorems show:
- nonsquare => strict repair;
- no strict repair => square;
- nonsquare => exact one-unit measure drop.

## Scope honesty

This patch connects the *algebraic rank-two Smith certificate* to the already-defined abstract finite repair state. It does not by itself identify a subsequent concrete Rees/Schur geometric event; that is a separate global assembly/interface question.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
