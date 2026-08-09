# Phase 75.7 — Exact Schur clock collapse

This phase strengthens the green first-transverse Schur machinery.

## New algebraic facts

For a rank-one Schur series whose cleared determinant satisfies

    det(S) = Q * X^Delta

with `Q.coeff 0 != 0`:

* a positive transverse layer must exist;
* every determinant coefficient before the first transverse order vanishes;
* the first transverse order is at most `Delta`.

Therefore the first transverse order has exactly two possibilities:

    j < Delta   (preterminal)
    j = Delta   (determinant-closing)

There is no no-departure branch and no post-closing branch.

## Frontier endpoint

`FrontierExactRankOneSchurSeries.preterminalRepair_or_closing` now gives:

* strict rank-one -> rank-two repair or affine/separated continuation in the preterminal case; or
* a genuinely nonzero transverse Schur coefficient exactly at determinant closure.

No `sorry`, `admit`, or `unsafe` is introduced.
