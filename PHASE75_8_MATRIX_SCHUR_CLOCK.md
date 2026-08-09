# Phase 75.8 — Matrix Schur Clock

This phase removes the partial-Legendre potential from the preterminal
rank-one exhaustion step.

## New algebra

* `HC4.Newton.GeneralFourBlockSchur`
  - general symmetric active 2x2 block `[a b; b d]`;
  - denominator-cleared Schur entries;
  - exact identity `det(cleared Schur) = det(active) * det(full)` over any
    commutative ring.

* `HC4.Newton.RankOneSchurSeriesAlignment`
  - constant left-pivot congruence using kernel vector `(-b,a)`;
  - right-axis alignment by axis swap;
  - exact determinant scaling of the aligned polynomial Schur series.

## Stronger preterminal route

`FrontierExactRankOneSchurClock` records only the exact matrix Schur series,
its nonzero leading coefficient, and the cleared determinant factorisation.
It does not assume a potential-level kernel-coefficient identification.

At the automatically selected first transverse order `j < defect`:

1. first-Schur linearisation gives `coeff_j(det S) = leading * kernel_j`;
2. exact determinant closure gives `coeff_j(det S) = 0`;
3. nonzero leading coefficient gives `kernel_j = 0`;
4. first-transverse nonvanishing therefore forces `offDiag_j != 0`;
5. this is packaged directly as strict rank-one -> rank-two `RepairProgress`.

Thus affine parameter layers that do not change the Schur Hessian no longer
create a separate local branch.

## Four-block constructor

`FrontierExactFourBlockSchurData` is the remaining concrete extraction
interface: an actual symmetric 2+2 polynomial Hessian series with

* full determinant `X^defect`;
* active determinant with nonzero constant term;
* rank-one constant cleared Schur block.

From this data, left- and right-pivot constructors build an exact matrix
Schur clock automatically and prove `rankTwoProgress_or_closing`.

No `sorry`, `admit`, or `unsafe` is introduced.
