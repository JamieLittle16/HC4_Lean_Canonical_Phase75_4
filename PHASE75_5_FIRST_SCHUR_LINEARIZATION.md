# Phase 75.5 — First rank-one Schur-layer linearisation

This phase replaces the overly strong idea that the first raw parameter layer
must itself be the first Schur departure.

## New algebraic theorem

`HC4.Newton.FirstSchurLayerLinearization` treats a symmetric binary Schur
family

    [[A(X), B(X)], [B(X), C(X)]]

at a positive first transverse order `j`.  It assumes only that all
coefficients of `B` and `C` below `j` vanish.  Positive lower coefficients of
`A` are unrestricted.  It proves

    coeff_j (A*C - B^2) = A_0 * C_j.

Thus lower one-sided changes in the already-active rank-one direction cannot
pollute the first transverse determinant coefficient.

The HC4-specialised structure `PreterminalSchurDepartureData` additionally
identifies `A_0 = C b` and `C_j = P_{VV}` and proves that the determinant
coefficient is exactly `preterminalSchurLinearSource b V P`.

## Frontier handoff

`HC4.Valuation.FirstSchurDepartureBridge` now contains
`FrontierPreterminalSchurCertificate`.  A concrete certificate records only:

* the actual Schur series;
* first-transverse lower-layer vanishing;
* the actual coefficient potential `P_j`;
* compatibility between the binary Schur determinant and the corresponding
  layer of the full Hessian determinant;
* `j < defect`.

From this data, `isPreterminalSchurLayerModel` is now *proved*, rather than
assumed.  The already-green determinant-defect and mixed-departure machinery
then gives strict rank-one-to-rank-two repair or the affine/separated channel.

## Remaining geometric task

The next phase should construct `FrontierPreterminalSchurCertificate` from the
retained Smith-frontier provenance.  Importantly, it now suffices to prove
lower-layer vanishing of only the transverse Schur entries `B` and `C`; no
claim is required about earlier active-direction layers `A`.
