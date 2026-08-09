# Phase 93.40 — first-departure binary Hessian source

## Purpose

Phase 93.39 closed the one-zero terminal endpoint wrapper.  The remaining
restart-exhaustion interface is the preterminal mixed departure before the
call to `FiniteRepairTermination`.

This phase factors out the exact algebra that should sit immediately below
that adapter.

For a first departing coefficient

    P_j(U,V;X) = V * A(U;X) + B(U;X),

the binary Hessian in `(U,V)` is schematically

    [[*,   A_U],
     [A_U,   0 ]],

so

    det Hess_(U,V)(P_j) = -(A_U)^2.

The new module proves, over a field:

* `firstDepartureBinaryDet_eq_neg_sq`;
* `firstDepartureBinaryDet_eq_zero_iff`;
* `firstDeparture_mixed_source_ne_zero`;
* `firstDeparture_binary_source_dichotomy`;
* a characteristic-zero spelling for the final adapter.

Thus the local split is now exposed as a theorem-level interface:

    A_U = 0  -> zero source / affine-separated channel
    A_U != 0 -> nonzero mixed source

## Deliberate scope

This patch does **not** guess the current signature of
`HC4.Newton.FiniteRepairTermination`.  The next patch should open the actual
93.40-green `FiniteRepairTermination.lean` and `MixedDepartureAdapter.lean`
and connect the nonzero-source theorem to the existing termination theorem
field-by-field.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
