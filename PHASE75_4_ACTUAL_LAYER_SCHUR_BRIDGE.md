# Phase 75.4 — Exact parameter layer and first-Schur bridge

## Purpose

This patch removes a subtle mismatch in the departure-frontier clock and
factors the exact remaining preterminal determinant calculation into a named
Lean interface.

`firstPositiveParameterOrder` is an X-adic valuation selector on source
coefficient polynomials. It is not the same as the first positive parameter
exponent actually occurring in the family: for example, `1 + X^5` has
valuation zero but has a nonzero fifth layer.

The new `ActualParameterLayer` module therefore reconstructs the exact
coefficient potential `P_j` in

    P = sum_j X^j P_j

and selects the least positive exponent that actually occurs.

## New proved layer API

- `familyParameterLayer`
- `familyParameterLayer_coeff`
- `familyParameterLayerOrders`
- `mem_familyParameterLayerOrders_iff`
- `firstPositiveActualParameterOrder`
- positivity, realisation and minimality lemmas
- `CanonicalSmithDepartureFrontier.actualParameterClock_trichotomy`

## New first-Schur handoff API

`FirstSchurDepartureBridge` proves from the exact Hessian-defect equation that
all determinant layers below `Delta` vanish:

    hessianDefect_parameterLayer_eq_zero_of_lt

It then introduces the explicit local identity

    IsPreterminalSchurLayerModel f j b V

which says that the actual j-th determinant layer is exactly the linear
rank-one Schur source `b * (P_j)_{VV}`.

Once that identity is supplied, the patch proves:

    preterminalSchurLayer_source_zero

and immediately invokes the already-green mixed-departure adapter to obtain
strict rank-one -> rank-two repair progress or the affine/separated channel:

    preterminalSchurLayer_canonicalStrictRepair_or_affineSeparated

with a specialisation to the exact first actual layer.

## Audit boundary

This patch does NOT assert `IsPreterminalSchurLayerModel` without proof.
That identity requires the retained stationary rank-one Schur line, its
adapted coordinates, and the statement that every lower Schur coefficient is
one-sided. The current `CanonicalSmithDepartureFrontier` retains the family,
packet and exact Hessian defect, but does not yet package that adapted Schur
filtration certificate.

That is now the exact rigid-branch interface to add next. The rank-two
escalation branch likewise needs an adapter from `HasRankTwoPacketEscalation`
to the concrete Rees/Schur entry expected by the already-developed rank-two
terminal/repair modules.

No `sorry`, `admit`, axiom, or synthetic proof of either missing geometric
adapter is introduced by this patch.
