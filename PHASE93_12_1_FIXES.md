# Phase 93.12.1 — Finsupp/API repair for transverse first wall

Affected file:

    HC4/Newton/SmithFirstWallTransverse.lean

The Phase 93.12 failures were all representation/API issues.

## Explicit Finsupp subtraction type

Every occurrence of

    d - Finsupp.single i 1

is now written with the explicit exponent type

    d - (Finsupp.single i 1 : σ →₀ ℕ).

This resolves the metavariable ambiguity that made Lean treat the
subtraction result as a non-function.

## `zero_pow`

The pinned theorem expects an exponent nonzero proof directly, so the file
now uses

    zero_pow hrj

instead of passing `Nat.pos_of_ne_zero hrj`.

## Homogeneous support degree

The unavailable `Finsupp.degree_apply` API is removed entirely.

After proving the contributor shape

    d = single x (d x) + single i 1,

the proof rewrites the already-available theorem

    hhom.degree_eq_sum_deg_support hd

by that shape and simplifies.  This directly yields

    d x + 1 = D.

## Blocker derivative evaluation

Two explicit helper lemmas are added:

    transverseAxisBlockerExponent_apply_transverse
    transverseAxisBlockerExponent_sub_transverse.

They prove the blocker has transverse exponent one and that differentiation
leaves exactly `single x (D-1)`.

The nonzero contribution theorem then rewrites by these facts and evaluates
the pure x monomial at `e_x`, rather than relying on a large global `simp`.

No theorem statement is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
