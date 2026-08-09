# Phase 93.31.1 — weighted-homogeneous argument-order repair

Affected module:

    HC4/Newton/TerminalPermutedGradient.lean

Mathlib defines `MvPolynomial.IsWeightedHomogeneous w P d` as

    ∀ ⦃m⦄, coeff m P ≠ 0 -> Finsupp.weight w m = d,

so the exponent `m` is implicit.

In the reverse conversion from Mathlib weighted homogeneity to the
project-local `IsIntegralWeightedHomogeneous`, the Phase 93.31 proof used

    hhom m hm

which attempts to pass the exponent as the explicit coefficient-nonzero
proof argument.

The repair uses

    hhom hm

and lets Lean infer the implicit exponent from `hm`.

The unused `nsmul_eq_mul` simp argument in the weighted-degree identity is
also removed.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
