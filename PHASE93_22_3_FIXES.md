# Phase 93.22.3 — explicit Finsupp summand instantiation

Affected file:

    HC4/Newton/TerminalConformalWeight.lean

The pinned compiler recognised `Finsupp.sum_add_index'`, but Lean inferred
slightly different elaborations of the weighted summand on the two sides
of the target.

This repair removes that ambiguity completely.

The proof now introduces one named function

    weightTerm : σ -> ℕ -> ℤ

and explicitly instantiates `Finsupp.sum_add_index'` with

    f := single i 1
    g := single j 1
    h := weightTerm.

The two singleton sums are then evaluated explicitly with
`Finsupp.sum_single_index`, again using the same named `weightTerm`.

Thus no coercion or summand function is left for unification to infer.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
