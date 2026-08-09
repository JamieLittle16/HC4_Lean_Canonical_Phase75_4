# Phase 93.22.2 — stable Finsupp weighted-sum repair

Affected file:

    HC4/Newton/TerminalConformalWeight.lean

The pinned Mathlib build does not expose
`Finsupp.sum_single_add_single`.

The quadratic weighted-degree proof is now based only on older, stable
Finsupp big-operator primitives:

    Finsupp.sum_add_index'
    Finsupp.sum_single_index

The weighted-degree summand

    (n : ℤ) * lambda k

is additive in `n` and vanishes at zero, so `sum_add_index'` splits the
weighted degree of

    single i 1 + single j 1

into the sum of the two singleton weighted degrees.  The singleton sums
then simplify directly.  This proof works uniformly whether `i = j` or
`i != j`; the fragile overlap case split is removed.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
