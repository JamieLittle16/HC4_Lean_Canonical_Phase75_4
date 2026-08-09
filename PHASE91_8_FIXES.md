# Phase 91.8 — linear-power recurrence profile

## New module

    HC4/Newton/LinearPowerRecurrence.lean

Phase 91.7 proves uniqueness for the finite directional recurrence.

Phase 91.8 constructs the canonical solution

    c(k) = choose(n,k) * v^k * (-u)^(n-k),

the coefficient profile of the binary power

    (v*X - u*Y)^n.

Using `Nat.choose_succ_right_eq`, Lean proves that this profile satisfies

    u*(k+1)*c(k+1) + v*(n-k)*c(k) = 0

for every `k < n`.

It also proves that every scalar multiple of this profile satisfies the
same recurrence.

Thus the next phase only needs to match one endpoint coefficient and invoke
the Phase 91.7 uniqueness theorem.  On each frozen external multi-index,
that will identify the entire transverse coefficient slice as a scalar
multiple of one linear-form-power profile.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
