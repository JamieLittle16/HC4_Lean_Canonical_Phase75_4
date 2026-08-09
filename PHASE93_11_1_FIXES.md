# Phase 93.11.1 — exact-collision helper repair

Affected file:

    HC4/Newton/ExactCollisionFirstWall.lean

The Phase 93.11 failure had two local causes.

## Support-sum syntax

The theorem statement used scoped big-operator syntax

    ∑ d in F.support, ...

without opening the corresponding parser scope.  Because the statement
failed to parse, the later uniqueness theorem also could not see
`mvGradientComponentAt_eq_sum_support`.

The repair avoids the scoped notation entirely and writes

    F.support.sum (fun d => ...).

The proof itself is unchanged.

## Positive derivative degree

After applying homogeneous coefficient vanishing, Lean asks for

    0 != D - 1.

The previous proof constructed the opposite orientation and then attempted
to simplify it.  The repair lets `omega` prove the required inequality
directly from `2 <= D`.

No theorem statement is mathematically weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
