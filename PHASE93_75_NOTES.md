# Phase 93.75 — Final restart assembly

Built over green Phase 93.74.3.

This phase deliberately does not invent a proposition named `HC4`: the
current Lean tree does not contain such a proposition.  Instead it closes
the entire geometric restart recursion and exposes the exact remaining
global interfaces.

## New full-state entry

`CanonicalExactCollisionEntry D` packages:

- the polynomial family over `K[tau]`;
- exact determinant defect;
- ordinary source homogeneity;
- the exact family-gradient collision from the zero section;
- the canonical right special point `e0`.

It converts directly to `CanonicalGeometricRestartState`.

## Full-state geometric reachability

`CanonicalGeometricReachable` keeps an actual canonical family at every
restart vertex while using the already-green `GlobalRestartProgress`
relation for the numerical well-founded step.

The strict restart output of Phase 93.74 is converted into an actual
successor state by:

`canonicalState_of_strictGeometricDefectRestart`.

## Closed global geometric recursion

`canonicalGeometricState_closedStep` combines the state fields with the
green Phase-93.74 theorem.

It has exactly two outcomes:

1. `HasCanonicalSmithRepairOrTerminal D complexity`;
2. a new full canonical state with strictly smaller determinant defect.

Strong induction on the defect then proves:

`canonicalGeometricRestart_reachesSmithFrontier`.

There is no continuation or scale hypothesis in this theorem.

## Terminal collision bridge

`canonicalGeometricState_specialFiber_exactCollision` specializes the
family collision to the canonical distinct collision `0 ~ e0`.

Then:

`canonicalGeometricState_terminalEndpoint_impossible_of_JC2`

calls the existing certified-terminal theorem and closes any state whose
special fibre is a `CertifiedTerminalEndpoint`.

## Generic final assembly

The project currently lacks a concrete proposition-level `HC4` definition,
so the patch gives a proposition-agnostic final assembly theorem:

`noCounterexample_of_JC2_canonicalEntry_and_frontierExhaustion`.

It proves that any counterexample predicate is impossible under JC2 once:

1. that predicate constructs a `CanonicalExactCollisionEntry`;
2. the canonical Smith local frontier is exhausted into the certified local
   endpoint machinery.

This isolates the real remaining proof boundary.  In particular, the
current `HasCanonicalSmithRepairOrTerminal` ends at a rigid rank-one packet
or a numerical repair successor and does not retain enough rank-two
geometric data to derive `CertifiedTerminalEndpoint` automatically.

No hidden global restart assumption is introduced.
