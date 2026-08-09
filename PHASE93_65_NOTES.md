# Phase 93.65 — Zero-slope Smith one-step dispatcher

Built over the green Phase 93.64.2 tree.

This phase connects a genuine polynomial family directly to both green
Smith branches.

## Automatic special-point consequences

If the moving marked sections reduce to

    a(0) = 0,
    b(0) = e_0,

then the three transverse coordinates of both sections are automatically
divisible by the parameter.  This removes the explicit
`HasSmithTransverseParameterFactor` assumptions from the dispatcher.

Exact polynomial-family gradient collision also descends automatically to
the exact special-fibre collision `0 ~ e_0`.

## Minimal branch

For a homogeneous special fibre of degree `D >= 2` with nonempty projected
Smith support, symmetric minimality at old minimum/base zero feeds directly
into the green Phase 93.62 theorem

    smithFirstWall_hasRepairOrTerminal_symmetricMinimal.

The old-minimum inequality is trivial and attainment follows from projected
support nonemptiness.

## Non-minimal branch

The complementary branch uses Phase 93.64 and derives the section
divisibility from the special-point identities.  It produces the exact
denominator-cleared numerical restart

    10*Delta -> 10*Delta - 4.

## Headline theorem

    zeroSlopeSmith_oneStepDispatcher

takes the genuine family, marked sections, special-fibre homogeneity,
nonempty projected support, exact Hessian defect, exact family collision,
canonical special points, and a state measured on the fixed-ten scale.

It returns either

- a strict fixed-ten Smith defect restart; or
- the canonical local rigid/repair Smith outcome.

## Important remaining global issue

This theorem is intentionally one-step.

Repeatedly applying a theorem which freshly ramifies by ten would not by
itself prove well-founded descent relative to the previous raw defect.
Final global assembly must therefore formalise one of:

1. a single common ramification chosen before the whole restart sequence,
   with every later Smith tilt expressed on that fixed parameter; or
2. a pole-depth-minimal normalisation argument eliminating repeated strict
   Smith improvements before the restart induction.

This scale issue is now explicit rather than hidden behind the numerical
`GlobalRestartState`.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
