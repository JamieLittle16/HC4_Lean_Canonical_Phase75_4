# Phase 93.36.2 — explicit second-derivative fibre identities

Affected module:

    HC4/Newton/TerminalOneZeroPlanarFibre.lean

The Phase 93.36.1 build confirms that recursive first-order fibre
specialisation works.  The remaining failure came from broad simplification
of the final Jacobian product: Lean attempted product cancellation and
replaced the desired equality by an irrelevant disjunction.

## Repair

The Jacobian proof now establishes four explicit second-derivative
specialisation identities first:

    h22 :
      d0(d0 fibre(F)) = fibre(d2(d2 F))

    h33 :
      d1(d1 fibre(F)) = fibre(d3(d3 F))

    h32 :
      d1(d0 fibre(F)) = fibre(d3(d2 F))

    h23 :
      d0(d1 fibre(F)) = fibre(d2(d3 F))

Each is proved by two direct applications of the already-green first-order
commutation lemmas.

The planar Jacobian determinant is then unfolded and rewritten by exactly
these four equations.  Only after all outer derivatives have disappeared
do we simplify the ring-homomorphic fibre specialisation of

    Delta23 =
      F22*F33 - F32*F23.

This prevents the simplifier from cancelling products or generating
zero-factor disjunctions.

No theorem statement, hypothesis, mathematical argument, or heartbeat
setting changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
