# Formalisation status after candidate Phase 81

Phase 80 is reported green by the user.  Phase 81 is a candidate until the
pinned Lean 4.24 / Mathlib build succeeds locally.

If green, the following portion of the autonomous-ODE manuscript proof is
machine checked:

- translation to a nonzero root;
- exact pole-order coefficients;
- polynomial autonomous degree ≤ 2;
- quadratic coefficient rigidity;
- finite-chart coverage of every reduced-rational target value except the
  single value represented at infinity.

Remaining rank-three front-half work:

1. connect the rank-three autonomous rational expression to a reduced
   numerator/denominator pair;
2. use the finite preimage theorem to exclude finite poles of the autonomous
   right-hand side away from the infinity value;
3. supply the infinity-chart certificate at the exceptional value;
4. conclude the autonomous right-hand side is polynomial and invoke the
   already-green Phases 79/77 chain;
5. assemble the complete rank-three edge theorem.


## Phase 81.1
One local elaboration repair only: replaced an invalid `change` across polynomial evaluation by `simpa using hroot`. Kernel verification is pending the user's pinned local build.
