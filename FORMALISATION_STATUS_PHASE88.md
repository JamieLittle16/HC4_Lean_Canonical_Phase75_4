# Formalisation status — Phase 88 candidate

## Previously user-verified green

Through Phase 87.1, including:

- complementary-edge rigidity;
- rank-three logarithmic Hessian/fraction bridge;
- local pole-order coefficient certificates;
- polynomial autonomous degree bound `deg R <= 2` once a polynomial ODE is
  available;
- root translation;
- finite-preimage/two-chart pole removal;
- canonical reduced source/target fractions;
- finite RatFunc rank-three assembly;
- exact source infinity certificates `rho(infinity)=deg phi` and
  `eta(infinity)=0` in degree form.

## Phase 88 candidate

Phase 88 is intended to close the remaining rational-to-polynomial seam.
The strongest endpoint starts from singularity of the concrete substituted
rank-three logarithmic core and, assuming the manifest raw target denominator
is nonzero and the reduced source has positive denominator degree, produces
an explicit polynomial autonomous right-hand side.

This phase is **not** yet kernel-verified in the assistant environment.
Jamie’s pinned `./verify.sh` run remains authoritative.

## Still downstream after Phase 88

- turn the resulting RatFunc polynomial identity into the exact cleared
  polynomial-ODE interface consumed by Phase 79;
- invoke the already-green degree-≤2 and quadratic coefficient-rigidity
  layers;
- assemble the manuscript rank-three asymptotic/character case split and
  terminal pencil contradictions into the exact rank-three edge theorem;
- then return to the GN/top-degree and four-sided/global assembly obligations.
