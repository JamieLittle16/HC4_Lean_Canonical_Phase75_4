# Formalisation status after Phase 83 candidate

## Green prerequisites (reported by user)

- Phase 75.2 complementary-edge rigidity
- Phase 76 rank-three logarithmic Hessian bridge
- Phase 77.3 quadratic autonomous coefficient rigidity
- Phase 78.1 local pole-order coefficients
- Phase 79.1 polynomial autonomous degree <= 2
- Phase 80 translation to a nonzero root
- Phase 81.1 finite-preimage / two-chart source cover
- Phase 82 target denominator removal

## Candidate in this phase

`rankThree_fraction_equation_of_core_det_zero` connects the actual substituted
rank-three logarithmic core to the autonomous fraction equation without
assuming the target denominator is nonzero.

## Remaining rank-three bridge after a green Phase 83

1. choose / construct reduced source and target fraction presentations;
2. instantiate the Phase 82 denominator-removal theorem;
3. transport the resulting polynomial target into Phase 79/77;
4. formalise the three explicit infinity cases of Theorem 4.2 and dispatch
   them into the already-verified pencil terminal cases;
5. assemble the complete rank-three edge rigidity theorem.
