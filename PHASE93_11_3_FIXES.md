# Phase 93.11.3 — explicit additive-map support decomposition

Affected file:

    HC4/Newton/ExactCollisionFirstWall.lean

The remaining Phase 93.11.2 goal was exactly the linearity statement

    eval point (pderiv i (support.sum monomial))
      =
    support.sum (fun d => eval point (pderiv i (monomial d ...))).

The previous proof delegated this to `simp`.  On the pinned Mathlib build,
the simplifier did not choose the required finite-sum map lemmas.

The repair now invokes the generic `map_sum` theorem explicitly twice:

1. for `MvPolynomial.pderiv i`, viewed as an additive map;
2. for `MvPolynomial.eval point`, viewed as a ring hom and hence an
   additive map.

After these two rewrites, the goal is definitionally equal to the
`gradientMonomialContributionAt` support sum and closes by `rfl`.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
