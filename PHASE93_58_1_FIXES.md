# Phase 93.58.1 — Classical candidate-set / witness fixes

The first Phase 93.58 build exposed four implementation issues only.

1. `IsActiveKernelCoordinate` elaborates as
   `∃ d, d ∈ support ∧ 0 < d kernel`, so after choosing `d` the positivity
   proof is `.2`, not `.2.2`.

2. `Finset.filter` needs a decidable predicate.  The admissibility predicate
   contains polynomial divisibility and has no constructive
   `DecidablePred` instance.  Since the slope selection is already declared
   `noncomputable`, `integralKernelSlopeCandidates` now uses an explicit
   `by classical` definition body.

3. Candidate membership is unpacked/repacked through direct `simp` on the
   definition, avoiding ambiguous elaboration of `Finset.mem_filter`.

4. In the zero-slope identity theorem, `hzero` is an equality of an
   expression with zero, not a variable equality suitable for `subst`.
   The proof now constructs the universally valid slope-zero divisibility
   witness and uses `simpa only [hzero]` with the green zero-identity theorem.

No theorem statement or mathematical content is changed.
