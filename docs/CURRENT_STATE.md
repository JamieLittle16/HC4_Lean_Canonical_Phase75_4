# Current proof state — 26 November 2026

**Conditional HC4: Lean verified.** The maintained endpoint is [`HC4.Polynomial.hc4_of_planarJC2`](../HC4/Polynomial/RankThreeOneVariableKernel.lean), with no additional extraction or producer assumptions.

| Target | Status |
|---|---|
| PlanarJC2Injectivity K → determinant-one Hessian gradient injectivity in four variables | Verified |
| Unconditional HC4 | Open in this project |
| Planar JC2 | Assumed, not proved |
| Polynomial inverse conclusion | Not part of the final declaration |
| Mathematical priority and attribution | Publication audit pending |

The exact verification checkpoint is [38e58bf4](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/commit/38e58bf49cbd91ce9ae2d4e18b7d64e33fe02c8c), merged through [PR #64](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/pull/64). Maintainer local full build: 9051 jobs successful. The explicit gradient example in [Audit.lean](../HC4/Audit.lean) passed, with final transitive axioms exactly `[propext, Classical.choice, Quot.sound]`.

The proof uses the global weighted extremal counterexample, rank exclusion, complementary Hessian and rational kernel rigidity, followed by Taylor normalization and a signed first-wall contradiction. See [PROOF_PATHS.md](PROOF_PATHS.md).

The previous valuation/Smith/Rees extraction route and transverse-cap investigations remain research history, not remaining obligations of this conditional theorem. Their prior status is preserved in the [25 November checkpoint](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/CURRENT_STATE.md). Do not treat their partial endpoints as unconditional global theorems.
