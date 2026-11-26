# Current proof state — 26 November 2026

**JC2 ↔ HC4 in the polynomial-inverse formulation: Lean verified.** The public endpoint is [`HC4.StatementAudit.jc2_iff_hc4_explicit`](../HC4/FinalEquivalence.lean), over algebraically closed characteristic-zero fields. On 26 November 2026 the maintainer reported a successful local audit of all five final equivalence declarations with exactly the standard three foundational axioms. Independent fresh-checkout reproduction [passed](https://github.com/JamieLittle16/HessianConjecture4/actions/runs/45855370863) at commit `1377de42` (8358 jobs, 55m 4s), with only the three foundational axioms and rejection of a false equality.

**Conditional HC4: Lean verified.** The maintained endpoint is [`HC4.Polynomial.hc4_of_planarJC2`](../HC4/Polynomial/RankThreeOneVariableKernel.lean), with no additional extraction or producer assumptions.

| Target | Status |
|---|---|
| PlanarJC2Injectivity K → determinant-one Hessian gradient injectivity in four variables | Verified |
| Unconditional HC4 | Open in this project |
| Planar JC2 | Assumed, not proved |
| Nonzero constant Hessian determinant and two-sided polynomial inverse equivalence | Verified over algebraically closed characteristic-zero fields |
| Generic injective polynomial map implies polynomial inverse | Verified over algebraically closed characteristic-zero fields |
| Checked declaration dependency and baseline provenance export | Completed (125 defining modules; 1,446 reachable local declarations) |
| Mathematical priority and attribution | Preliminary audit completed; detailed literature comparison pending |
| Clean-host equivalence reproduction | Passed; later standalone extraction separately locally verified |

The exact verification checkpoint is [38e58bf4](https://github.com/JamieLittle16/HessianConjecture4/commit/38e58bf49cbd91ce9ae2d4e18b7d64e33fe02c8c), merged through [PR #64](https://github.com/JamieLittle16/HessianConjecture4/pull/64). Maintainer local full build: 9051 jobs successful. The explicit gradient example in [Audit.lean](../HC4/Audit.lean) passed, with final transitive axioms exactly `[propext, Classical.choice, Quot.sound]`.

See the [proof and contribution audit](PROOF_AND_CONTRIBUTION_AUDIT.md) for the consolidated proof architecture, source provenance and attribution.

The proof uses the global weighted extremal counterexample, rank exclusion, complementary Hessian and rational kernel rigidity, followed by Taylor normalization and a signed first-wall contradiction. See [PROOF_PATHS.md](PROOF_PATHS.md).

The previous valuation/Smith/Rees extraction route and transverse-cap investigations remain research history, not remaining obligations of this conditional theorem. Their prior status is preserved in the [25 November checkpoint](https://github.com/JamieLittle16/HessianConjecture4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/CURRENT_STATE.md). Do not treat their partial endpoints as unconditional global theorems.

## Standalone rational affine-plane rigidity

The general all-rank theorem [`rationalMap_affinePlane`](../HC4/Polynomial/RationalMapAffinePlane.lean) is verified by the maintainer's targeted build (8317 jobs, 26 November 2026, commit [9e548ccb](https://github.com/JamieLittle16/HessianConjecture4/commit/9e548ccbd91920cb7f49ba40c2bf93e11e996b14)) with the standard three foundational axioms. It requires only a rational three-variable map with cube-zero Jacobian and a nonsingular polynomial Hessian symmetrizer over a characteristic-zero field. See the [mathematical note](research/rational-affine-plane-rigidity.tex). It is not an additional hypothesis of HC4, and does not change the original final proof.
