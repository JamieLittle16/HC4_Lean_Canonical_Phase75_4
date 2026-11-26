# Publication and research next steps

The conditional theorem is verified at 38e58bf4 (26 November 2026). The subsequent [full polynomial-inverse equivalence](../HC4/FinalEquivalence.lean) also passed the maintainer's local audit on 26 November 2026. Preserve this proof checkpoint and its full history; do not change the Lean implementation merely to improve presentation.

## Publication preparation

1. Reproduce the audit on a fresh checkout using the pinned toolchain and dependencies, and record the exact commit and result.
2. The declaration dependency and dated module-provenance exports are complete; see [the audit](PROOF_AND_CONTRIBUTION_AUDIT.md). Record the standalone build result and source footprint, keeping historical work intact.
3. Extend the preliminary Tang comparison in the audit to a full lemma-level and prior-literature review. The standalone all-rank theorem is verified and its [LaTeX exposition](research/rational-affine-plane-rigidity.tex) is available; review that exposition independently and compare it to Tang's Theorem 2.1 and prior literature. Do not claim priority or mathematical independence prematurely.
4. Draft a manuscript with the exact conditional theorem, definitions, global extremal reduction, rank exclusions, rational rigidity, Taylor normalization, signed first wall, and Lean verification details. Include transparent attribution and limitations.
5. Arrange independent mathematical and Lean review before making publication or novelty claims.

## Further mathematics

Unconditional HC4 and planar JC2 are not established here. The polynomial inverse and nonzero constant Hessian determinant extensions have now been verified over algebraically closed characteristic-zero fields. The outstanding work is independent reproduction, mathematical exposition and review, not another obligation for the stated equivalence. Earlier research routes remain available for further work but are not gaps in the conditional theorem.

The [previous research plan](https://github.com/JamieLittle16/HessianConjecture4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/NEXT_STEPS.md) is historical.

The [global extremal-weight note](research/global-extremal-weight.tex) is now drafted alongside the rational rigidity note. The [supporting rank-exclusion note](research/extremal-rank-exclusions.tex) now expands the nonnegative rank-two and rank-three exclusions. Compile and independently review all three notes, then expand the distinct-weight signed-wall pivot argument before treating the exposition as a self-contained proof of the equivalence.
