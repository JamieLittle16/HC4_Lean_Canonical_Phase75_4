# Manuscript review record — 26 November 2026

The consolidated draft is [hc4-jc2-manuscript.tex](hc4-jc2-manuscript.tex). This is a review checkpoint, not a publication certificate.

## Formal statement and major-interface comparison

The following declarations were reopened at the current master branch and their hypotheses and conclusions compared to the manuscript. Names below are abbreviated where the module already identifies the namespace.

| Manuscript stage | Formal source / declaration | Scope checked |
|---|---|---|
| Same-field injectivity equivalence | `HC4/StatementAudit.lean`: `planarJC2_iff_hessianFour_injective` | Characteristic zero; planar nonzero constant determinant; four-variable literal determinant one. |
| Full polynomial-inverse equivalence | `HC4/FinalEquivalence.lean`: `jc2_iff_hc4_explicit` | Algebraically closed characteristic-zero field; determinant a polynomial-ring unit; both composition identities, both conjectures universally quantified. |
| Standalone rational rigidity | `HC4/Polynomial/RationalMapAffinePlane.lean`: `rationalMap_affinePlane` | Rational map in three variables, cube-zero Jacobian, nonsingular polynomial Hessian symmetrizer, nonzero constant affine relation. No planar hypothesis. |
| Anchored characteristic | `HC4/Polynomial/RankThreeCubicCharacteristics.lean`: `exists_anchored_lineEval_gradient_eq` | Singular Hessian; actual nonsingular principal minor at the chosen point; normalized direction and exact polynomial gradient line identity. |
| Global maximum | `HC4/Polynomial/WeightedGlobalOptimum.lean`: `exists_global_integralWeightOptimum` | Actual determinant-one chart, nonnegative integral weights, positive cap, nonnegative determinant weight; maximum over all such charts and caps. |
| Zero determinant weight | `HC4/Polynomial/NonnegativeTerminalAssembly.lean`: `gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2` | Full-source cap, nonnegative weights, determinant one, planar assumption. |
| Rank at most two excluded | `HC4/Polynomial/RankTwoGlobalClosure.lean`: `globalWeightOptimum_not_rankAtMostTwo` | Positive determinant weight, global optimality, determinant one; actual leading Hessian does not have all third-order minors zero. |
| Complementary chart | `HC4/Polynomial/RankThreeExtremalReduction.lean`: `counterexample_exists_rankThree_complementary_chart` | Actual counterexample and planar assumption yield a zero adjugate column and **one** surviving principal cofactor at a distinct coordinate; full-source cap, collision, determinant and optimality preserved. |
| Relative frontier | `HC4/Polynomial/RankThreeOneVariableKernel.lean`: `counterexample_rankThree_zeroWeight_relative_frontier` | Same counterexample hypotheses and normalized rational kernel; active weight zero, equal passive weights, nonzero passive diagonals, restricted minors zero, passive derivatives of the kernel zero. |
| Signed-wall rigidity | Same module: `rankThree_signedWall_restrictedMinors_zero` | Pairwise distinct signed integral weights, homogeneous polynomial, singular Hessian, all three passive principal cofactors nonzero. No nonnegative global-optimum assumption. |
| Signed first contact | Same module: `rankThree_normalizedWall_impossible`, `rankThree_clearedPhase_normalize_impossible` | Actual full source; nonzero constant determinant, relative cap, top slope cap, low-degree constraint and surviving cofactors; cleared rational phase normalization. |
| Reverse implication | `HC4/PlanarJC2HessianEmbedding.lean`: `planarJC2_of_hessianFour_gradient_injective` | Planar target normalization followed by the four-variable doubling potential. |
| Polynomial inverse bridge | `HC4/RationalInverseAudit.lean`: `polynomial_inverse_of_injective_eval` | Algebraically closed characteristic-zero field; injectivity on points; two polynomial substitution identities. |

The draft uses a shared polynomial transport lemma, expands the anchored characteristic construction and reverse implication, and reconstructs the generic polynomial-inverse argument using the same classical ingredients as Lean. Some mathematical steps are rearranged from the dependency graph; this interface comparison is **not** a completed independent line-by-line proof review.

## Verification and remaining checks

- Maintainer-reported core, final equivalence and standalone rigidity builds and axiom reports have passed (see the [contribution audit](../PROOF_AND_CONTRIBUTION_AUDIT.md)).
- The separate rational-rigidity, global-weight and rank-exclusion notes have each compiled locally. The final rank-exclusion revision at commit 57ad636f compiled cleanly in two passes (7 pages). The consolidated manuscript is a new source.
- Structural validation of the consolidated draft passed (balanced LaTeX environments, distinct labels, all internal references present). The maintainer confirmed successful local compilation of the merged manuscript on 26 November 2026, following the revision at dca672e6. The supplied log confirms two successful pdfTeX passes at checkout e6a4d3ba: 18 pages, 303120 bytes on the second pass, all references resolved. Eight overfull boxes remained in the source guide, reproduction and bibliography; commit 98b377e3 adjusts these line breaks. Recompilation of that revision and visual review remain outstanding.
- Independent clean reproduction is in progress according to the maintainer; do not mark it complete until a successful output and exact tested commit are recorded.
- Independent mathematical review is still outstanding, particularly the informal coefficient-transfer and Taylor normalization arguments, the Lüroth specialization argument, and the correspondence of the reorganized exposition to the checked proofs. Check citations against the original papers before submission.
- The author field is a project-level placeholder. Author attribution and disclosure wording should be settled by the maintainer before publication. Tang's theorem and influence are acknowledged; no priority claim is made.
- Manuscript compilation has been confirmed. Contact Tang after the clean reproduction evidence is available. Present this as a formalisation and algebraic adaptation of his result, and request his mathematical feedback, rather than asserting an independently discovered equivalence.
