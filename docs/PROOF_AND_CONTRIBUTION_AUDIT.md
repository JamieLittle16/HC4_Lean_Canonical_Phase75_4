# Proof, verification and contribution audit

**26 November 2026 — preliminary scholarly account of the completed formalisation.**

This report records the result actually checked by Lean, the mathematical route used to prove it, and the evidence available about the origins of that route. It is intended as a review guide, not a priority claim or a replacement for a full mathematical manuscript.

## 1. Result and scope

Let K be an algebraically closed field of characteristic zero. Write JC2(K) for the assertion that every polynomial map K² → K² with nonzero constant Jacobian determinant has a two-sided polynomial inverse. Write HC4(K) for the corresponding assertion for gradients of arbitrary polynomials in four variables.

The verified equivalence is JC2(K) ↔ HC4(K).

```lean
theorem HC4.StatementAudit.referenceJC2_iff_referenceHC4
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    HC4.StatementAudit.ReferenceJC K 2 ↔ HC4.StatementAudit.ReferenceHC4 K
```

The public theorem [jc2_iff_hc4_explicit](../HC4/FinalEquivalence.lean) expands both conjectures using multivariate polynomial partial derivatives, matrix determinants and two-sided substitution identities. It allows arbitrary degrees and any unit Hessian determinant, not just determinant one.

The hard direction rests on the following more general same-field injectivity implication, which does not require algebraic closure:

```lean
theorem HC4.Polynomial.hc4_of_planarJC2
    {K : Type*} [Field K] [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant P = 1) :
    Function.Injective (HC4.Newton.mvGradientMap P)
```

Its only conjectural premise is the planar injectivity hypothesis. Neither conjecture is asserted unconditionally. The two-sided polynomial-inverse equivalence is stated over algebraically closed characteristic-zero fields, not all characteristic-zero fields.

The planar statement was cross-checked with the conventions in [Google DeepMind's Formal Conjectures, pinned reference](https://github.com/google-deepmind/formal-conjectures/blob/a88aee564684360292318c61b9b8e27febef2ae0/FormalConjectures/Wikipedia/JacobianConjecture.lean). [StatementAudit](../HC4/StatementAudit.lean) checks the determinant, transpose, unit and evaluation conventions. It uses a local predicate with the composition equations expanded, not an import of an unresolved conjecture from that repository.

## 2. Mathematical proof architecture

The following is an outline of the actual proof of the hard direction, not an alternative informal proof. The declaration signatures govern the precise hypotheses.

| Stage | Main declaration / source | Mathematical role |
|---|---|---|
| Planar doubling (reverse implication) | [PlanarJC2HessianEmbedding](../HC4/PlanarJC2HessianEmbedding.lean), `planarJC2_of_hessianFour_gradient_injective` | Normalize a planar Keller map and realize its collision as a gradient collision of a four-variable doubled potential. |
| Attainment of a global optimum | [WeightedGlobalOptimum](../HC4/Polynomial/WeightedGlobalOptimum.lean), `exists_global_integralWeightOptimum` | Optimize normalized weights across actual determinant-one linear charts, using finite support patterns and rational linear constraints. |
| Zero determinant weight | [NonnegativeTerminalAssembly](../HC4/Polynomial/NonnegativeTerminalAssembly.lean), `gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2` | Split the zero-clock terminal into positive, one-zero and two-zero weight cases; reduce the last to planar injectivity. |
| Singular leading Hessian | [RankThreeExtremalReduction](../HC4/Polynomial/RankThreeExtremalReduction.lean), `counterexample_exists_rankThree_complementary_chart` | At positive determinant weight, rule out rank at most two using the weighted extremal analysis and obtain a rank-three chart with a surviving principal cofactor and constant adjugate annihilator. |
| Anchored rational rigidity | [RationalCharacteristicRankOneClosure](../HC4/Polynomial/RationalCharacteristicRankOneClosure.lean), [RationalCharacteristicRankTwoClosure](../HC4/Polynomial/RationalCharacteristicRankTwoClosure.lean), `rationalCharacteristic_anchored_adjugate_annihilator` | Use the anchored characteristic and its nilpotent Jacobian; handle rank at most one and rank two to obtain a constant adjugate annihilator. |
| Remove the distinguished anchor | [SingularHessianConstantAnnihilator](../HC4/Polynomial/SingularHessianConstantAnnihilator.lean), `singularHessian_exists_constant_adjugate_annihilator` | Move a surviving principal cofactor into the distinguished coordinate and transport the annihilator back. The adjugate-zero case is immediate. |
| Relative rank-three normal form | [RankThreeOneVariableKernel](../HC4/Polynomial/RankThreeOneVariableKernel.lean), `counterexample_rankThree_zeroWeight_relative_frontier`, `rankThree_relativePurePower` | Obtain an active zero-weight coordinate, equal passive weights and the relative rank-one form; use relative Euler identities and gradient ratios to isolate a pure power. |
| Wronskian / Taylor normalization | Same file, `globalWeightOptimum_rankThree_relativeWronskian`, `rankThree_clearedPhase_normalize_impossible` | Exclude affine dependence, clear denominators, choose a regular ground-field point and normalize the three passive coefficients via a second-order jet matrix. |
| Signed first-wall obstruction | Same file, `rankThree_normalizedWall_impossible`, `globalWeightOptimum_rankThree_zeroWeight_impossible` | Control the lower-degree first contact and passive cofactors of the normalized leading phase, contradicting the nonzero constant Hessian determinant. |
| Final assembly | Same file, `hc4_of_planarJC2` | Eliminate the alleged collision. |
| Polynomial inverse conclusion | [PolynomialInverseAudit](../HC4/PolynomialInverseAudit.lean), [RationalInverseAudit](../HC4/RationalInverseAudit.lean), [FinalEquivalence](../HC4/FinalEquivalence.lean) | Use the Nullstellensatz, fraction-field/separable-degree arguments, Ax–Grothendieck and reduced-coordinate denominator cancellation to obtain both polynomial composition identities. Normalize nonzero constant Hessian determinants over algebraically closed fields. |

For the optimum, if the cap is normalized to one, the objective is to maximize the sum of nonnegative rational weights, bounded by two, subject to each supported exponent having weight at most one, across determinant-one linear substitutions. The integral version clears denominators. The determinant weight is then 4m − 2∑wᵢ. This is a global extremal organization, not an assertion that any one local wall continuation is sufficient.

For the constant annihilator, the conclusion is a nonzero constant vector d with adj(H)d = 0, not H d = 0. This distinction is important for nonhomogeneous singular Hessians. The anchored result uses an actual polynomial source with a regular transverse Hessian block; the anchor is subsequently removed. No general unrestricted rational-map classification is asserted by this report.

## 3. Verification evidence

The maintainer reported:

- 26 November: core full library build at [38e58bf4](https://github.com/JamieLittle16/HessianConjecture4/commit/38e58bf49cbd91ce9ae2d4e18b7d64e33fe02c8c), 9,051 jobs; explicit gradient audit passed.
- 26 November: final equivalence introduced at [7fdbfcea](https://github.com/JamieLittle16/HessianConjecture4/commit/7fdbfceae27addbf28928668678c62e18fc0fce8); all five printed final declarations passed with exactly the foundational axioms listed below. The later integrated verification script also completed locally.
- 26 November: successful checked-environment export following [2a020f46](https://github.com/JamieLittle16/HessianConjecture4/commit/2a020f463b737270e97c7d9d0919428ce035a636); module provenance export at [513028fb](https://github.com/JamieLittle16/HessianConjecture4/commit/513028fbbe1d38d9d8c891d85ee01789b1555835).

The final proof's transitive axioms are:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, Tang theorem axiom, planar conjecture axiom or additional mathematical axiom occurs in the audited final dependency closure. The equivalence is a theorem about the two conjectural propositions. The local Lean version is pinned by `lean-toolchain` (v4.24.0) and the dependency revisions by `lake-manifest.json`.

**Fresh-host reproduction:** the [clean reproduction workflow](../.github/workflows/clean-reproduction.yml) was reported running on 26 November. Its result is not yet recorded. It disables the project build cache, permits the pinned Mathlib dependency cache, rebuilds the final entry point, checks the axiom whitelist and rejects a deliberately false equality. The separately staged standalone build is also reported in progress; its outcome and exact source footprint are not yet certified. Neither is a substitute for external mathematical review.

## 4. Declaration dependency audit

These counts are from the maintainer's successful local export, not the much larger textual module inventory. The traversal follows constant references in checked declaration types and values, including opaque proofs and inductive constructors, in the style of Lean's axiom collector. The exported local graphs retain generated and private declarations and edges between local endpoints.

| Metric | Core implication | Full equivalence |
|---|---:|---:|
| Reachable declarations, all libraries | 31,807 | 36,528 |
| HC4-owned declarations | 1,393 | 1,446 |
| Theorem-kind HC4 declarations | 1,078 | 1,125 |
| Definition-kind HC4 declarations | 313 | 319 |
| HC4 defining modules | 119 | 125 |
| Local typed edges | 7,483 | 7,803 |
| Source modules with no reachable declaration | 1,835 | 1,829 |
| Reachable nonstandard axioms | 0 | 0 |

The full export reported 1,193,920 typed edges for the two roots together. Of 1,954 source modules counted, 125 (6.4%) own declarations reachable from the final equivalence. This does not mean that the other 1,829 files can be deleted: elaboration, notation, instances, tactics and transitive imports may need additional source files. The standalone build must be validated separately.

The largest owners include RankThreeOneVariableKernel (227), RatFuncLuroth (88), RankOneHessianRatioRigidity (36), RatFuncIntermediateField (34), RankThreeCubicCharacteristics (34), PlanarJC2HessianEmbedding (22), and WeightedExtremalAffinePlane (22).

Reproduce the diagnostics on the same proof snapshot:

```bash
lake build HC4.FinalEquivalence
lake env lean tools/ExportProofDependencies.lean
python3 tools/summarise_proof_dependencies.py
python3 tools/module_provenance.py
python3 tools/publication_footprint.py
```

The results are written under `proof-dependencies/`. The source-import footprint script is a diagnostic, not a proof of minimality. The figures above describe the reported snapshot, not all future revisions of the repository.

## 5. Historical provenance of the reachable source

The comparison baseline is [90b9d97e](https://github.com/JamieLittle16/HessianConjecture4/commit/90b9d97e2937b34c12c2ab845a404048f4a3c4b1), dated 25 November 2026 at 20:36:48 UTC. It is the repository checkpoint selected before the project's recorded discussion of Tang's paper. It is not a cutoff for publication priority; Tang's preprint was already public in November.

The provenance audit compares source blobs at that checkpoint and at the reported HEAD, and records first recorded addition dates. All 39 earlier reachable module files have identical blobs at the two snapshots.

| First recorded addition period | Modules | Reachable declarations |
|---|---:|---:|
| August 2026 | 30 | 183 |
| 20–23 November | 9 | 64 |
| 25 November | 46 | 579 |
| 26 November | 40 | 620 |
| Total | 125 | 1,446 |

| Baseline classification | Modules | Reachable declarations |
|---|---:|---:|
| Present and unchanged | 39 | 247 |
| Present but modified | 0 | 0 |
| Absent | 86 | 1,199 |

Thus 17.1% of the final local reachable declarations reside in unchanged pre-discussion files. For the core implication alone, 221 of 1,393 are in those files. In the induced HC4-only graph rooted at the zero-clock terminal theorem, 151 of 202 reachable declarations (74.8%) are from unchanged baseline files. These last counts exclude possible paths through external-library vertices.

This shows substantive reuse of the earlier terminal and cubic-characteristic infrastructure. It does **not** measure mathematical originality: commit timestamps and dependency counts do not establish when an idea was discovered, whether it was known in the literature, how difficult it is, or how much is attributable to any particular researcher.

Selected dated evidence:

- [20 November: cubic fibre pencils](https://github.com/JamieLittle16/HessianConjecture4/commit/c925bd02b946278c0fa74ab72ff539b8f9cf07b2).
- [20 November: straight cubic characteristics](https://github.com/JamieLittle16/HessianConjecture4/commit/e5aec736cf33bf00fbfc54d92c0827af4a2b82a5).
- [24 November: arbitrary-degree characteristic classification](https://github.com/JamieLittle16/HessianConjecture4/commit/ff7b34b1cf).
- [25 November: rational characteristic transport](https://github.com/JamieLittle16/HessianConjecture4/commit/10d2502f8c56a1e3bd157165e0ad08142a62319e).
- [26 November: rank-one Hessian ratio rigidity](https://github.com/JamieLittle16/HessianConjecture4/commit/129e0a526074f27ba653f1349f58349859116bbb).
- [26 November: explicit Tang attribution](https://github.com/JamieLittle16/HessianConjecture4/commit/517bed9c34859c7a148c2097ed452dbbc97ab66b).

## 6. Attribution and comparison with the literature

**Qiyue Tang**, *Equivalence of the Four-Variable Hessian and Planar Jacobian Conjectures*, [Hexagon preprint 2611.00156v2](https://hexagonmath.org/2611.00156v2), 2026, CC BY 4.0 ([PDF](https://hexagonmath.org/pdf/2611.00156v2)). The completed route was substantially informed by this preprint. Its equivalence over C is part of Theorem 1.1; the present project does not claim independent discovery of that equivalence or priority over Tang.

The following comparison is preliminary and should guide a full lemma-by-lemma review.

| Component | Relationship / attribution |
|---|---|
| Doubling | Standard construction; Tang Lemma 1.2. Our implementation and terminal planarisation infrastructure were developed earlier. |
| Rank-one rational characteristic | Substantial overlap with Tang Theorem 2.1, including the one-parameter/Lüroth reduction, polynomial-pencil and affine-coordinate arguments. The project supplies checked algebraic versions. |
| Rank-two rational characteristic | Tang Theorem 2.1 invokes geometry of line congruences, including De Poi's classification. Our anchored source argument instead uses fraction-field derivations, straight-fibre polynomial identities and normal/parameter rigidity. The source-level conclusion is checked; whether the argument yields all of Tang's more general theorem, or is new in the literature, has not been established. |
| Singular Hessian | The constant adjugate annihilator is an algebraic route to the constraint needed for the weighted proof, related to Tang Theorem 2.3 and de Bondt's translation-direction question. Do not identify an annihilator of the adjugate with a constant kernel vector of the Hessian. |
| Weighted reduction | The global optimization over linear charts is a different organization from the sequence of leading-form transitions in Tang Sections 3–4, while sharing the weighted strategy. A detailed comparison is needed before any originality claim. |
| Final rank-three obstruction | Direct adaptation of the Wronskian/second-order Taylor normalization and signed first wall in Tang Lemma 3.3, especially pp. 17–18. |
| Polynomial inverse and explicit statement | Separate formal bridge using standard algebraic results, with a statement audit against the polynomial-map conventions of Formal Conjectures. |

In particular, Tang's Theorem 1.1 contains a structural alternative for noninvertible potentials: after a linear change, the potential is jointly affine in two fibre variables over a two-variable base. Our final public equivalence does not explicitly assert this stronger classification. The same-field characteristic-zero injectivity theorem and the algebraically closed field equivalence have the scopes stated in Section 1; neither statement should be substituted silently for Tang's full theorem.

The rank-two algebraic route is a candidate for a standalone exposition. Its main pieces are [straight direction](../HC4/Polynomial/RationalCharacteristicRankTwoStraightFibre.lean), [affine gradient](../HC4/Polynomial/RationalCharacteristicRankTwoAffineGradient.lean), [variable direction closure](../HC4/Polynomial/RationalCharacteristicRankTwoVariableClosure.lean), and [constant direction / final closure](../HC4/Polynomial/RationalCharacteristicRankTwoClosure.lean). These are evidence of a difference in formal proof strategy, not a proven new mathematical result beyond existing literature.

### Mathlib and other dependencies

122 reachable local declarations belong to the two vendored Mathlib modules, not to a wholly original project proof:

- [RatFuncLuroth](../HC4/Backport/RatFuncLuroth.lean) (88 declarations), upstream [348837d3](https://github.com/leanprover-community/mathlib4/blob/348837d3aa976624060d7c35c183fff587c5a24a/Mathlib/FieldTheory/RatFunc/Luroth.lean).
- [RatFuncIntermediateField](../HC4/Backport/RatFuncIntermediateField.lean) (34), upstream [b66958d5](https://github.com/leanprover-community/mathlib4/blob/b66958d58522a5c643c456fa6349c2043968db80/Mathlib/FieldTheory/RatFunc/Luroth.lean), with a later lemma from the split version.

Both files retain the Apache-2.0 copyright and authorship notices for Miriam Philipp, Justus Springer and Junyan Xu and document compatibility modifications. The underlying Lüroth theorem is classical. The broader proof also depends on Mathlib, Lean's foundational library and its ordinary classical axioms.

Relevant prior literature to audit includes M. de Bondt, *Polynomial Hessians with small rank*, [arXiv:1609.03904](https://arxiv.org/abs/1609.03904), and *Quasi-translations and singular Hessians*, Colloq. Math. 152 (2018), as well as P. De Poi, *Congruences of lines with one-dimensional focal locus*, Port. Math. 61 (2004). These references are identified via Tang's bibliography; a full comparison against their results is pending.

### AI-assisted development

The project has been developed with substantial AI assistance in mathematical exploration, Lean proof construction and debugging, alongside maintainer-run verification. Tang's own preprint record separately documents AI-assisted research and review. A manuscript should describe both workflows transparently and distinguish machine-checked proof validity from independent human understanding, attribution and priority.

## 7. Remaining publication tasks

1. Record the successful fresh-host workflow run, exact commit, log artifact and axiom output when available.
2. Verify the separately staged standalone source library, record its file count and build, and preserve the full historical research repository.
3. Write a human-readable, source-linked exposition of the anchored rank-one/rank-two rigidity proof, followed by the global weight argument and final obstruction.
4. Complete the lemma-level comparison against Tang and the earlier literature, including the precise difference in theorem scope. Review backport license and attribution requirements.
5. Invite Tang and independent Lean/mathematical reviewers to check the result. Do not assert first formalisation priority or new mathematical results without supporting evidence.

The mathematical equivalence has been locally verified. The open items here concern reproducibility, exposition, review and provenance, not an additional conjectural premise of the stated Lean theorem.
