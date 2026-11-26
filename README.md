# Hessian Conjecture in Dimension Four

A Lean 4 formalisation of the equivalence of the planar Jacobian conjecture and the four-variable Hessian conjecture, together with supporting algebraic research.

## Verified polynomial-inverse equivalence

For every algebraically closed field K of characteristic zero, JC2(K) is equivalent to HC4(K): both conjectures assert that the relevant polynomial maps with nonzero constant Jacobian determinant possess a two-sided polynomial inverse. On the Hessian side the maps are formal gradients of arbitrary four-variable polynomials.

```lean
theorem HC4.StatementAudit.referenceJC2_iff_referenceHC4
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    HC4.StatementAudit.ReferenceJC K 2 ↔ HC4.StatementAudit.ReferenceHC4 K
```

See [FinalEquivalence.lean](HC4/FinalEquivalence.lean) for `HC4.StatementAudit.jc2_iff_hc4_explicit`, which expands both predicates directly using partial derivatives, matrix determinants, and polynomial substitution. The maintainer reported successful local verification on 26 November 2026 of this module (introduced in [`7fdbfcea`](https://github.com/JamieLittle16/HessianConjecture4/commit/7fdbfceae27addbf28928668678c62e18fc0fce8)), with all five printed declarations depending only on `[propext, Classical.choice, Quot.sound]`. Independent fresh-checkout reproduction of the final equivalence [passed](https://github.com/JamieLittle16/HessianConjecture4/actions/runs/45855370863) on 26 November 2026 (8358 jobs, 55m 4s, commit `1377de42`), including the final axiom audit and rejection of a false equality. No existing Lean proof source changed between that checkpoint and the manuscript checkpoint. The later standalone rigidity extraction was verified locally, not by this run.

The planar statement follows the polynomial inverse conventions of Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/a88aee564684360292318c61b9b8e27febef2ae0/FormalConjectures/Wikipedia/JacobianConjecture.lean), with its composition equations expanded in [StatementAudit.lean](HC4/StatementAudit.lean). No open conjecture declaration from that project is imported. [PolynomialInverseAudit.lean](HC4/PolynomialInverseAudit.lean) and [RationalInverseAudit.lean](HC4/RationalInverseAudit.lean) prove the generic polynomial-inverse bridge using Mathlib's Nullstellensatz, Ax–Grothendieck and separable degree.

Neither JC2 nor HC4 is proved unconditionally.

## Verified conditional theorem

Let K be any field of characteristic zero. Assume every planar polynomial map over K with nonzero constant Jacobian determinant is injective. Then every polynomial P in four variables with det Hess(P) = 1 has an injective gradient.

```lean
theorem HC4.Polynomial.hc4_of_planarJC2
    {K : Type*} [Field K] [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant P = 1) :
    Function.Injective (HC4.Newton.mvGradientMap P)
```

The declaration lives in [RankThreeOneVariableKernel.lean](HC4/Polynomial/RankThreeOneVariableKernel.lean). The assumption is defined in [PlanarJC2Interface.lean](HC4/PlanarJC2Interface.lean); [Audit.lean](HC4/Audit.lean) also checks the explicitly evaluated gradient signature.

Maintainer verification, 26 November 2026, at [`38e58bf4`](https://github.com/JamieLittle16/HessianConjecture4/commit/38e58bf49cbd91ce9ae2d4e18b7d64e33fe02c8c): full `lake build` completed (9051 jobs); `lake env lean HC4/Audit.lean` passed with final transitive axioms `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or additional axioms in the final theorem.

**Scope:** this stronger same-field injectivity implication needs no algebraic-closure hypothesis. The polynomial-inverse equivalence above is stated over algebraically closed characteristic-zero fields. See the attribution below and the preliminary proof and contribution audit; detailed mathematical priority analysis remains outstanding.

## Standalone rational rigidity theorem

The project also proves a source-independent algebraic version of Tang's Theorem 2.1: for any characteristic-zero field K, a rational three-variable map v with nilpotent Jacobian N and a nonsingular polynomial Hessian H satisfying NᵀH = HN has a nonzero constant affine relation on its components. This covers every rank and does not assume planar JC2 or a four-variable source.

The declaration [`rationalMap_affinePlane`](HC4/Polynomial/RationalMapAffinePlane.lean) passed the maintainer's targeted build (8317 jobs, 26 November 2026, [9e548ccb](https://github.com/JamieLittle16/HessianConjecture4/commit/9e548ccbd91920cb7f49ba40c2bf93e11e996b14)); its transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. The [mathematical exposition (LaTeX)](docs/research/rational-affine-plane-rigidity.tex) explains all ranks, including the polynomial transport argument replacing the rank-two geometric classification. The new endpoint is separate from the original equivalence proof.

## Consolidated manuscript (review draft)

The [unified LaTeX manuscript](docs/research/hc4-jc2-manuscript.tex) consolidates the mathematical notes, including the anchored characteristic construction, rank exclusions, signed-wall contradiction, reverse doubling implication and polynomial-inverse bridge. See its [review record](docs/research/MANUSCRIPT_REVIEW.md) for formal interface checks and outstanding validation. The author-identified manuscript compiled successfully in two passes on 26 November 2026 (19 pages); external mathematical review remains pending.

## Global extremal-weight exposition

The [companion LaTeX note](docs/research/global-extremal-weight.tex) explains attainment over realized support patterns, local weight-improvement obstructions, the checked rank reductions and the final signed first-wall argument adapted from Tang. It is a source-linked proof outline; the longer rank-reduction lemmas are summarized rather than fully reproved. The [supporting rank-exclusion note](docs/research/extremal-rank-exclusions.tex) expands the constant-image obstruction, affine kernel graphs, isotropic-slope root evaluation, relative frontier and distinct-weight signed-wall rigidity. These notes complement the standalone rational rigidity note above.

## Mathematical attribution

The final weighted proof was substantially informed by Qiyue Tang, *[Equivalence of the Four-Variable Hessian and Planar Jacobian Conjectures](https://hexagonmath.org/2611.00156v2)*, Hexagon preprint 2611.00156v2 (2026), CC BY 4.0. Tang's preprint presents the equivalence over the complex numbers (Theorem 1.1). In particular, we adapted the Wronskian/Taylor coordinate normalization and signed first-wall obstruction in Lemma 3.3 (pp. 17–18), as well as drawing on the broader weighted leading-form strategy.

The project predates this preprint, but its earlier investigations and the completed proof should not be conflated with an independent discovery of the final implication. The contribution documented here is a Lean 4 formalisation and algebraic adaptation, including the precise same-field injectivity statement over arbitrary characteristic-zero fields. The final Lean proof does not assume Tang's theorem as an axiom. The [proof and contribution audit](docs/PROOF_AND_CONTRIBUTION_AUDIT.md) records the mathematical route, actual declaration dependency graph statistics, dated source provenance, and a preliminary comparison with Tang. A full literature and lemma-level novelty review remains outstanding.

## Publication branch

The research snapshot is preserved at [archive/research-2026](https://github.com/JamieLittle16/HessianConjecture4/tree/archive/research-2026) (commit `fe55e3fb`). This branch retains 229 HC4 modules, including the 227-module import closure of the two main endpoints, the umbrella module and the focused audit. The maintainer reported successful incremental builds and all five endpoint axiom audits after pruning. Two elementary lemmas were relocated verbatim; obsolete transitive imports were removed. The theorem statements are unchanged. Fresh-host verification of this smaller publication checkpoint is still pending.

The independent reproduction cited above applies to the earlier verified equivalence, not to the later pruning or migration. The publication migration now pins Lean and Mathlib 4.35.0. The maintainer reported a successful 9,274-job build and clean five-endpoint axiom audit after migration (commit `7842bc5`); the subsequent module-system conversion is at `0a69d9a`. A fresh independent build of the final submission snapshot remains outstanding.

## Palomar statement and verification

[Challenge.lean](Challenge.lean) states the polynomial-inverse equivalence and the same-field injectivity equivalence directly with Mathlib objects, without importing HC4. [Solution.lean](Solution.lean) proves the same two declarations from the existing development. The deliberate `sorry` statements in Challenge are required placeholders for Comparator, not part of the solution proof.

The standalone rational rigidity theorem remains a supporting result in the library and is not a separate advertised Comparator declaration in this submission. See [formalization.yaml](formalization.yaml) for structured provenance, AI assistance, source attribution, and review limitations.

Run from the repository root:

```bash
lake build HC4 Challenge Solution
lake env lean HC4/Audit.lean
bash scripts/verify-comparator.sh
```

The Comparator script uses the pinned toolchain's bundled independent kernels and requires bubblewrap. Final verification must pass before submission.

## Reproduce the proof

```bash
lake exe cache get
lake build HC4
lake env lean HC4/Audit.lean
```

The audit enforces the foundational axiom whitelist for five public endpoints, including the standalone rational rigidity theorem. For the full verification procedure including a deliberately false negative control, run `bash verify.sh`. For source indexes run `python3 tools/generate_proof_inventory.py`; for a read-only source closure report run `python3 tools/prune_publication.py`.

## Reading guide

- [Consolidated mathematical manuscript](docs/research/hc4-jc2-manuscript.tex) and [review record](docs/research/MANUSCRIPT_REVIEW.md).
- [Proof and contribution audit](docs/PROOF_AND_CONTRIBUTION_AUDIT.md) — historical verification, declaration statistics and attribution.
- [Documentation hub](docs/README.md).
- [Historical research snapshot](https://github.com/JamieLittle16/HessianConjecture4/tree/archive/research-2026) — all exploratory sources, phase notes and original documentation.

Development, Lean proof construction and manuscript drafting used substantial AI assistance. This is an independent project by Jamie Little, a Computer Science undergraduate at the University of Cambridge; no institutional endorsement is implied.

## Licence

The project's source is licensed under [Apache 2.0](LICENSE). See [NOTICE](NOTICE) and the original copyright headers for attribution and third-party material. Tang's preprint retains its own CC BY 4.0 licence.
