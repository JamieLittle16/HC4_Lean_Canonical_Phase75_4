# Hessian Conjecture in Dimension Four

A Lean 4 formalisation of the equivalence of the planar Jacobian conjecture and the four-variable Hessian conjecture, together with supporting algebraic research.

## Verified polynomial-inverse equivalence

For every algebraically closed field K of characteristic zero, JC2(K) is equivalent to HC4(K): both conjectures assert that the relevant polynomial maps with nonzero constant Jacobian determinant possess a two-sided polynomial inverse. On the Hessian side the maps are formal gradients of arbitrary four-variable polynomials.

```lean
theorem HC4.StatementAudit.referenceJC2_iff_referenceHC4
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    HC4.StatementAudit.ReferenceJC K 2 ↔ HC4.StatementAudit.ReferenceHC4 K
```

See [FinalEquivalence.lean](HC4/FinalEquivalence.lean) for `HC4.StatementAudit.jc2_iff_hc4_explicit`, which expands both predicates directly using partial derivatives, matrix determinants, and polynomial substitution. The maintainer reported successful local verification on 26 November 2026 of this module (introduced in [`7fdbfcea`](https://github.com/JamieLittle16/HessianConjecture4/commit/7fdbfceae27addbf28928668678c62e18fc0fce8)), with all five printed declarations depending only on `[propext, Classical.choice, Quot.sound]`. Independent fresh-checkout reproduction remains to be recorded.

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

The [unified LaTeX manuscript](docs/research/hc4-jc2-manuscript.tex) consolidates the mathematical notes, including the anchored characteristic construction, rank exclusions, signed-wall contradiction, reverse doubling implication and polynomial-inverse bridge. See its [review record](docs/research/MANUSCRIPT_REVIEW.md) for formal interface checks and outstanding validation. The final manuscript compile and independent reproduction are not yet recorded.

## Global extremal-weight exposition

The [companion LaTeX note](docs/research/global-extremal-weight.tex) explains attainment over realized support patterns, local weight-improvement obstructions, the checked rank reductions and the final signed first-wall argument adapted from Tang. It is a source-linked proof outline; the longer rank-reduction lemmas are summarized rather than fully reproved. The [supporting rank-exclusion note](docs/research/extremal-rank-exclusions.tex) expands the constant-image obstruction, affine kernel graphs, isotropic-slope root evaluation, relative frontier and distinct-weight signed-wall rigidity. These notes complement the standalone rational rigidity note above.

## Mathematical attribution

The final weighted proof was substantially informed by Qiyue Tang, *[Equivalence of the Four-Variable Hessian and Planar Jacobian Conjectures](https://hexagonmath.org/2611.00156v2)*, Hexagon preprint 2611.00156v2 (2026), CC BY 4.0. Tang's preprint presents the equivalence over the complex numbers (Theorem 1.1). In particular, we adapted the Wronskian/Taylor coordinate normalization and signed first-wall obstruction in Lemma 3.3 (pp. 17–18), as well as drawing on the broader weighted leading-form strategy.

The project predates this preprint, but its earlier investigations and the completed proof should not be conflated with an independent discovery of the final implication. The contribution documented here is a Lean 4 formalisation and algebraic adaptation, including the precise same-field injectivity statement over arbitrary characteristic-zero fields. The final Lean proof does not assume Tang's theorem as an axiom. The [proof and contribution audit](docs/PROOF_AND_CONTRIBUTION_AUDIT.md) records the mathematical route, actual declaration dependency graph statistics, dated source provenance, and a preliminary comparison with Tang. A full literature and lemma-level novelty review remains outstanding.

## Reproduce the proof

Use the pinned Lean toolchain and Lake manifest.

```bash
lake exe cache get
lake build HC4.FinalEquivalence
lake env lean HC4/FinalEquivalence.lean
lake env lean HC4/Audit.lean
# Optional: build all historical and current modules
lake build
```

Look for the final axiom reports for `HC4.StatementAudit.jc2_iff_hc4_explicit` and `HC4.Polynomial.hc4_of_planarJC2`. The verification checkpoint is preserved in [PR #64](https://github.com/JamieLittle16/HessianConjecture4/pull/64).

## Reading guide

- [Proof, verification and contribution audit](docs/PROOF_AND_CONTRIBUTION_AUDIT.md) — consolidated mathematical summary and provenance for external reviewers.

- [Current proof status](docs/CURRENT_STATE.md)
- [Proof routes and exact interfaces](docs/PROOF_PATHS.md)
- [Publication and research next steps](docs/NEXT_STEPS.md)
- [Documentation hub](docs/README.md)
- [Historical research and phase notes](docs/archive/README.md)
- [Reconstruction provenance](RECONSTRUCTION_PROVENANCE.md)

Earlier valuation, Newton, Smith/Rees and transverse-cap investigations remain in the repository as mathematical research history; they are not extra hypotheses of the final theorem. For a broader verification script see `verify.sh`. Run `python3 tools/generate_proof_inventory.py` to regenerate the declaration and module indices.
