# Hessian Conjecture in Dimension Four

A Lean 4 formalisation of the implication from planar Jacobian injectivity to four-dimensional determinant-one Hessian gradient injectivity, together with supporting algebraic research.

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

**Scope:** this proves conditional gradient injectivity, not unconditional HC4, not planar JC2 itself, and not a polynomial inverse theorem as presently stated. See the attribution below; detailed mathematical priority and dependency analysis remain outstanding.

## Mathematical attribution

The final weighted proof was substantially informed by Qiyue Tang, *[Equivalence of the Four-Variable Hessian and Planar Jacobian Conjectures](https://hexagonmath.org/2611.00156v2)*, Hexagon preprint 2611.00156v2 (2026), CC BY 4.0. Tang's preprint presents the equivalence over the complex numbers (Theorem 1.1). In particular, we adapted the Wronskian/Taylor coordinate normalization and signed first-wall obstruction in Lemma 3.3 (pp. 17–18), as well as drawing on the broader weighted leading-form strategy.

The project predates this preprint, but its earlier investigations and the completed proof should not be conflated with an independent discovery of the final implication. The contribution documented here is a Lean 4 formalisation and algebraic adaptation, including the precise same-field injectivity statement over arbitrary characteristic-zero fields. The final Lean proof does not assume Tang's theorem as an axiom. A detailed comparison of proof dependencies and the relevant earlier literature is still needed for a scholarly manuscript.

## Reproduce the proof

Use the pinned Lean toolchain and Lake manifest.

```bash
lake exe cache get
lake build HC4.Polynomial.RankThreeOneVariableKernel
lake build
lake env lean HC4/Audit.lean
```

Look for the final axiom report for `HC4.Polynomial.hc4_of_planarJC2`. The verification checkpoint is preserved in [PR #64](https://github.com/JamieLittle16/HessianConjecture4/pull/64).

## Reading guide

- [Current proof status](docs/CURRENT_STATE.md)
- [Proof routes and exact interfaces](docs/PROOF_PATHS.md)
- [Publication and research next steps](docs/NEXT_STEPS.md)
- [Documentation hub](docs/README.md)
- [Historical research and phase notes](docs/archive/README.md)
- [Reconstruction provenance](RECONSTRUCTION_PROVENANCE.md)

Earlier valuation, Newton, Smith/Rees and transverse-cap investigations remain in the repository as mathematical research history; they are not extra hypotheses of the final theorem. For a broader verification script see `verify.sh`. Run `python3 tools/generate_proof_inventory.py` to regenerate the declaration and module indices.
