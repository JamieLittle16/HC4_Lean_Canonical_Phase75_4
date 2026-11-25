# HC4 current proof state

**Source checkpoint: 25 November 2026, [`90b9d97`](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/commit/90b9d97e2937b34c12c2ab845a404048f4a3c4b1).** This is a source audit, not a new Lean certification. The maintainer reports that this checkpoint compiles; the exact CI result should be checked separately.

## Targets and status

| Target | Status at this checkpoint |
|---|---|
| Unrestricted determinant-one Hessian gradient injectivity in four variables | Open at the public theorem level in the interfaces audited here. |
| `PlanarJC2Injectivity K → HC4(K)`, with no extra extraction/producer assumption | Open in the interfaces audited here. |
| Transverse cap two, marked collision at 0 and the first unit vector, determinant one | Proved source declaration, including regular and singular transverse blocks. |
| Transverse cap two, polynomial automorphism in arbitrary dimension | Paper argument and exact rational-coefficient regression tests; not a universal Lean certificate. |
| Transverse cap three / full-rank leading transverse Hessian | Partial source results; no end-to-end injectivity conclusion established by the declarations below. |
| Arbitrary transverse cap, full-rank leading transverse Hessian | Source characteristic, linear classification and lower-grade constraints; not a complete injectivity theorem. |

Labels: **SOURCE THEOREM** means a proof declaration exists at the pinned source checkpoint. **LEAN VERIFIED** requires a successful build of that exact target/commit. **PAPER CANDIDATE** is an unverified mathematical argument; **OPEN** is an outstanding implication or integration obligation. Do not upgrade status based solely on an old handoff, theorem name or passing inventory export.

## Public assembly

The unrestricted target (under the project's ambient field assumptions) is
`∀ F : MvPolynomial (Fin 4) K, HC4.Polynomial.hessianDeterminant F = 1 → Function.Injective (mvGradientMap F)`.

* [Reachable reduction](../HC4/Valuation/AdaptiveAlignedSmithCanonicalReachableHC4Reduction.lean): `gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible` requires impossibility of presented rank-three terminals at zero raw defect for states with raw defect at most six. It does not prove this impossibility.
* [JC2 assembly](../HC4/Valuation/AdaptiveAlignedSmithCanonicalJC2HC4Assembly.lean): `gradient_injective_of_hessianDeterminant_one_of_JC2_of_presentedTerminalExtraction` requires both JC2 and `AdaptiveAlignedSmithCanonicalPresentedTerminalExtraction`. The latter demands actual associated-graded collision data from the presented terminal.
* [Final planar frontier](../HC4/Valuation/AdaptiveAlignedSmithCanonicalFinalPlanarJC2Frontier.lean): the source-native/relative first-contact producer variants also have extra hypotheses. Do not present them as a bare JC2 equivalence.

These are exact inspected interfaces, not an exhaustive search for every equivalent reduction. Keep the existing raw-defect recursion; do not add a parallel termination mechanism.

## Quadratic transverse cap

[Source marked endpoint](../HC4/Valuation/QuadraticTransverseCapSourceMarkedEndpoint.lean):
`quadraticTransverseCapSource_markedCollision_impossible` proves False from the actual source, `HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F`, determinant one and an exact gradient collision at the marked points 0 and (1,0,0,0).

The regular branch owns `quadraticTransverseCapSource_regularGradient_bijective` ([source](../HC4/Valuation/QuadraticTransverseCapSourceRegularGradient.lean)), under the nonzero transverse determinantCore. The singular branch owns `quadraticTransverseCap_two_singularSource_impossible` ([source](../HC4/Valuation/QuadraticTransverseCapSourceSingularClosure.lean)), under zero determinantCore and equality of the three source linear-coefficient evaluations at 0 and 1.

The marked result is not automatically a theorem about arbitrary collisions under a fixed transverse cap: an adapter must preserve the relevant bound or use a different proof. Nor does it show all canonical terminals have cap two. The dimension-independent polynomial inverse argument is [research/QuadraticTransverseCapAutomorphismBreakthrough.md](research/QuadraticTransverseCapAutomorphismBreakthrough.md).

## Cubic and arbitrary-degree transverse frontier

The most recent active module is [TransverseLeadingDirectionalRigidity.lean](../HC4/Polynomial/TransverseLeadingDirectionalRigidity.lean). Read the exact interfaces in [PROOF_PATHS.md](PROOF_PATHS.md) before working further.

* Arbitrary cap m ≥ 2: leading full Hessian determinant vanishes; a regular transverse anchor gives actual straight gradient transport.
* With generically invertible leading transverse block: a nilpotent linear characteristic or a genuinely nonpolynomial characteristic.
* Stationary cubic marked collision: `sourceStationary_cubic_markedCollision_impossible` in [TransverseLeadingStationary.lean](../HC4/Polynomial/TransverseLeadingStationary.lean) closes the case with zero leading longitudinal derivative, regular anchor at zero, nonzero constant determinant and the actual marked collision. Any normalization from the general stationary branch must preserve these hypotheses.
* Nonzero linear characteristic: a fixed directional power in the leading source; for a cubic, a repeated linear factor in the transverse determinant.
* Cubic squarefree determinant: a genuine nonpolynomial characteristic is impossible. Repeated-factor cases are not all excluded by this theorem.
* Latest mixed-residue seam: `sourceCubic_fixedMixedResidue_global_directionalSquare_eq_zero` proves a global directional second derivative vanishes, under its explicit fixed direction, prime, principal-cofactor, nonzero residue and mixed-equation hypotheses. It is not a collision contradiction or a proof that those hypotheses always hold.

Do not conflate the leading characteristic with the mixed-correction residue. Work from the original source, and carry every necessary hypothesis into the next step.

See [NEXT_STEPS.md](NEXT_STEPS.md) for immediate tasks. The September [status](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/CURRENT_STATE.md), [route map](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/PROOF_PATHS.md), and [implementation plan](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/FORMALISATION_PLAN_2026-09-12.md) remain historical mathematical evidence, not current TODO lists.
