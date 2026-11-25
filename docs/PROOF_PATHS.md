# HC4 proof paths

**Source checkpoint: 25 November 2026, `90b9d97`.** See [CURRENT_STATE.md](CURRENT_STATE.md) for certification qualifications. This map is deliberately selective: exact Lean statements govern all hypotheses.

## Global and conditional routes

```text
det Hess F = 1 + alleged collision
  → existing canonical reduction / rawDefect descent
  → reachable presented terminal
  → OPEN: contradiction on actual reachable terminal
  → unrestricted HC4
```

Owner: [AdaptiveAlignedSmithCanonicalReachableHC4Reduction.lean](../HC4/Valuation/AdaptiveAlignedSmithCanonicalReachableHC4Reduction.lean), theorem `gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible`.

Conditional route: actual presented terminal → OPEN extraction of `TerminalAssociatedGradedCollisionData` → planar JC2 contradiction. Owner: [AdaptiveAlignedSmithCanonicalJC2HC4Assembly.lean](../HC4/Valuation/AdaptiveAlignedSmithCanonicalJC2HC4Assembly.lean). Alternative producer interfaces: [AdaptiveAlignedSmithCanonicalFinalPlanarJC2Frontier.lean](../HC4/Valuation/AdaptiveAlignedSmithCanonicalFinalPlanarJC2Frontier.lean). A local transverse theorem only contributes to either route after a source-honest adapter.

## Cap two

```text
actual cap-two source + determinant one + marked collision
  ├─ regular transverse determinantCore → regular gradient bijective
  └─ singular transverse determinantCore → linear-coefficient collision impossible
  → marked collision impossible
```

Owner: [QuadraticTransverseCapSourceMarkedEndpoint.lean](../HC4/Valuation/QuadraticTransverseCapSourceMarkedEndpoint.lean), theorem `quadraticTransverseCapSource_markedCollision_impossible`. To use it, derive the actual cap and exact marked collision, not just a rank-two layer or a presented proxy.

## Cubic / arbitrary leading transverse degree

| Step | Canonical source and theorem | Scope |
|---|---|---|
| Leading singularity | [TransverseLeadingCharacteristics](../HC4/Polynomial/TransverseLeadingCharacteristics.lean), `transverseLeading_hessian_det_eq_zero` | cap m ≥ 2, constant full Hessian determinant |
| Straight characteristic | same, `transverseLeading_exists_anchored_characteristic` | regular transverse anchor, characteristic zero |
| Classification | [TransverseLeadingLinearClassification](../HC4/Polynomial/TransverseLeadingLinearClassification.lean), `exists_sourceLeading_nilpotentLinear_or_nonPolynomial` | regular leading transverse block; actual source transport; linear matrix has cube zero |
| Fixed power | [TransverseLeadingFixedPower](../HC4/Polynomial/TransverseLeadingFixedPower.lean), `sourceLeading_fixedPower_of_nonzero_linear` | nonzero linear characteristic |
| Cubic determinant factors | same, `reference_cubic_det_triple_or_distinct_linear_of_nonzero_characteristic` | triple linear or square times nonproportional linear, under nonzero linear transport hypotheses |
| Squarefree rational pole | [RankThreeCubicSquarefreePoleFinal](../HC4/Polynomial/RankThreeCubicSquarefreePoleFinal.lean), `sourceCubic_squarefreePole_impossible` | actual cubic transport, squarefree determinant and nonpolynomial velocity |
| Rank-one pole closure | [RankThreeCubicSourceHomogeneousPoleRankOneClosure](../HC4/Polynomial/RankThreeCubicSourceHomogeneousPoleRankOneClosure.lean), `sourceCubic_homogeneousLinearPole_rankOne_impossible` | regular reference block, nonzero homogeneous linear factor dividing every adjugate entry |
| Lower grade | [TransverseLeadingFirstCorrection](../HC4/Polynomial/TransverseLeadingFirstCorrection.lean), `sourceLeading_constantDet_firstCorrection_trace_zero` | genuine adjacent grades, not arbitrary replacement polynomial |
| Mixed residue | same, `sourceCubic_fixedMixedResidue_directional_divisibility` | fixed direction and cleared mixed equation with nonzero residue |
| Latest endpoint | same, `sourceCubic_fixedMixedResidue_global_directionalSquare_eq_zero` | under explicit additional hypotheses yields global directional second derivative zero |

The characteristic split has stationary (N=0), nonzero linear and nonpolynomial possibilities. The listed endpoints are not an exhaustive closure of these cases; the singular leading-transverse-block case is not covered by the regular-anchor results.

For detailed older A19 interfaces, see the pinned [September route map](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/PROOF_PATHS.md) and [historical routes](HISTORICAL_AND_SUPERSEDED_ROUTES.md). For current research tasks see [NEXT_STEPS.md](NEXT_STEPS.md).
