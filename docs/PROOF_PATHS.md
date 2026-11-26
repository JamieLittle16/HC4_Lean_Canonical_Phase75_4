# Verified conditional HC4 proof path

**26 November 2026.** The final conditional result is verified at [38e58bf4](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/commit/38e58bf49cbd91ce9ae2d4e18b7d64e33fe02c8c). The earlier routes below are historical, not remaining hypotheses of this result.

## Main proof and manuscript outline

1. **Statement and definitions.** Over a characteristic-zero field K, assume planar Keller maps are injective. Let P be a four-variable polynomial with Hessian determinant one. The goal is injectivity of its evaluated gradient.
2. **Global weighted extremal reduction.** An alleged collision yields a globally optimal actual linear chart and nonnegative weight cap with positive determinant weight. The rank-zero, one, two and four possibilities for the leading Hessian are excluded. See [RankThreeExtremalReduction.lean](../HC4/Polynomial/RankThreeExtremalReduction.lean), `counterexample_exists_rankThree_complementary_chart`. Zero determinant weight is handled by [NonnegativeTerminalAssembly.lean](../HC4/Polynomial/NonnegativeTerminalAssembly.lean).
3. **Rank-three chart and relative pure power.** A constant adjugate annihilator and nonzero principal cofactor yield a normalized rational kernel. In [RankThreeOneVariableKernel.lean](../HC4/Polynomial/RankThreeOneVariableKernel.lean), `counterexample_rankThree_zeroWeight_relative_frontier` gives the omitted zero-weight coordinate, equal passive weights and vanishing restricted minors. Relative Euler and gradient ratios lead to `rankThree_relativePurePower`; degree two is excluded.
4. **Wronskian and genuine affine normalization.** `globalWeightOptimum_rankThree_relativeWronskian` excludes affine dependence of the two phase ratios. Clear all denominators and use a regular K-point where the polynomial jet determinant and both scalar factors are nonzero. Invert the second-order jet matrix and embed it in a constant four-dimensional affine chart. `rankThree_clearedPhase_normalize_impossible` transports the actual determinant and relative-degree cap, yielding the slope-zero leading layer c(u + ξv + ξ²t)^n.
5. **Signed first wall.** The explicit phase has nonzero passive principal cofactors. `rankThree_normalizedWall_impossible` excludes the lower-degree first contact and forces a contradiction with the nonzero constant full Hessian determinant. `rankThree_normalized_clearedPhase_impossible` handles regular-factor cancellation and exact signed top extraction.
6. **Assembly.** `globalWeightOptimum_rankThree_zeroWeight_impossible` excludes the last case, and `hc4_of_planarJC2` contradicts the original collision. The explicit gradient statement and transitive axiom report are in [Audit.lean](../HC4/Audit.lean).

This is a source-based outline, not yet a complete human-readable mathematical manuscript or an exhaustive declaration dependency graph. The recent Tang work that informed parts of the weighted approach must be identified and compared precisely before assigning priority; the formalisation is not a claim of independent discovery of every argument.

---

# Historical proof routes — checkpoint 25 November 2026

The following material preserves the previous route map and its local results. References to OPEN obligations concern those particular historical approaches only.

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
| Stationary cubic endpoint | [TransverseLeadingStationary](../HC4/Polynomial/TransverseLeadingStationary.lean), `sourceStationary_cubic_markedCollision_impossible` | cap three, nonzero constant determinant, stationary leading longitudinal derivative, regular anchor at zero, actual marked collision |
| Fixed power | [TransverseLeadingFixedPower](../HC4/Polynomial/TransverseLeadingFixedPower.lean), `sourceLeading_fixedPower_of_nonzero_linear` | nonzero linear characteristic |
| Cubic determinant factors | same, `reference_cubic_det_triple_or_distinct_linear_of_nonzero_characteristic` | triple linear or square times nonproportional linear, under nonzero linear transport hypotheses |
| Squarefree rational pole | [RankThreeCubicSquarefreePoleFinal](../HC4/Polynomial/RankThreeCubicSquarefreePoleFinal.lean), `sourceCubic_squarefreePole_impossible` | actual cubic transport, squarefree determinant and nonpolynomial velocity |
| Rank-one pole closure | [RankThreeCubicSourceHomogeneousPoleRankOneClosure](../HC4/Polynomial/RankThreeCubicSourceHomogeneousPoleRankOneClosure.lean), `sourceCubic_homogeneousLinearPole_rankOne_impossible` | regular reference block, nonzero homogeneous linear factor dividing every adjugate entry |
| Lower grade | [TransverseLeadingSchurFoundation](../HC4/Polynomial/TransverseLeadingSchurFoundation.lean), `sourceLeading_constantDet_firstCorrection_trace_zero` | genuine adjacent grades, not arbitrary replacement polynomial |
| Mixed residue | [TransverseLeadingDirectionalRigidity](../HC4/Polynomial/TransverseLeadingDirectionalRigidity.lean), `sourceCubic_fixedMixedResidue_directional_divisibility` | fixed direction and cleared mixed equation with nonzero residue |
| Latest endpoint | same, `sourceCubic_fixedMixedResidue_global_directionalSquare_eq_zero` | under explicit additional hypotheses yields global directional second derivative zero |

The characteristic split has stationary (N=0), nonzero linear and nonpolynomial possibilities. The listed endpoints are not an exhaustive closure of these cases; the singular leading-transverse-block case is not covered by the regular-anchor results.

For detailed older A19 interfaces, see the pinned [September route map](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/blob/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs/PROOF_PATHS.md) and [historical routes](HISTORICAL_AND_SUPERSEDED_ROUTES.md). For current research tasks see [NEXT_STEPS.md](NEXT_STEPS.md).
