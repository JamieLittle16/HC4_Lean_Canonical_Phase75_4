# HC4 proof architecture

This document explains the **live mathematical architecture** of the cumulative HC4 Lean development. It is organized by proof role, not chronology.

Use the documentation set as follows:

- `CURRENT_STATE.md` — exact theorem-level status and live frontier;
- `PROOF_PATHS.md` — branch-by-branch file sequence;
- `CANONICAL_OWNERS.md` — canonical reusable definitions and theorem families;
- `GLOSSARY_AND_INVARIANTS.md` — carrier, clock, balance, and provenance vocabulary;
- `HISTORICAL_AND_SUPERSEDED_ROUTES.md` — how older proved routes relate to the current one;
- `generated/LEAN_MODULE_INDEX.md` — exhaustive index of every Lean module.

## 1. The current top-level proof shape

The unrestricted proof begins by contradicting a hypothetical distinct exact gradient collision for a four-variable polynomial with Hessian determinant one.

```text
F with hessianDeterminant F = 1
        +
distinct p,q with mvGradientMap F p = mvGradientMap F q
        |
        v
canonical collision normalization
+ automatic nonlinear degree cap
        |
        v
zero-defect collision entry
        |
        v
canonical positive rank-one re-entry
        |
        v
rank-one state
        |
        v
A18.4.109 raw-defect termination trace
with successful positive Rees moves folded into restart edges
        |
        v
actual reached rank-three state
repair provenance retained
        |
        +--------------------------------------+
        |                                      |
        | outer global successor exists        | no outer global successor
        v                                      v
continue global macro proof              A19.45 forces rawDefect = 0
                                               |
                                               v
                                  producer-free zero strict-low terminal
                                               |
                                               v
                                  genuine singular maximal top face
                                               |
                                               v
                                  balance-free boundary rank split
                                               |
                         +---------------------+---------------------+
                         |                                           |
                         v                                           v
                  rank-three facet                            codimension two
                         |
                         v
                  A19.58--A19.70
        cross-facet / lower first contact /
        quadratic square / confinement frontier
```

The decisive current point is A19.45: **positive reached rank-three geometry is outer global progress, not a locally terminal low-layer branch**. The genuinely local final frontier is at literal raw defect zero.

## 2. Unrestricted collision entry

Canonical modules:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalCollisionNormalization.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalCollisionAutoDegree.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4Reduction.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean`

The public input is not assumed homogeneous, torus-balanced, pre-normalized, or equipped with an external degree cap.

The reachable-terminal reduction is the preferred final-assembly interface because it retains actual provenance from the canonical rank-one path, especially

```lean
state.repair = rankOneRepairState 0
```

Do not weaken this to an arbitrary-terminal interface unless a reusable theorem genuinely benefits from the stronger quantification.

## 3. The only rank-one recursion

Owner:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean`

The trace has two constructors:

```text
terminal completeRankThreeGeometry
restart globalProgress rawDefect_lt repair_eq tail
```

Its recursive call is justified only by:

```lean
target.rawDefect < source.rawDefect
```

with `rawDefect : ℕ`.

Structural consumption is owned by:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean`

### Architectural invariant

There is no need for another final rank-one recursion. In particular do not introduce:

- rational well-founded descent;
- cross-scale descent treated as a natural order;
- repair promotion as a termination measure;
- a second final trace object duplicating A18.4.109.

If a proposed move supplies global macro progress, strict actual raw-defect decrease, and unchanged repair state, it belongs as an ordinary restart edge of the existing trace.

## 4. Positive Rees moves and clock provenance

Canonical family:

- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesFrontier.lean`
- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceProgress.lean`
- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesUnramified*.lean`
- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesLowLayerOrder.lean`
- `AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction.lean`

The key correction in A19.34b is **where** a successful Rees test is consumed.

A normalized terminal may contain a positive pure ramification. A strict decrease measured only after that presentation is not automatically a strict decrease from the unramified source state. Therefore successful Rees progress is tested at the actual rank-one trace state, where it produces the exact A18 restart data.

`AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace` is the resulting trace-facing carrier.

Older positive-low-layer resolver structures remain proved milestones, but A19.45 subsequently shows that positive **reached rank-three** geometry is outer global progress.

## 5. A19.45: the global/local boundary

Owner:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneReesRankThreeClosure.lean`

At the actual reached state:

```text
rawDefect = 0
OR
genuine AdaptiveAlignedSmithCanonicalGlobalMacroProgress
```

Thus if the reached state is globally terminal, its raw defect is literally zero.

This theorem is the current boundary between global and local proof work. New local terminal arguments should normally begin **after** using A19.45, not from older positive residual resolver fields.

## 6. Producer-free zero-clock terminal

Historical intermediate owner:

- `AdaptiveAlignedSmithCanonicalRankOneReesFinalOutcome.lean` (A19.46)

A19.46 reduced the local problem to one zero-blocker first-contact producer.

Current owner:

- `AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean` (A19.53)

A19.53 removes that producer and retains actual data:

- zero-clock reached state;
- canonical repair equality;
- canonical presented blocker;
- actual represented strict-low Smith exponent;
- support membership;
- one of the three genuine strict-low patterns.

This is an important architectural shift: **retain existing witnesses rather than manufacture a synthetic endpoint.**

## 7. The zero strict-low source packet

The live chain begins before Newton boundary analysis:

### A19.49 — residual normal form

`AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm.lean`

Turns the actual strict-low pattern into an exact two-endpoint polynomial factorization.

### A19.50 — exact same-exponent mixedness

`AdaptiveAlignedSmithCanonicalZeroStrictLowMixedDegree.lean`

Retains mixed ordinary-degree support and the first longitudinal departure at the **same actual Smith exponent**.

### A19.51 — zero-clock packet

`AdaptiveAlignedSmithCanonicalZeroStrictLowZeroClockPacket.lean`

Carries the source zero clock through the certified pure presentation and bundles the normal form/mixedness/departure data.

### A19.52 — Hessian first contact

`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactHessian.lean`

Uses the already-proved zero-linear-jet/right-recentering infrastructure to turn actual later longitudinal support into genuine nonzero diagonal-or-mixed Hessian geometry.

### A19.53 — producer-free terminal

`AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean`

Packages the actual local terminal data.

### A19.54 — singular top-face carrier

`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminal.lean`

Attaches the genuine nonzero maximal ordinary top face of the represented zero-clock family, with Hessian determinant zero.

## 8. Balance-free Newton boundary architecture

At this point the important carrier is the **actual singular maximal ordinary top face**.

### Generic owners

- `HC4/Newton/FiniteSupportExposedVertex.lean`
- `HC4/Newton/FiniteSupportSingularBoundaryVertex.lean`
- `HC4/Newton/MvBoundaryStrata.lean`
- `HC4/Newton/SingularBoundaryRankSplit.lean`
- `HC4/Newton/PositiveCoordinateSingularBoundaryVertex.lean`

### A19.55

`AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryFrontier.lean`

Exposes an actual nonlinear boundary exponent and splits:

```text
rank three on a coordinate facet
OR
codimension two
```

No torus balance is used.

### A19.56

`AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStrata.lean`

Converts the abstract boundary condition into actual finite support slices on the same top face.

## 9. Rank-three top-face architecture

For a rank-three boundary exponent on a coordinate facet:

### A19.58 — direct cross or top-face confinement

`AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeFacetSplit.lean`

If the same top face contains positive support in the omitted coordinate, construct `CrossFacetInitialData` there. Otherwise the whole top face is confined to the facet.

### A19.59 — transport confinement to source hypotheses

`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetSource.lean`

Exports:

- nonlinear degree bound;
- polynomial Monge–Ampère equation;
- top-degree-on-facet hypothesis.

### A19.60 — source trichotomy

`AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeSourceSplit.lean`

```text
direct top-face cross-facet
OR
lower nonlinear source support outside facet
OR
all nonlinear source support confined
```

This split is source-honest: it does not infer that a recentered witness lies on the top face.

## 10. Residual source support and confinement

### Low-negative source witnesses

- `AdaptiveAlignedSmithCanonicalZeroStrictLowResidualSupport.lean` (A19.61)

The factorized coefficient polynomial reconstructs actual nonlinear source support.

### Low-negative confinement elimination

- `AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementFacetElimination.lean` (A19.62)

Uses explicit positive source coordinates to restrict possible confinement facets.

### Pure-longitudinal source witness

- `AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport.lean` (A19.63)

Reconstructs an actual nonlinear axis monomial.

### Unified pattern-sensitive confinement classification

- `AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementPatternSplit.lean` (A19.64)

In particular complete nonlinear confinement cannot occur on the marked `.qs` facet.

## 11. Lower first-nonfacet cross-facet architecture

### A19.65 — exhaustive low-degree split

Generic owner:

- `HC4/Newton/FirstNonfacetLowDegreeSquareSplit.lean`

```text
LowDegreeTameAtFacet
OR
literal supported omitted-coordinate quadratic square
```

The failure branch is explicit finite-support data.

### A19.66 — actual first-nonfacet carrier

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet.lean`

In the tame branch the generic first-nonfacet selector is applied to the actual represented special fibre. The resulting carrier retains:

- exact first-contact face;
- scale/bump;
- Hessian singularity;
- nonlinear support;
- actual support on both sides of the contact facet;
- exact contact equation.

It is intentionally a **lower first-contact carrier**, not the maximal top face.

## 12. Two cross-facet routes — keep them distinct

There are two mathematically different routes.

### 12.1 Balanced affine-line route

Owner:

- `HC4/Newton/FirstContactCrossFacetAffineLine.lean`

Downstream:

- `FirstContactCrossFacetEndpointStratum.lean`
- `FirstContactCrossFacetAffineRR*.lean`
- `HC4/RationalRigidity/RankThreeAffineTwoFixedImpossible.lean`

This route uses a genuine torus-balance equation. It remains reusable where balance is proved.

### 12.2 Balance-free finite-support ray route

Owners:

- `HC4/Newton/FiniteSupportCrossFacetExposure.lean`
- `HC4/Newton/FiniteSupportCrossFacetRay.lean`

`FiniteSupportCrossFacetRay` performs three successive exact exposures in the three non-contact coordinates. Their exact weight equations replace the unavailable balance equation and force support onto an affine ray.

This is the active unrestricted zero-clock cross-facet route.

Do not add balance merely to reuse the older route.

## 13. A19.67--A19.70 boundary transition chain

### A19.67

`HC4/Newton/FiniteSupportCrossFacetRay.lean`

Produces `CrossFacetRayData` with actual support provenance and coordinatewise affine proportionality.

### A19.68

- `HC4/Newton/PositiveCoordinateSingularBoundaryVertex.lean`
- `AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayBoundary.lean`

Forces an exposed singular boundary exponent while preserving positivity of the old contact coordinate. Therefore a rank-three outcome cannot return to the same omitted-coordinate facet.

### A19.69

`AdaptiveAlignedSmithCanonicalZeroStrictLowCrossFacetBoundaryTransition.lean`

A direct or lower cross-facet carrier yields:

```text
rank three on a different facet
OR
codimension two
```

### A19.70

`AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeBoundaryReduction.lean`

The current exact rank-three frontier is:

1. top-face boundary transition;
2. boundary transition on a retained lower first-contact carrier;
3. literal omitted-coordinate quadratic square;
4. complete nonlinear source confinement to the starting facet.

Carrier identity is retained in every branch.

## 14. Codimension-two is a separate branch

`MvExponentOnCodimensionTwoBoundary` is owned by `HC4/Newton/SingularBoundaryRankSplit.lean`.

A codimension-two exponent is not automatically a specialized two-zero planar collision. The repository has a separate two-zero/JC2 route, but an adapter must prove that the exact current carrier satisfies those stronger hypotheses before using it.

Relevant planar modules include:

- `HC4/Newton/TwoZeroDoublingHessianSquareGeneral.lean`
- `HC4/Newton/TerminalTwoZeroDoublingForm.lean`
- `HC4/Newton/TerminalTwoZeroPlanarCollision.lean`
- `HC4/PlanarJC2HessianEmbedding.lean`
- `HC4/Valuation/AdaptiveAlignedSmithFirstContactTwoZeroJC2.lean`
- `AdaptiveAlignedSmithCanonicalFirstContactPlanarCollision.lean`
- `AdaptiveAlignedSmithCanonicalFinalPlanarJC2Frontier.lean`
- `AdaptiveAlignedSmithCanonicalJC2HC4Assembly.lean`

## 15. Terminal RationalRigidity architecture

`HC4/RationalRigidity/` owns the contradiction algebra. Major families are:

- balanced homogeneous direction/endpoint rigidity;
- supported/binomial line normal forms;
- affine line terminal normal forms;
- fixed-direction and two-fixed equalities;
- autonomous-polynomial clearing and quadratic extraction;
- root multiplicity;
- vertical-line contradiction.

Important active terminal owner:

- `HC4/RationalRigidity/RankThreeAffineTwoFixedImpossible.lean`

Valuation/Newton code should package exact data for RationalRigidity and invoke it. Do not reproduce the projective/univariate algebra inside a state-machine adapter.

`AdaptiveAlignedSmithCanonicalTerminalImpossible.lean` is an example of the correct adapter pattern: it packages an actual singular carrier into an already-closed terminal contradiction when the genuine supported balanced rank-three line certificates are available.

## 16. Carrier provenance is part of the proof

Treat these as distinct until an explicit theorem connects them:

```text
original source
normalized/recentered source
polynomial family
family special fibre
presented/ramified family
blocker endpoint raw special fibre
right-recentered special fibre
maximal ordinary top face
first-contact face
cross-facet face
lower first-nonfacet carrier
finite-support ray
```

A support witness on one carrier is not automatically support on another.

The same applies to clocks:

```text
source raw defect
presented raw defect
endpoint defect
actual trace-edge raw-defect decrease
parameter-layer order
ramified parameter order
```

See `GLOSSARY_AND_INVARIANTS.md` for the full rules.

## 17. What not to rebuild

Before adding new infrastructure, search for existing owners of:

- four-variable boundary/facet predicates;
- coordinate support filters;
- exact initial-form coefficient/support identities;
- finite-support maxima/minima and exposed vertices;
- Hessian singularity preservation through exact initial forms;
- first-contact weights/contact equations;
- cross-facet exposure and affine-ray extraction;
- Smith projected support/pattern predicates;
- exact same-exponent mixed-degree data;
- longitudinal coefficient polynomial reconstruction;
- right-recentering/zero-linear-jet identities;
- positive Rees bounds, source progress, and low-layer order;
- canonical global macro progress;
- rank-one termination trace;
- RationalRigidity line/endpoint contradictions.

Use `CANONICAL_OWNERS.md` and the generated declaration index before declaring a generic-looking theorem or definition.

## 18. How the documentation stays non-duplicative

The documentation itself has ownership boundaries:

- **current truth:** `CURRENT_STATE.md`;
- **mathematical architecture:** this file;
- **exact route lookup:** `PROOF_PATHS.md`;
- **definition/theorem ownership:** `CANONICAL_OWNERS.md`;
- **vocabulary and invariants:** `GLOSSARY_AND_INVARIANTS.md`;
- **old-route interpretation:** `HISTORICAL_AND_SUPERSEDED_ROUTES.md`;
- **every file/declaration/import:** generated indexes.

Do not copy full status tables between documents. Link to the owner document instead.

## 19. Final completion criterion

The project reaches unrestricted HC4 only when a top-level theorem proves determinant-one gradient injectivity with no caller-supplied resolver, producer, terminal-impossibility hypothesis, balance assumption, homogeneity assumption, or JC2 hypothesis, and that theorem is included in the audited root build.

Until then, the correct description is: **global termination and unrestricted entry are built; final zero-clock local boundary assembly remains.**