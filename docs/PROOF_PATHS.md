# HC4 proof paths

This document is a **route map**. It is organized around the proof obligation you currently have and tells you which files form the canonical path to the next interface.

It complements:

- `CURRENT_STATE.md` — what is currently live/open;
- `PROOF_ARCHITECTURE.md` — why the architecture is organized this way;
- `CANONICAL_OWNERS.md` — where reusable concepts are defined;
- `generated/LEAN_MODULE_INDEX.md` — exhaustive file/import/declaration inventory.

The tables below use four columns:

- **Have** — the exact carrier/hypothesis available;
- **Use** — canonical file or theorem family;
- **Get** — the next interface;
- **Do not substitute** — a tempting but invalid shortcut.

## 1. Unrestricted HC4 front door

| Have | Use | Get | Do not substitute |
|---|---|---|---|
| `F` with `hessianDeterminant F = 1` and a hypothetical distinct exact gradient collision | `AdaptiveAlignedSmithCanonicalCollisionNormalization.lean`, `...CollisionAutoDegree.lean` | normalized collision with canonical degree data | do not require a homogeneous input or caller-supplied degree cap |
| normalized exact collision | `AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.lean` | canonical zero-defect collision entry and positive rank-one re-entry | do not create a parallel entry state |
| collision entry | `AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean` | reachable rank-one terminal obligation with repair provenance | do not quantify over arbitrary unrelated presented terminals if reachability is available |

The public contradiction starts from `mvGradientMap F p = mvGradientMap F q`, converts it to `HasExactGradientCollision`, and enters the canonical state machine once.

## 2. Rank-one global termination

| Have | Use | Get | Do not substitute |
|---|---|---|---|
| canonical rank-one state with `repair = rankOneRepairState complexity` | `AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgress.lean` | complete rank-three geometry or an actual strict successor | do not invent a semantic progress token |
| strict successor with global progress + `rawDefect` drop + repair equality | `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean` | recursive tail in the same trace | no rational descent or secondary well-founded clock |
| completed trace | `AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean` | contradiction once terminal impossibility is supplied | do not run another induction on the stored decrease proofs |

Canonical recursion measure:

```lean
termination_by source.rawDefect
```

That is the only rank-one recursion.

## 3. Positive Rees path at an actual trace state

```text
actual rank-one trace state
        |
        v
positive transverse Rees coefficient test
        |
        +-----------------------------+
        | bound succeeds              | bound fails
        v                             v
global progress +                 concrete positive
rawDefect drop +                  Rees low layer
repair preserved                      |
        |                             v
        +---- ordinary trace restart  retained actual-state evidence
```

Canonical files:

- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesFrontier.lean`
- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceProgress.lean`
- `AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction.lean`

The coefficient test must be run on the **actual unramified trace state** when it is being used to justify an A18 restart. Do not postpone the comparison until after a pure ramified presentation and then compare incompatible clocks.

## 4. Rees-reduced reached rank-three path

Canonical file:

- `AdaptiveAlignedSmithCanonicalRankOneReesRankThreeClosure.lean` (A19.45)

Exact split:

```text
reached rank-three state
        |
        +-----------------------------+
        | rawDefect = 0               | global macro successor exists
        v                             v
local zero-clock problem          outer global progress
```

A positive reached rank-three state is therefore **not** a live local terminal case.

When working below a globally terminal reached state, first use:

```lean
reachedRankThree_rawDefect_eq_zero_of_no_globalProgress
```

or the corresponding zero-or-progress theorem instead of carrying old positive residual fields forward.

## 5. Zero-clock constructor split

At raw defect zero, the normalized presented rank-three terminal historically had blocker and surviving constructors.

The current route uses:

- surviving strict-low exclusion from the presented surviving family;
- conformal zero-clock impossibility when no strict-low pattern occurs;
- the actual blocker strict-low exponent when one does occur.

Key files include:

- `AdaptiveAlignedSmithCanonicalTerminalConformalZeroClockImpossible.lean`
- `AdaptiveAlignedSmithCanonicalRankOneReesFinalOutcome.lean` (A19.46, historical producer interface)
- `AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean` (A19.53, current producer-free carrier)

Use A19.53 for new final-assembly work.

## 6. Zero strict-low source packet: A19.49–A19.54

### 6.1 Actual strict-low exponent → residual normal form

**Have**

```text
presented blocker D
actual e ∈ smithProjectedSupport ... specialFiber
one of the three strict-low patterns
```

**Use**

- `AdaptiveAlignedSmithCanonicalZeroStrictLowBlocker.lean`
- `AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm.lean` (A19.49)

**Get**

One of three concrete two-endpoint factorizations:

```text
pure longitudinal:    A' = X (X - 1) C, C ≠ 0
low-negative-first:   A  = X (X - 1) B, B ≠ 0
low-negative-second:  A  = X (X - 1) B, B ≠ 0
```

Do not replace these by pattern labels once the factorization is available.

### 6.2 Same exponent → mixed-degree / first departure

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowMixedDegree.lean` (A19.50)

Get, on the same right-recentered represented fibre and same Smith exponent:

- `ExactSmithExponentMixedDegreeData`;
- `HasFirstExactSmithExponentLongitudinalDeparture`.

The identity of the exponent matters. Do not combine witnesses from different projected exponents merely because their pattern types match.

### 6.3 Source zero → represented zero packet

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowZeroClockPacket.lean` (A19.51)

Get:

- represented state raw defect zero;
- blocker endpoint defect zero;
- residual normal form;
- exact mixedness;
- first longitudinal departure.

### 6.4 First departure → Hessian geometry

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactHessian.lean` (A19.52)
- older zero-linear-jet/right-recentering owners it imports.

Get:

- actual first-contact diagonal-or-mixed Hessian geometry on the right-recentered represented special fibre.

### 6.5 Packet → producer-free terminal

Use:

- `AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean` (A19.53)

Get:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData` retaining state, blocker, zero clock, exponent, support membership, and pattern.

### 6.6 Terminal → singular maximal ordinary top face

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminal.lean` (A19.54)

Get:

- complete rank-three geometry on the actual represented blocker;
- literal represented raw defect zero;
- genuine nonzero maximal ordinary top face;
- Hessian determinant zero on that top face.

This top face is a new carrier. Do not move recentered-source support witnesses onto it without a support theorem.

## 7. Singular top face → balance-free boundary split: A19.55–A19.56

### A19.55

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryFrontier.lean`
- generic `FiniteSupportSingularBoundaryVertex.lean`
- `SingularBoundaryRankSplit.lean`

Get an actual exposed nonlinear top-face exponent satisfying:

```text
rank three on a coordinate facet
OR
codimension two
```

No balance hypothesis is used.

### A19.56

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStrata.lean`

Get literal nonempty `zeroCoordinateSupport` slices on the actual top face.

This is the bridge from an abstract coordinate-zero statement to finite-support data.

## 8. Rank-three top-face branch: A19.58 onward

Suppose the A19.55 boundary exponent is rank three on `facet`.

### 8.1 Does the actual top face already cross the facet?

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeFacetSplit.lean` (A19.58)

Exact split:

```text
positive omitted-coordinate support exists on top face
    -> CrossFacetInitialData on that same top face
OR
entire top face is supported on the facet
```

Do not use the recentered outside-support witness from A19.57 as though it were top-face support.

### 8.2 Confined top face → source-level first-nonfacet hypotheses

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetSource.lean` (A19.59)

Get:

- `NonlinearDegreeBound topDegree sourceSpecialFiber`;
- polynomial Monge–Ampère equation;
- `TopDegreeOnFacet facet topDegree sourceSpecialFiber`.

### 8.3 Source split below the top degree

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeSourceSplit.lean` (A19.60)

Exact trichotomy:

```text
direct top-face cross-facet data
OR
top face confined + lower nonlinear source support outside facet
OR
all nonlinear source support confined to facet
```

## 9. Lower-outside-support branch

### 9.1 Low-degree behavior

Use:

- `HC4/Newton/FirstNonfacetLowDegreeSquareSplit.lean` (A19.65)

Get:

```text
LowDegreeTameAtFacet
OR
literal supported quadratic square in omitted coordinate
```

The second branch is exact finite-support data, not “failure of tameness.”

### 9.2 Tame branch → honest first contact

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet.lean` (A19.66)
- generic `FirstNonfacetContact.lean`
- generic `FirstContactCrossFacetCarrier.lean`
- generic `FiniteSupportCrossFacetExposure.lean`

Get a carrier containing:

- actual first-contact face;
- positive scale/bump;
- exact initial-form identity;
- Hessian determinant zero;
- every supported monomial nonlinear;
- actual support on both sides of the contact facet;
- exact contact equation.

Do not replace this carrier by the maximal top face: it is a lower first-contact object.

## 10. Cross-facet carrier → balance-free affine ray

Use:

- `HC4/Newton/FiniteSupportCrossFacetRay.lean` (A19.67)

The construction performs three successive exact cross-facet exposures in the three non-contact coordinates.

Get `CrossFacetRayData` with:

- actual facet and outside exponents;
- both still in the original carrier support;
- final-face support subset;
- Hessian singularity transport;
- coordinatewise affine proportionality.

This is the canonical unrestricted replacement for the older torus-balance affine-line equation.

## 11. Ray → outside boundary transition

### A19.68

Use:

- `HC4/Newton/PositiveCoordinateSingularBoundaryVertex.lean`
- `AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayBoundary.lean`

Get a nonlinear supported boundary exponent whose old contact coordinate remains strictly positive.

Therefore if it is rank three on `next`, then:

```text
facetOmittedCoordinate next ≠ facetOmittedCoordinate oldFacet
```

### A19.69

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowCrossFacetBoundaryTransition.lean`

Get:

```text
rank three on a genuinely different coordinate facet
OR
codimension two
```

for either:

- direct top-face cross-facet carrier; or
- retained lower first-contact cross-facet carrier.

## 12. A19.70 exact rank-three residual frontier

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeBoundaryReduction.lean`

Starting from a rank-three A19.55 boundary exponent, obtain one of:

```text
1. top-face boundary transition
2. retained lower-carrier boundary transition
3. literal omitted-coordinate quadratic square
4. complete nonlinear source confinement
```

The proof preserves which polynomial/face owns each witness.

This is the current exact rank-three local frontier.

## 13. Confinement branches

The strict-low factorization already forces actual nonlinear source monomials.

### Low-negative-first

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowResidualSupport.lean`
- `AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementFacetElimination.lean`

Actual source support has positive coordinates `0` and `2`, so complete confinement can survive only on `.pr` or `.rq`.

### Low-negative-second

Actual source support has positive coordinates `0` and `1`, so complete confinement can survive only on `.sp` or `.rq`.

### Pure longitudinal

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport.lean`

Get an actual nonlinear source monomial supported only in longitudinal coordinate `0`. Hence complete confinement cannot be on `.qs`.

### Unified classification

Use:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementPatternSplit.lean` (A19.64)

Do not rederive pattern-sensitive facet lists downstream.

## 14. Codimension-two branch

The generic owner is:

- `HC4/Newton/SingularBoundaryRankSplit.lean`

The zero-strict-low carrier exposing this branch is:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryFrontier.lean`
- `AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStrata.lean`

Treat codimension two as its own live carrier. A codimension-two boundary exponent is **not automatically** the same thing as the specialized two-zero planar collision data required by the JC2 bridge.

Before using a planar theorem, prove the exact transport from the actual top-face/source carrier to the planar interface.

## 15. Older balanced cross-facet affine-line route

Use this route only if genuine torus balance is available.

Canonical sequence:

```text
FirstContactCrossFacetAffineLine
    -> FirstContactCrossFacetEndpointStratum
    -> FirstContactCrossFacetAffineRR
    -> FirstContactCrossFacetAffineRRReconstruction
    -> FirstContactCrossFacetAffineRRTerminal
    -> FirstContactCrossFacetAffineRRTerminalScalarData
    -> FirstContactCrossFacetAffineRRTwoFixedCertificate
    -> FirstContactCrossFacetAffineRRTwoFixedElimination
    -> FirstContactCrossFacetAffineRRFiniteSplit
    -> FirstContactCrossFacetAffineRRTransition
    -> FirstContactCrossFacetAffineRRImpossible
    -> RationalRigidity/RankThreeAffineTwoFixedImpossible
```

This path remains valid where its hypotheses are present. It is not the default unrestricted zero-clock route.

Do not force a balance equation or an integral finite-segment parameterization merely to enter it.

## 15a. Exact PR leading self calculation (R18.36--R18.37)

All files below are under `HC4/Valuation/` and share the prefix
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContact`.

| Owner suffix | Established output |
| --- | --- |
| `PrExtremalContactLayer.lean` | Exact contact slices and parameter/source Euler scalars |
| `PrExtremalResidualLayers.lean` | Longitudinal Hessian scalar, leading contact-order minimality, longitudinal support ceiling |
| `PrExtremalComplementLayers.lean` | Leading straightened mixed and quadratic entries |
| `PrLeadingSelfCoefficient.lean` | Full leading raw-complement coefficient; exact parameter-residual coefficient; residual-zero iff leading contact deficit is zero |
| `PrExtremalOrders.lean` | Nonzero-slice cancellation **when** the scalar/slice zero has been supplied |
| `BinaryProfilePivotExtremalCancellation.lean` | Terminal contradiction **when** both exposed active-pivot/profile product coefficients have been proved zero |

The last two rows are conditional consumers, not proofs of their inputs.
R18.36--R18.37 finish the displayed coefficient calculations, but do not kill
the raw complementary coefficient or either exposed active-pivot/profile
product coefficient. The remaining geometric correction is explained in
`CURRENT_STATE.md`, section 8a. In particular, the parameter residual is not
identically zero at the leading exposed order when its contact deficit is
positive.

## 16. Rank-three RationalRigidity route

The RationalRigidity directory is the contradiction owner. Typical flow is:

```text
actual supported rank-three geometry
    -> line / affine / vertical recognition
    -> endpoint/direction refinement
    -> binomial or autonomous-polynomial normal form
    -> fixed-direction / two-fixed equalities
    -> contradiction
```

Main families:

- `RankThreeBalancedHomogeneous*.lean`
- `RankThreeSupported*.lean`
- `RankThreeAffine*.lean`
- `RankThreeRootMultiplicity.lean`
- `PolynomialAutonomousClearing.lean`
- `PolynomialAutonomousQuadraticExtraction.lean`
- `RankThreeVertical*.lean`

Valuation adapters should package inputs for these owners. They should not clone the univariate/projective calculation.

## 17. Terminal singular-carrier adapter route

Canonical files:

- `AdaptiveAlignedSmithCanonicalTerminalSingularCarrier.lean`
- `AdaptiveAlignedSmithCanonicalTerminalSupportFrontier.lean`
- `AdaptiveAlignedSmithCanonicalTerminalRigidityData.lean`
- `AdaptiveAlignedSmithCanonicalTerminalRankThreeFirstContact.lean`
- `AdaptiveAlignedSmithCanonicalTerminalImpossible.lean`

This route is useful once the exact supported balanced rank-three line certificates have genuinely been constructed.

`AdaptiveAlignedSmithCanonicalTerminalImpossible` deliberately does not equate arbitrary affine first-contact lines with the older integral supported-segment model.

## 18. Two-zero / planar / JC2 route

Canonical files include:

- `HC4/Newton/TwoZeroDoublingHessianSquareGeneral.lean`
- `HC4/Newton/TerminalTwoZeroDoublingForm.lean`
- `HC4/Newton/TerminalTwoZeroPlanarCollision.lean`
- `HC4/PlanarJC2HessianEmbedding.lean`
- `HC4/Valuation/AdaptiveAlignedSmithFirstContactTwoZeroJC2.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalFirstContactPlanarCollision.lean`
- `AdaptiveAlignedSmithCanonicalFirstContactPlanarEquivalence.lean`
- `AdaptiveAlignedSmithCanonicalFinalPlanarJC2Frontier.lean`
- `AdaptiveAlignedSmithCanonicalJC2HC4Assembly.lean`

This is a legitimate specialized route when the exact two-zero/planar hypotheses have been established. It is not a shortcut from an arbitrary codimension-two exponent.

## 19. How to choose a route

Use this decision sequence:

```text
Do I have actual balance?
  yes -> balanced route may be available
  no  -> finite-support/balance-free route

Is my witness on the same carrier required by the next theorem?
  yes -> apply it
  no  -> find/prove an explicit equality/subset/transport theorem

Does my proposed step give global progress + rawDefect drop + repair equality?
  yes -> it belongs in the existing rank-one trace

Am I at a reached rank-three state with positive rawDefect?
  yes -> A19.45: seek outer global progress, not a local terminal contradiction

Am I globally terminal?
  yes -> reduce to literal rawDefect zero, then use the zero strict-low chain
```

## 20. How to verify a proposed missing lemma really is missing

Before adding it:

1. search `CANONICAL_OWNERS.md`;
2. search the declaration spelling in `generated/DECLARATION_INDEX.md`;
3. search concept synonyms in `generated/LEAN_MODULE_INDEX.md`;
4. inspect reverse importers to see whether an apparently unrelated module already owns the bridge;
5. compare the exact carrier and hypotheses, not just the conclusion wording;
6. only then create a new owner or adapter.

If a theorem exists with stronger data but on a different carrier, the missing work is probably a **transport adapter**, not a duplicate theorem.
