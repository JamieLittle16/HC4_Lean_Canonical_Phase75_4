# Historical and superseded HC4 proof routes

The HC4 repository is cumulative. Old theorems are usually retained because they are proved and may remain reusable, even after a stronger or more provenance-honest route becomes the preferred final assembly.

This document prevents a common failure mode: seeing an older reduction or phase note, assuming it is current, and rebuilding infrastructure that a later route has already replaced.

## 1. Status vocabulary

Use these labels when reading old files.

### Active live route

The preferred path for the current unrestricted proof.

### Reusable alternate route

Still mathematically valid and useful when its exact hypotheses are available, but not the default path from the unrestricted front door.

### Superseded interface

A proved theorem or resolver structure whose obligations were subsequently reduced further. It remains valid, but should not be treated as the current missing-lemma list.

### Historical checkpoint

A Markdown/status artifact describing the repository at an earlier point. Useful for archaeology only.

## 2. Historical phase Markdown files

The root files:

```text
FORMALISATION_STATUS_PHASE*.md
FORMALISATION_LEDGER.md
CERTIFICATION_STATUS.md
```

record earlier snapshots.

They are **not** authoritative for:

- what is currently missing;
- which theorem owner is canonical;
- whether a gap listed there has subsequently been closed;
- which final-assembly route is now preferred.

Current authority order:

```text
Lean source
  > generated inventory
  > docs/CURRENT_STATE.md
  > docs/PROOF_PATHS.md / PROOF_ARCHITECTURE.md
  > canonical owners
  > historical status files
```

## 3. Evolution of the unrestricted residual interface

The A19 development intentionally left milestone reductions in the tree. Read them as a sequence of strengthening interfaces.

### A19.1 — arbitrary presented-terminal impossibility

`AdaptiveAlignedSmithCanonicalHC4Reduction.lean`

The unrestricted gradient-injectivity theorem was reduced to impossibility of every normalized presented terminal.

This was correct but stronger than needed because it forgot that the terminal was actually reached from the canonical rank-one path.

### A19.23 — reachable presented-terminal impossibility

`AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean`

Improvement: retain

```lean
state.repair = rankOneRepairState 0
```

at the reached terminal.

Preferred over the arbitrary-terminal version when doing final assembly.

### A19.24 — three-field final residual resolver

`AdaptiveAlignedSmithCanonicalFinalResidualReduction.lean`

Residual fields were:

1. zero strict-low;
2. positive low layer;
3. positive Rees re-entry.

**Superseded as a current TODO list.** Later files remove/reclassify positive branches.

### A19.26 — constructor-specific residual resolver

`AdaptiveAlignedSmithCanonicalFinalResidualConstructorReduction.lean`

Split blocker/surviving constructors and discharged crossed impossible combinations.

Still useful as a constructor theorem, but not the sharpest final frontier.

### A19.34b — Rees-reduced trace

`AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction.lean`

Major architectural correction: successful positive Rees coefficient bounds are inserted as ordinary restart edges at the actual rank-one trace state.

This deletes the old successful-Rees-reentry residual.

### A19.35 — actual source-order low-layer split

`AdaptiveAlignedSmithCanonicalRankOneReesLowLayerOrderReduction.lean`

Positive low layers are refined presentation-free into:

- actual special-fibre low support; or
- genuinely earlier positive actual parameter layer.

This is stronger than the undifferentiated positive-low-layer field, but it too is later overtaken at the final local/global split.

### A19.45 — positive reached rank-three is global progress

`AdaptiveAlignedSmithCanonicalRankOneReesRankThreeClosure.lean`

This is the decisive strengthening:

```text
reached rawDefect = 0
OR
outer global macro progress
```

Therefore positive reached rank-three geometry is no longer a locally terminal obligation.

**For current final assembly, do not resurrect positive-low-layer resolver fields below a globally terminal reached state.**

### A19.46 — one zero-blocker first-contact producer

`AdaptiveAlignedSmithCanonicalRankOneReesFinalOutcome.lean`

After A19.45, the local frontier was reduced to one producer which, from a zero-clock strict-low blocker and first departure, promised an honest first-contact endpoint.

This was an intermediate interface.

### A19.53 — producer-free zero strict-low terminal

`AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean`

The producer is no longer needed. The actual blocker/exponent/zero-clock data are retained directly.

**Use this route for new work.**

## 4. Balanced affine-line route versus balance-free finite-support route

These are not chronological versions of the same theorem. They have different assumption sets.

### Older balanced route — reusable alternate

Core owner:

- `HC4/Newton/FirstContactCrossFacetAffineLine.lean`

It uses genuine torus balance as one of the independent affine equations.

Downstream modules include the `FirstContactCrossFacetAffineRR*.lean` family and `RationalRigidity/RankThreeAffineTwoFixedImpossible.lean`.

This route is still valid **when balance is actually available on the exact carrier**.

### Newer balance-free route — active unrestricted local route

Core owners:

- `HC4/Newton/FiniteSupportCrossFacetExposure.lean`
- `HC4/Newton/FiniteSupportCrossFacetRay.lean`
- `HC4/Newton/PositiveCoordinateSingularBoundaryVertex.lean`

It replaces the missing balance equation by three successive finite-support exact exposures.

Use it in the unrestricted zero-clock strict-low branch.

### Invalid migration

Do not take a balance-free carrier and add/assume torus balance merely to re-enter the older affine-line route.

## 5. Integral finite-segment support versus general affine support

Several older rank-three terminal modules use integer finite-segment parameterizations. Later first-contact geometry can produce a more general affine line/ray.

These are not interchangeable.

The historical mistake to avoid is:

```text
general affine support
    -> silently assume integral step/divisibility
    -> use old finite-segment theorem
```

The newer affine/RationalRigidity adapters were developed specifically to avoid that hidden divisibility assumption.

When exact integer segment data are genuinely available, the older route remains useful.

## 6. Homogeneous-source routes versus mixed-degree current states

Earlier parts of the project frequently worked under ordinary or graded homogeneity assumptions.

The current canonical restart pipeline can be mixed-degree after recentering and local transformations.

The replacement discipline is:

- use `NonlinearDegreeBound` when a degree cap is what is actually preserved;
- use exact homogeneous initial forms/top faces locally;
- do not infer global source homogeneity from a homogeneous selected face.

Older homogeneous theorems remain reusable when the exact homogeneous hypotheses have been proved on the current carrier.

## 7. Old terminal cocharacter/endpoint producers versus retained actual carriers

Earlier final-assembly attempts often introduced a producer whose output was a synthetic terminal endpoint/cocharacter satisfying the hypotheses of an older contradiction theorem.

The current direction is to retain actual objects already present in the proof:

- actual strict-low exponent;
- actual represented special fibre;
- actual first longitudinal departure;
- actual singular maximal top face;
- actual finite cross-facet carrier;
- actual finite-support ray;
- actual boundary exponent.

Prefer this provenance-preserving route over manufacturing a new endpoint unless a theorem genuinely requires one and the construction is proved.

## 8. Old positive-Rees-after-presentation reasoning

A previous temptation was to perform a terminal presentation first, run a Rees step on the ramified state, observe a strict decrease there, and treat it as descent from the original source.

That is unsafe because pure ramification rescales the clock.

Current correction:

- run successful Rees progress at the actual trace state;
- use `AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceProgress`;
- insert it into the existing raw-defect trace.

Do not revive cross-scale rational descent.

## 9. Positive low-layer residuals after A19.45

Files such as:

- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesLowLayerOrder.lean`
- `AdaptiveAlignedSmithCanonicalSurvivingLowLayerElimination.lean`
- `AdaptiveAlignedSmithCanonicalRankOneReesLowLayerOrderReduction.lean`

remain useful and contain real theorems.

However, at the **final globally terminal reached rank-three node**, A19.45 is stronger: positive raw defect gives outer global progress.

So these low-layer modules should be viewed as ingredients in proving/understanding positive progress and as reusable local results, not as the final live terminal checklist.

## 10. Two-zero / JC2 route

The repository contains a real planar/JC2 pathway:

- `TwoZeroDoublingHessianSquareGeneral.lean`
- `TerminalTwoZeroDoublingForm.lean`
- `TerminalTwoZeroPlanarCollision.lean`
- `PlanarJC2HessianEmbedding.lean`
- `AdaptiveAlignedSmithFirstContactTwoZeroJC2.lean`
- `AdaptiveAlignedSmithCanonicalFirstContactPlanarCollision.lean`
- `AdaptiveAlignedSmithCanonicalFinalPlanarJC2Frontier.lean`
- `AdaptiveAlignedSmithCanonicalJC2HC4Assembly.lean`

Status: **reusable specialized route**, not an automatic interpretation of every codimension-two boundary exponent.

A current codimension-two carrier must first be proved to satisfy the exact two-zero/planar hypotheses.

## 11. Classified-family / old main assembly route

`HC4/MainAssembly.lean` and `HC4/ClassifiedFamilies/*` belong to an older downstream classification architecture: once a gradient has already been placed into one of the classified forms, they provide explicit inverses/conjugacies and final injectivity consequences.

These modules remain valuable, but they are not the current missing bridge from an unrestricted determinant-one polynomial to classification.

Do not read `MainAssembly.lean` as the current unrestricted front door.

## 12. Historical “missing GN / autonomous ODE / four-sided” ledger entries

Old phase ledgers listed broad manuscript gaps such as Gordan–Noether, autonomous ODE front halves, four-sided character bridges, or global Newton assembly.

Since then the repository has accumulated extensive replacement infrastructure, including:

- finite-support exposed boundary machinery;
- autonomous polynomial clearing/root modules;
- large rank-three RationalRigidity families;
- global Smith/Rees termination and provenance;
- unrestricted collision entry;
- producer-free zero-clock local carriers.

Therefore an old ledger line saying “missing X” is not evidence that X should be implemented under that historical formulation.

Search the current module/declaration indexes and live proof path first.

## 13. How to classify an old file you encounter

Ask in this order:

1. Is it imported by a current live frontier module?
2. Does a later module explicitly say it strengthens/replaces its interface?
3. Does it require balance, homogeneity, a producer, a ramified clock comparison, or a stronger terminal model absent from the live carrier?
4. Is the theorem generic and still reusable even if its assembly interface is old?

Then label it mentally as:

```text
active owner
reusable alternate
superseded reduction
historical artifact
```

Do not delete proved infrastructure merely because it is not on the current main path; instead keep the live-path documentation explicit.

## 14. Migration rules for future proof work

### If an old resolver has more fields than a new resolver

Use the new resolver.

### If an old theorem requires balance and the current carrier is balance-free

Use the finite-support route or prove genuine balance; do not assume it.

### If an old theorem uses an integral segment and the current carrier is affine

Use affine RationalRigidity or prove the missing divisibility exactly.

### If an old theorem produces an existential endpoint but the current state already stores a witness

Adapt the retained witness rather than constructing a second endpoint.

### If an old theorem treats positive rank-three as a local terminal

Use A19.45 and route it to outer global progress.

### If an old phase note says a theorem is missing

Search the generated index and current source before writing anything.

## 15. What should actually be removed?

Normally, very little Lean infrastructure needs deletion during final assembly. Keeping proved alternate routes has value.

Candidates for deletion should be limited to things such as:

- accidental duplicate declarations;
- genuinely dead temporary files with no mathematical ownership role;
- documentation that claims to be current but cannot be maintained.

Prefer marking old proof routes in this document over deleting valuable proved lemmas.