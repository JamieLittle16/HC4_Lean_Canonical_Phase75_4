# HC4 glossary and proof invariants

This document defines the vocabulary used by the current A18/A19 proof and records the invariants that should survive every adapter. Its purpose is to stop two common failures in a very large Lean development:

1. using the same word for mathematically different carriers; and
2. transporting a fact across normalization, ramification, recentering, initial-form selection, or first contact without the theorem that justifies the transport.

The Lean source remains authoritative. This glossary describes intended meaning and proof discipline.

## 1. Source-level objects

### Source polynomial

The original four-variable `MvPolynomial` whose gradient injectivity is being studied.

Do not confuse it with:

- a normalized translate/source transform;
- a polynomial family;
- a family special fibre;
- a presented/ramified family;
- an initial form or maximal ordinary face.

### Exact gradient collision

`HasExactGradientCollision F p q` means the coordinate partial derivatives of `F` agree at `p` and `q`.

It is the proposition-level form used by the normalization machinery after reducing failure of `Function.Injective (mvGradientMap F)`.

### Normalized collision

The canonical entry machinery moves an arbitrary distinct collision to the chosen axis configuration using determinant-preserving source changes. It is a transformed source with explicit equivalence/provenance, not a statement that the original points were already normalized.

## 2. Family-level objects

### Polynomial family

A parameterized polynomial object used by the valuation/Rees machinery. Family-level facts may concern all parameter layers, not only the special fibre.

### Special fibre

`polynomialFamilySpecialFiber family` is the parameter-zero polynomial.

A support witness in the special fibre is stronger than merely knowing that a coefficient occurs in some positive parameter layer, but weaker/different from support in a chosen initial form.

### Positive actual parameter layer

A genuine positive parameter order occurring in the family. The phrase **actual** is important: it refers to the current family before synthetic or normalized rescaling obscures the source order.

### First positive actual parameter order

The minimum positive parameter order of the actual family, when one exists. It is used to compare genuine source parameter order against determinant/raw-defect clocks.

## 3. Presentation and ramification

### Presented family / presented state

A canonical terminal may carry a presentation obtained by a pure positive ramification or related normalizing move.

Facts about the presented state are not automatically facts about the source state. Use the certified presentation move and its exact equalities.

### Pure ramification

A parameter substitution that multiplies relevant orders by a positive integer ramification factor.

Key discipline:

- equality/scale laws are safe when explicitly proved;
- a strict inequality measured after ramification is not automatically a strict inequality against the original unramified source clock;
- this is why successful positive Rees progress is tested at the actual rank-one trace state before accepting terminal presentation.

## 4. Scale-aware state vocabulary

### `ScaleAwareAdaptiveGeometricRestartState`

The canonical state carrier for the global Smith/Rees restart machine.

Conceptually it retains:

- the current polynomial family;
- raw Hessian/determinant defect data;
- repair metadata;
- scale/provenance information needed by certified transitions.

Do not introduce another final state type merely to store a subset of these fields unless an adapter boundary genuinely needs a smaller carrier.

### Repair state

The repair coordinate records the canonical rank/repair stage. In the final rank-one route the important equality is typically:

```lean
state.repair = rankOneRepairState complexity
```

A19 final assembly usually uses `complexity = 0`.

Repair equality is provenance. It is not a substitute for a well-founded measure.

### `rawDefect`

A natural-number defect attached to the actual scale-aware state.

This is the well-founded measure used by `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace`.

### Endpoint defect

A defect attached to an aligned/Smith endpoint or blocker endpoint. It may be related to state raw defect by an explicit theorem, but the two names should not be interchanged syntactically or conceptually.

### Presented raw defect

The raw defect of a presented/ramified state. It may equal a positive ramification factor times the source raw defect. That relationship must be used explicitly.

## 5. Progress vocabulary

### Global macro progress

`AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source` is the canonical global successor relation used by final assembly.

It is not itself the rank-one recursion measure.

### Rank-one restart edge

A restart constructor in `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace` stores:

- global macro progress;
- `target.rawDefect < source.rawDefect`;
- `target.repair = source.repair`;
- a tail trace from `target`.

A proposed move with exactly these properties belongs here.

### Outer global progress

After rank-three geometry is reached, some states may admit a strict global-macro successor even if that successor is not inserted into the raw-defect-only rank-one trace at that point. A19.45 exposes this distinction.

At a globally terminal reached rank-three state, A19.45 forces literal `rawDefect = 0`.

## 6. Newton/support carriers

### Support witness

A proof `d ∈ F.support` belongs to the exact polynomial `F` named in the proposition.

Never silently reuse it for another polynomial.

### Initial form

An exact weighted face of a polynomial at a specified weight and level.

Canonical support principle:

```text
support(initialForm ...) ⊆ support(source)
```

when supplied by the appropriate theorem.

The reverse inclusion is false in general.

### Maximal ordinary top face

The exact initial form selected at maximal ordinary degree. In the zero-defect terminal route it is a genuine nonzero polynomial whose Hessian determinant is zero.

It is **not** the whole represented special fibre.

### First-contact face

An exact initial form chosen by a contact weight so that previously on-facet support and newly outside support meet at the first contact level.

It is a new finite-support carrier.

### Lower first-nonfacet carrier

The first-contact face obtained when the maximal top face is confined to a facet but lower nonlinear source support leaves that facet.

It must remain distinct from the maximal top face.

### Cross-facet face

A face with actual support on both sides of a coordinate facet:

```text
some d with d j = 0
some q with 0 < q j
```

The generic carrier is `CrossFacetInitialData`.

### Finite-support affine ray

`CrossFacetRayData` is obtained by successive exact finite-support exposures in the three coordinates other than the contact coordinate. Its final face has support affinely proportional to the stored facet/outside direction.

This route does not require torus balance.

## 7. Boundary vocabulary

### Coordinate facet

A `ToricFacet` corresponds to one omitted source coordinate. Use `facetOmittedCoordinate` for the canonical bridge.

### `MvSupportOnFacet`

Every supported exponent of a polynomial lies on the chosen coordinate facet.

This is a whole-support predicate, not a statement about one boundary exponent.

### `MvExponentOnBoundary`

An exponent has at least one zero coordinate.

Canonical owner: `HC4.Polynomial`, despite heavy use in Newton modules.

### `MvRankThreeOnFacet facet d`

The exponent `d` has zero in the coordinate omitted by `facet` and positive exponents in the three remaining coordinates.

Because the definition depends on a facet match, elimination may require `mvRankThreeOnFacet_iff` or `cases facet`.

### Codimension-two boundary

An exponent has two distinct zero coordinates.

This is weaker/different from a fully constructed two-zero planar collision carrier.

## 8. Balance and homogeneity

### Torus balance

A linear arithmetic relation on exponents coming from a genuine toric grading/support condition.

Do not infer it from being on an affine ray or from Hessian singularity.

### Balanced affine-line route

The older cross-facet affine-line machinery uses a balance equation as one of the independent affine equations forcing line support.

Use it only when balance is actually proved for the carrier.

### Balance-free route

The unrestricted zero-clock branch replaces the unavailable balance equation by repeated finite-support exposure. `FiniteSupportCrossFacetRay.lean` is the canonical owner.

### Homogeneity

Global source homogeneity is **not** a general invariant of the current mixed-degree/recentered pipeline.

Use local exact initial-form homogeneity, top-face homogeneity, or `NonlinearDegreeBound` statements where those are what has actually been proved.

Do not strengthen a mixed-degree state to homogeneous merely to reach an old theorem.

## 9. Smith vocabulary

### Smith support exponent

A projected exponent recording the longitudinal/transverse coordinates relevant to the aligned Smith analysis.

### Strict-low patterns

The final zero-clock blocker retains one of three patterns:

- pure longitudinal;
- low-negative-first;
- low-negative-second.

A fourth `w`-linear pattern occurs in positive-Rees low-layer classification but is excluded on canonical surviving special fibres by the surviving-wall `noWLinear` result.

### Exact same-Smith-exponent mixed degree

`ExactSmithExponentMixedDegreeData` says distinct ordinary-degree source terms occur at the same exact projected Smith exponent after the specified recentering.

The phrase **same exponent** matters: do not combine unrelated witnesses from different projected exponents.

### First longitudinal departure

`HasFirstExactSmithExponentLongitudinalDeparture` records the first later longitudinal layer at that same Smith exponent.

This is a source of actual positive longitudinal support in the right-recentered represented special fibre.

## 10. Recentering vocabulary

### Right-recentered special fibre

The polynomial obtained by the canonical longitudinal right recentering used around the normalized two-endpoint collision.

Support in this polynomial is not support in the unrecentered represented fibre unless a reconstruction/transport theorem is invoked.

### Zero linear jet

The right-recentered blocker fibre has vanishing linear coefficients in the final strict-low route. This allows existing first-contact Hessian lemmas to turn a supported positive longitudinal monomial into nonzero diagonal-or-mixed Hessian geometry.

## 11. RationalRigidity vocabulary

### Rank-three line support

A polynomial support condition along a one-dimensional rank-three exponent family, often represented through explicit integer parameters.

### Affine rank-three line

A more general affine support relation that need not satisfy the older integral finite-segment divisibility model.

Do not coerce an affine line into the older segment representation without proving the arithmetic conditions.

### Two-fixed contradiction

The affine RationalRigidity route eventually derives incompatible fixed relations at two normalized endpoints/directions. `RankThreeAffineTwoFixedImpossible.lean` is a terminal owner for that contradiction.

### Terminal adapter

A Valuation/Newton theorem that packages the exact current carrier into a RationalRigidity interface. It should not redo the RationalRigidity algebra.

## 12. Planar / JC2 vocabulary

### Two-zero form

A specialized geometry with the exact zero-coordinate structure required by the planar reduction.

### Planar collision

A carrier that has been converted to the two-dimensional Jacobian/Hessian problem required by `PlanarJC2HessianEmbedding` and related theorems.

A generic codimension-two exponent is not automatically a planar collision.

## 13. Carrier identity invariants

These are mandatory proof disciplines.

### Invariant A — support provenance

For every `d ∈ F.support`, record which `F` it belongs to. Transport requires one of:

- equality of polynomials;
- support subset theorem;
- coefficient reconstruction theorem;
- exact initial-form support theorem.

### Invariant B — clock provenance

Every inequality involving a defect/order should say whether it concerns:

- source raw defect;
- presented raw defect;
- endpoint defect;
- first positive actual parameter order;
- ramified order.

Do not cancel scale factors informally.

### Invariant C — repair provenance

If a theorem needs `state.repair = rankOneRepairState 0`, preserve or rederive that exact equality through every transition.

### Invariant D — balance provenance

If a theorem uses `HasBalancedMvSupport`, identify the theorem that supplies balance on that exact carrier.

### Invariant E — actual witness retention

If an actual exponent/face/target has already been constructed, prefer storing it over replacing it with an existential proposition that loses identity.

### Invariant F — no duplicate termination

Global recursive descent remains the `rawDefect : ℕ` recursion already encoded in `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace`.

## 14. Namespace ownership

Use the namespace of the representation owner:

| Kind of concept | Expected namespace |
|---|---|
| four-variable polynomial/exponent/support predicate | `HC4.Polynomial` |
| finite-support Newton geometry / boundary / first contact | `HC4.Newton` |
| scale-aware state / Smith / Rees / progress / provenance | `HC4.Valuation` |
| rank-three terminal algebra / projective contradiction | `HC4.RationalRigidity` |
| toric combinatorics | `HC4.Toric` |

Frequent consumption by another subsystem does not change ownership.

## 15. Filename suffix semantics

These are conventions rather than Lean rules, but they help navigation.

### `...Data`

Retains a concrete witness and facts about it.

### `...Packet`

Bundles several logically related facts about the same carrier without necessarily defining a new structure.

### `...Frontier`

Exposes an exhaustive next-step split.

### `...Split`

Performs a local case distinction, usually preserving explicit failure witnesses.

### `...Reduction`

Rephrases a larger goal as smaller named obligations or a sharper interface.

### `...Closure`

Discharges one family of branches, often by routing them to progress or contradiction.

### `...Impossible`

Terminal contradiction theorem or adapter into one.

### `...Adapter`

Transports an established interface to another representation without introducing new fundamental mathematics.

### `...Reentry` / `...Restart` / `...Progress`

State-machine operations. Check clock and repair provenance especially carefully.

## 16. Common category errors

### Error: “Both polynomials have the same formula shape, so support transfers.”

Fix: use an explicit polynomial equality or coefficient theorem.

### Error: “The terminal is ramified but the defect got smaller, so recurse.”

Fix: compare on the actual unramified state or use the exact certified raw-defect restart theorem.

### Error: “Boundary means rank three.”

Fix: use the rank-three-or-codimension-two split.

### Error: “Codimension two means planar JC2.”

Fix: build the exact planar collision carrier first.

### Error: “An affine ray gives torus balance.”

Fix: use the balance-free route or prove actual balance separately.

### Error: “A positive reached rank-three state is a local low-layer terminal.”

Fix: A19.45 routes positive reached rank-three geometry to outer global progress.

### Error: “A theorem name is free because this file compiles alone.”

Fix: inspect the generated declaration index and full import graph; sibling modules may collide only under an aggregator.

## 17. Minimal annotation to include in new module docstrings

For every substantial new final-assembly module, say:

1. **Carrier:** exact polynomial/state/face the theorem is about.
2. **Consumes:** previous module/theorem interface.
3. **Produces:** exact next interface.
4. **Preserves:** support/repair/clock provenance that remains available.
5. **Does not assume:** especially balance, homogeneity, JC2, synthetic endpoint, or new progress if absent.

That small discipline makes the generated module index much more useful because its purpose field comes directly from module documentation.