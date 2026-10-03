# HC4 fresh-context handoff — unit finite-staircase final closure

**Date:** 17 September 2026  
**PR:** #34 — `final-assembly/a18-4-42-termination-frontier`  
**Purpose:** authoritative continuation point for the last local `V = 1` finite-staircase closure and the final unrestricted-HC4 splice.

This document supersedes `HANDOFF_2026-09-16_HC4_FRESH_CONTEXT_FINAL_SPRINT.md` as the **active TODO / continuation handoff**. Older handoffs remain useful mathematical provenance, but the live branch has now moved materially beyond their stated stopping points.

---

## 1. Read this first

The most important status distinction is:

```text
current branch state != last certified code checkpoint
```

At the time this handoff was prepared, the branch had a generated-inventory commit on top of the last substantive code commit. The authoritative proof checkpoint is therefore the last code commit whose complete CI suite is known green.

### Certified code checkpoint — LEAN VERIFIED

```text
commit: e2783035171d173516a33448615f6cccd4ec9feb
message: Add unit finite-staircase extremal fibers
Lean CI run: 35237635579
```

That run passed all four certification jobs:

```text
Build HC4                                      PASS
Axiom audit                                    PASS
Proof-complete branch negative control         PASS
Escape-hatch audit                             PASS
```

Therefore everything explicitly marked **LEAN VERIFIED** below is certified against `e2783035171d173516a33448615f6cccd4ec9feb`.

At drafting time the branch head above it was:

```text
cc8a7327e15ddf359650ed4a81e4161c01364f13
chore: update generated inventories 2026-09-17 14:59:43 UTC
```

That is a generated-inventory commit, not a new mathematical checkpoint. A fresh session must **re-pin PR #34 first** because bot inventory commits may have advanced the branch again.

Do not call a later head Lean-verified merely because it is descended from `e2783035...`; check its workflow state. If only documentation/inventory changed, keep `e2783035...` as the proof checkpoint until a later full certification run is actually green.

---

## 2. Executive proof state

The unrestricted HC4 development is no longer waiting on the broad A19 geometry programme described in the older September handoffs. The difficult global architecture, the nonunit other-facet closures, the unit endpoint machinery, and now most of the unit strict-interior finite-staircase infrastructure are already in Lean.

The live local state is now very narrow:

```text
nontrivial .pr other-facet carrier
            |
            | nonunit V>1 orientations already closed
            v
unit quotient (1,1)
            |
            | endpoint/contact + two source-honest interior selectors
            v
least strict-interior fibre Alo.k
highest strict-interior fibre Ahi.k
            |
            | LEAN VERIFIED: Alo.k <= every interior k <= Ahi.k
            v
       compare Alo.k, Ahi.k
          /             \
         /               \
   equal fibre        strict separation
   Alo.k=Ahi.k        Alo.k<Ahi.k
       |                  |
       | VERIFIED         | OPEN
       | same layer       | unit multi-fibre
       | same j/profile   | contradiction
       | dual Euler       |
       | degree trichotomy|
       v                  v
 one-fibre diagonal      contradiction
 contradiction OPEN
          \             /
           \           /
            unit strict interior impossible
                       |
                       v
          existing endpoint/no-interior closure
                       |
                       v
                   close .pr
                       |
                       v
              .sp/.rq by transport
                       |
                       v
             existing A19/global splice
                       |
                       v
               unrestricted HC4
```

The key new fact since the 16 September handoff is that the source-honest coupling between the two unit selectors is no longer speculative: the equal-fibre layer/profile identification, common dual Euler law, degree trichotomy, and least/greatest extremal selector theorems all compile in the certified build.

The remaining mathematical core is therefore:

1. eliminate the **equal-fibre** unit case by porting/reusing the already-verified nonunit lower/middle/upper diagonal contradictions;
2. eliminate the **strictly separated** unit multi-fibre case by porting/reusing the nonunit extrema/cross-roof machinery;
3. package those into unit finite-staircase closure;
4. splice the resulting unit contradiction into the already-existing `.pr` / other-facet / A19 / global assembly.

---

## 3. Status vocabulary — use this exactly

Use these labels in all continuation notes:

- **LEAN VERIFIED** — theorem/source is in a stated commit whose complete Lean certification run passed.
- **SOURCE-LANDED / NOT LEAN VERIFIED** — source is committed but the exact head has not passed the full relevant CI yet.
- **PAPER CANDIDATE** — a mathematical route is written/understood but is not compiled as the desired Lean theorem.
- **DIAGNOSTIC ONLY** — experiment, counterexample, symbolic computation, or audit result; not a proof theorem.
- **OPEN** — genuine remaining mathematical/formal/assembly obligation.

Do not use “basically done”, “solved”, or “green” without saying exactly which level is meant.

---

## 4. What is already LEAN VERIFIED and must not be rebuilt

### 4.1 Global / A19 architecture

The repository already contains the major A16/A17/A18/A19 assembly infrastructure developed during August and September: termination traces, zero-defect re-entry, global geometry-carrying rank-two frontiers, source-honest other-facet reductions, actual rank-two chart lifting, and the parent strict-low assembly route.

The final sprint should **splice into that infrastructure**, not invent another global restart mechanism.

In particular, do not restart work on generic JC2, generic stationary determinant comparison, or global homogeneity. Those were either deliberately avoided or superseded.

### 4.2 Nonunit `.pr` finite staircase

Both nonunit orientations are already closed. The live parent assembly uses the existing `V > 1` finite-staircase closure and reduces the `.pr` survivor to either a unit quotient or an actual rank-two chart.

Reference family:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircase*.lean
```

Do not reprove the nonunit closure. Use it as the template for the unit final steps.

### 4.3 Unit contact frontier and endpoint infrastructure

The normalized unit quotient and its two transverse orientations are already represented source-honestly.

Important existing modules include:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitContactFrontier.lean
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitNoInteriorSupport.lean
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointOnlySupport.lean
```

The right endpoint-only unit mirror has already been repaired and certified. Do not reopen it unless the compiler exposes a real dependency issue.

### 4.4 Locked/contact-side strict-interior selector

The low selector is source-honest and has exact affine coordinates, literal carrier coefficients, a nonzero one-variable profile, and its locked-end first variation.

Important modules:

```text
...PrUnitPlanarContactRees.lean
...PrUnitPlanarContactFirstInterior.lean
...PrUnitPlanarInteriorAffineLayer.lean
...PrUnitPlanarInteriorMomentRealisation.lean
...PrUnitPlanarLockedMomentRealisation.lean
...PrUnitPlanarInteriorFirstVariation.lean
```

The structure

```lean
QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData
```

contains, among other data,

```lean
k : ℕ
j : ℕ
1 < k
k < F.highest.n
0 < j
j < F.locked.ell
```

with support coordinates

```text
e0 + e1 = k
e0 + e2 = j + 1
e0 + e3 = k + j.
```

Its coefficient profile is nonzero and satisfies the locked-side affine two-root Euler equation.

### 4.5 Highest/pair-Rees strict-interior selector

The high selector is likewise source-honest and exposes the same affine-fibre interface.

Important modules:

```text
...PrUnitPairReesFirstInteriorAffineLayer.lean
...PrUnitPairReesFirstInteriorMomentRealisation.lean
...PrUnitPairReesHighestMomentRealisation.lean
...PrUnitPairReesFirstVariation.lean
```

The structure

```lean
QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData
```

has the same `k`, `j`, strict inequalities, affine support coordinates, literal carrier coefficient retention, and nonzero coefficient profile. Its profile satisfies the highest-end affine two-root Euler equation.

---

## 5. New certified unit finite-staircase infrastructure

This is the main progress that makes the remaining work small enough for a final closure sprint.

### 5.1 Equal selected pair degree means the literal same source fibre — LEAN VERIFIED

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiber.lean
```

Certified theorems include:

```lean
QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData.firstPositiveLayer_support_eq_pairFiber

QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData.firstPositiveLayer_support_eq_pairFiber

QsOtherFacetPrUnitLeftContactFrontierData.selectedInteriorLayers_eq_of_k_eq

QsOtherFacetPrUnitLeftContactFrontierData.selectedInterior_j_eq_of_k_eq

QsOtherFacetPrUnitLeftContactFrontierData.selectedInteriorProfiles_eq_of_k_eq
```

The two selected Rees layers are each exactly the carrier support fibre of their selected pair degree. Therefore, under

```lean
hext : Alo.k = Ahi.k
```

the selected multivariate layers are literally equal. From the common nonzero layer, the affine coordinates force

```lean
Alo.j = Ahi.j
```

and the honest one-variable coefficient profiles are literally equal.

This is stronger and cleaner than an abstract comparison argument: both selectors have landed on the same source-carrier fibre with unchanged coefficients.

### 5.2 Equal fibre gives two endpoint Euler equations on one nonzero profile — LEAN VERIFIED

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseEndpointEuler.lean
```

Main theorem:

```lean
QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_commonProfile_dualEuler
```

Under `Alo.k = Ahi.k`, it proves that `Alo.coefficientProfile` is nonzero and simultaneously satisfies:

```text
locked endpoint affineTwoRootEulerOperator = 0
highest endpoint affineTwoRootEulerOperator = 0.
```

This is the exact common-profile coupling needed for the one-fibre degree argument.

### 5.3 Equal fibre degree trichotomy — LEAN VERIFIED

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberDegree.lean
```

Main theorem:

```lean
QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_degree_trichotomy
```

For equal selected pair degree it proves:

```lean
Alo.j + 2 = Alo.k ∨
Alo.j + 1 = Alo.k ∨
Alo.j = Alo.k
```

The proof uses the state-free polynomial theorem

```lean
HC4.Polynomial.natDegree_eq_root_or_succ_of_affineTwoRoot
```

on the common nonzero profile, together with source-honest nonvanishing of the endpoint coefficients.

This theorem is already compiled. The next session should **consume this trichotomy**, not rebuild its degree analysis.

### 5.4 The two selectors are the actual least and greatest strict-interior fibres — LEAN VERIFIED

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseExtrema.lean
```

Certified theorems:

```lean
QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData.isLeast_strictInteriorPairFiber

QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData.isGreatest_strictInteriorPairFiber
```

For any source-carrier monomial lying on a strict-interior pair fibre, these prove respectively

```text
Alo.k <= k(e)
```

and

```text
k(e) <= Ahi.k.
```

Thus the low/contact selector is genuinely the least surviving strict-interior pair fibre and the high/pair-Rees selector is genuinely the greatest.

This is the correct starting point for the final split. There is no need to invent an auxiliary “two-fibre state”.

---

## 6. Live `.pr` parent assembly

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly.lean
```

The important current theorem is:

```lean
pr_nontrivial_after_nonunit_closure
```

Its effective conclusion is:

```lean
∃ R : QsOtherFacetContactQuadraticReesPackage C,
  Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1) ∨
  Nonempty (ActualRankTwoHessianChart (K := K))
```

Interpretation:

- all nonunit `.pr` quotient orientations have already been eliminated;
- if the desired rank-two geometry has not already appeared, the only `.pr` survivor is the **unit `(1,1)` quotient**.

Therefore the local target is not “understand arbitrary other-facet geometry”. It is simply:

```text
eliminate the surviving unit (1,1) quotient
OR turn it into the existing rank-two exit.
```

Once that is done, the parent `.pr` assembly should be strengthened so it no longer returns a live unit quotient branch.

---

## 7. Immediate next theorem: order the two selected unit fibres

This should be the first implementation in a fresh context.

Given strict-interior data `Alo` and `Ahi`, prove

```lean
Alo.k ≤ Ahi.k.
```

The proof should be thin:

1. take a supported exponent `e` from the nonzero high/pair-Rees selected layer;
2. `Ahi.coordinates` gives pair degree `Ahi.k`;
3. `Ahi.k_gt_one` and `Ahi.k_lt_highest` show it is strict interior;
4. its literal carrier provenance comes from `Ahi.coefficient_eq_carrier` / the already-proved exact fibre support theorem;
5. apply
   ```lean
   Alo.isLeast_strictInteriorPairFiber
   ```
   to obtain `Alo.k ≤ Ahi.k`.

Alternatively, choose from the low layer and apply `Ahi.isGreatest_strictInteriorPairFiber`; use whichever elaborates more cleanly.

Then split:

```lean
Alo.k = Ahi.k
```

or

```lean
Alo.k < Ahi.k.
```

Do not hide this split behind a newly invented state structure unless a genuine reusable abstraction emerges from the live code. A direct theorem/case split is preferable.

---

## 8. Remaining branch A: equal fibre / one-fibre impossibility — OPEN

The equal-fibre case already has the difficult coupling and degree restriction. What remains is to turn the three alternatives

```text
j + 2 = k
j + 1 = k
j     = k
```

into contradictions.

### Use the verified nonunit implementation as the template

Open these files first:

```text
...PrVGreaterOneFiniteStaircaseOneFiberImpossible.lean
...PrVGreaterOneFiniteStaircaseOneFiberLowerImpossible.lean
...PrVGreaterOneFiniteStaircaseOneFiberMiddleImpossible.lean
...PrVGreaterOneFiniteStaircaseOneFiberUpperImpossible.lean
```

The nonunit dispatcher is:

```lean
QsOtherFacetPrLeftVContactFrontierData.oneFiber_impossible
```

It consumes the nonunit degree trichotomy and dispatches to the three diagonal contradictions.

The lower nonunit theorem is:

```lean
QsOtherFacetPrLeftVContactFrontierData.oneFiber_lowerDiagonal_impossible
```

with assumption corresponding to

```lean
Alo.j + 2 = Alo.k.
```

The middle theorem is:

```lean
QsOtherFacetPrLeftVContactFrontierData.oneFiber_middleDiagonal_impossible
```

with assumption corresponding to

```lean
Alo.j + 1 = Alo.k.
```

Fetch the live upper theorem name before writing the unit port rather than guessing it from this document.

### Expected character of the port

The nonunit diagonal proofs reconstruct literal terminal/source exponents and nonzero source coefficients and then apply state-free polynomial/Hessian identities. The unit branch now exposes the same source-honest affine data.

Therefore first determine which parts of the three nonunit proofs are actually independent of `1 < V` and can be factored or specialized. Prefer, in order:

```text
reuse existing state-free theorem
> add thin unit wrapper
> factor common generic algebra
> duplicate a whole proof only as last resort.
```

Do **not** assume the port is automatic until Lean accepts it. This is the first remaining point that may still contain genuinely unit-specific algebra.

Acceptance condition for branch A:

```lean
unit oneFiber_impossible:
  Alo.k = Ahi.k -> False
```

under the existing strict-interior/source hypotheses.

---

## 9. Remaining branch B: strict separation / multi-fibre impossibility — OPEN

If the selected extrema do not coincide, the new least/greatest theorems should give

```lean
Alo.k < Ahi.k.
```

This is the unit multi-fibre branch.

### Nonunit reference machinery

Start from live files in the verified nonunit finite-staircase chain, especially:

```text
...PrVGreaterOneFiniteStaircaseMultiFiberExtrema.lean
...PrVGreaterOneFiniteStaircaseDualExtrema.lean
```

and then follow their imports into the cross-roof / exposed-roof contradiction modules used by

```text
...PrVGreaterOneFiniteStaircaseClosure.lean.
```

Search the repository before creating any new generic helper. The nonunit chain already contains source-carrier reconstruction lemmas such as the fibre tail/top exponent and coefficient nonvanishing results.

Known nonunit helper names include:

```lean
prLeftV_fiber_tailExponent_mem_carrier
prLeftV_fiber_tail_coeff_source_ne_zero
prLeftV_fiber_topExponent_mem_carrier
```

There are further helpers later in the same files; discover their exact current signatures from the live branch.

### Unit simplification

Here the quotient parameter is fixed at `1`. That should remove some of the arithmetic burden rather than add it. The unit selectors already provide:

- exact source fibres;
- strict interior inequalities;
- least/greatest extremality;
- exact affine coordinates;
- literal source coefficients.

Use those facts directly. Preserve source provenance all the way to the terminal Hessian/cross-roof contradiction.

Acceptance condition for branch B:

```lean
Alo.k < Ahi.k -> False
```

under the existing strict-interior/source hypotheses.

---

## 10. Package unit finite-staircase closure

Once branches A and B are closed, write the unit analogue of the nonunit finite-staircase closure.

The intended proof skeleton is now simple:

```text
assume strict interior survives
  -> build Alo from locked/contact first positive layer
  -> build Ahi from pair-Rees first positive layer
  -> prove Alo.k <= Ahi.k from extrema
  -> by_cases Alo.k = Ahi.k
       equal:
         oneFiber_impossible
       unequal:
         Alo.k < Ahi.k
         multiFiber_impossible
  -> contradiction
```

This should establish that the left unit contact frontier cannot have surviving strict-interior support.

Then use the already-verified endpoint/no-interior machinery to collapse the remaining unit carrier.

### Right orientation

The unit contact frontier has a transverse-swapped right orientation. Existing endpoint transport/mirror machinery is already present and the right endpoint-only branch was previously certified.

Before writing a second full proof, inspect the live permutation/transport declarations. The expected strategy is a thin coordinate-swap transport of the left unit closure. Only build a separate right proof if Lean reveals a genuine asymmetry.

---

## 11. Close `.pr` and then stop doing local algebra

Once the unit quotient is impossible (unless rank-two geometry has already appeared), return to

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly.lean
```

and strengthen/add the parent theorem so the live unit disjunct is gone.

Conceptually:

```text
pr_nontrivial_after_nonunit_closure
  : unit quotient OR rank-two chart

+ unit finite-staircase/endpoint closure

=> rank-two chart / desired contradiction only.
```

At that point, **do not invent another `.pr` subcase**. The local `.pr` mathematics should be finished.

---

## 12. `.sp` / `.rq` and final A19/global splice

After `.pr` closes, inspect the existing cyclic/permutation covariance machinery and transport the result to `.sp` and `.rq`. These faces were never intended to receive three separately developed finite-staircase theories.

Then splice the resulting other-facet contradiction/rank-two exit into the existing strict-low/A19 terminal assembly.

The expected remaining global path is:

```text
.pr unit closure
  -> .pr nontrivial closure
  -> .sp/.rq by existing coordinate transport
  -> other-facet branch impossible / rank-two exit
  -> existing strict-low/A19 assembly
  -> existing presented-terminal / global termination resolver
  -> unrestricted HC4 public/root theorem
  -> full root certification
```

A large amount of A16/A17/A18/A19 machinery is already green. Search for the existing parent theorems before adding any new global object.

---

## 13. Things explicitly NOT to do

### Do not collapse to generic JC2

A generic two-zero projection is full JC2, but the live branch retains much stronger source/contact/ray provenance. The current finite-staircase route was built precisely to exploit that information.

### Do not identify auxiliary clocks

In particular:

```text
auxiliary Rees/ray clock != zero-defect blocker clock
```

unless a theorem explicitly proves the relation needed in context.

### Do not infer superface singularity from a smaller ray

This shortcut was rejected earlier. Carry the actual source geometry.

### Do not use repair-only progress as contradiction

A restart/descent object marked only by repair is not itself a mathematical contradiction.

### Do not revive the generic stationary source/profile determinant bridge

The generic bridge was shown false in the required generality. The current source-honest finite-staircase route replaces it.

### Do not use first variation alone to claim degree <= 1

That shortcut has a counterexample and is documented in

```text
A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md.
```

The valid equal-fibre degree control is the compiled affine-two-root trichotomy described above.

### Do not invent handoff-only declarations

In particular, old planning names such as

```text
ATwoFibreState
WalkerData
```

are not a license to add duplicate infrastructure. Search the live declarations first. Prefer the existing finite-staircase/extrema packages.

### Do not rewrite documentation before the mathematical chain is green

This handoff is enough for the last sprint. Finish the Lean route first; refresh the broader `CURRENT_STATE` / architecture ledgers only after the actual final path compiles.

---

## 14. Recommended implementation order

Use small, compiler-driven commits.

### Commit U1 — selector-order split

Add the thin theorem proving

```text
Alo.k <= Ahi.k
```

and package the equal/strict split if useful.

### Commit U2 — unit lower diagonal

Port/factor the `j + 2 = k` one-fibre contradiction.

### Commit U3 — unit middle diagonal

Port/factor the `j + 1 = k` contradiction.

### Commit U4 — unit upper diagonal

Port/factor the `j = k` contradiction.

### Commit U5 — unit one-fibre dispatcher

Consume

```lean
oneFiber_degree_trichotomy
```

and close `Alo.k = Ahi.k`.

If U2–U4 factor into a single clean generic theorem, combine them; do not force artificial commit boundaries.

### Commit U6 — unit multi-fibre extrema/cross-roof adapter

Port/specialize the nonunit multi-fibre source reconstruction and contradiction to `V = 1`.

### Commit U7 — unit finite-staircase closure

Equal-vs-strict split, no surviving strict interior.

### Commit U8 — unit endpoint/no-interior closure + right mirror

Reuse existing endpoint-only and permutation machinery.

### Commit U9 — `.pr` parent splice

Eliminate the live unit quotient disjunct from `pr_nontrivial_after_nonunit_closure` or add the next theorem directly above it.

### Commit U10 — `.sp/.rq`, other-facet, A19/global splice

Use existing transports and parent assembly.

### Final certification

Run/check:

```text
root Build HC4
Axiom audit
Proof-complete branch negative control
Escape-hatch audit
```

Only a full passing exact-head certification authorizes the statement **unrestricted HC4 is LEAN VERIFIED**.

---

## 15. CI protocol for the final sprint

There is no reason to accumulate a large uncompiled patch now.

For each substantive step:

1. re-pin PR #34 head;
2. search/fetch the exact declarations being reused;
3. make the smallest coherent source change;
4. push it;
5. classify it **SOURCE-LANDED / NOT LEAN VERIFIED** while CI is pending;
6. if CI fails, inspect the exact failing file/line and repair in place;
7. only after the complete certification run passes mark it **LEAN VERIFIED**;
8. continue immediately to the next mathematical seam.

Generated-inventory commits may appear after code commits. Always distinguish the substantive code commit from a bot-generated child when quoting the certified proof state.

---

## 16. Fresh-context opening checklist

A new session should do these things in order:

```text
[ ] Read this file completely.
[ ] Pin PR #34 and current branch head.
[ ] Confirm certified code checkpoint e2783035171d173516a33448615f6cccd4ec9feb.
[ ] Confirm CI run 35237635579 is the complete green certification for that code checkpoint.
[ ] Open the four certified unit finite-staircase files:
      - ...PrUnitFiniteStaircaseOneFiber.lean
      - ...PrUnitFiniteStaircaseEndpointEuler.lean
      - ...PrUnitFiniteStaircaseOneFiberDegree.lean
      - ...PrUnitFiniteStaircaseExtrema.lean
[ ] Open the nonunit one-fibre impossible dispatcher and lower/middle/upper files.
[ ] Open nonunit MultiFiberExtrema / DualExtrema and follow the live closure imports.
[ ] Search before adding any generic helper.
[ ] Implement selector ordering first.
[ ] Close equal-k one-fibre case.
[ ] Close strict-k multi-fibre case.
[ ] Package unit finite-staircase closure.
[ ] Reuse endpoint/right-mirror machinery.
[ ] Splice .pr -> .sp/.rq -> A19/global.
[ ] Run exact-head full certification before claiming HC4.
```

---

## 17. Suggested prompt for the next fresh context

> Continue unrestricted HC4 from `docs/HANDOFF_2026-09-17_HC4_UNIT_FINITE_STAIRCASE_FINAL_CLOSURE.md` on PR #34. Re-pin the current branch first and distinguish the live head from the certified code checkpoint `e2783035171d173516a33448615f6cccd4ec9feb` (Lean CI `35237635579`). Treat only claims in that certified build as LEAN VERIFIED. Start from the new unit finite-staircase one-fibre/dual-Euler/degree/extrema infrastructure. First prove the selector ordering `Alo.k <= Ahi.k`; then eliminate the equal-k case by porting/factoring the verified nonunit lower/middle/upper one-fibre contradictions, and eliminate the strict-k case using the verified nonunit multi-fibre extrema/cross-roof chain specialized to `V = 1`. Package the unit finite-staircase closure, reuse the existing endpoint/right-mirror machinery, splice it into `.pr`, transport to `.sp/.rq`, and continue through the existing A19/global assembly. Search live declarations before adding infrastructure, preserve source/contact provenance, do not collapse to JC2, do not identify auxiliary clocks, and use GitHub CI as the compiler. Continue through plumbing-only commits rather than stopping after them.

---

## 18. Bottom line

At the certified checkpoint `e2783035171d173516a33448615f6cccd4ec9feb`, the unit branch has already crossed the difficult conceptual bridge:

```text
two different source-honest selectors
        -> exact least/greatest interior fibres
        -> same-fibre literal layer/profile identity
        -> same nonzero profile satisfies both endpoint Euler laws
        -> three-case degree trichotomy.
```

What remains is no longer an open-ended search for the shape of the proof. It is a finite closure programme against an already-verified nonunit template:

```text
three equal-fibre diagonals
+ one strict multi-fibre branch
+ endpoint/transport/parent splices.
```

That is the correct final-sprint target. It is still **not yet a claim that unrestricted HC4 is proved**, but the remaining local mathematical frontier is now sharply isolated and backed by a large amount of certified reusable infrastructure.
