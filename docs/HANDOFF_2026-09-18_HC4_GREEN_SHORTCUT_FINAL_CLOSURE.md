# HC4 unrestricted closure — green shortcut final-closure handoff

**Date:** 18 September 2026  
**Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`  
**PR:** #34 — `A18.4.42 collapse final termination frontier`  
**Branch:** `final-assembly/a18-4-42-termination-frontier`  
**Certified source checkpoint:** `3de2689ad2b50003deab6433e1b521be259e6622`  
**Exact-head Lean CI:** run `35399193381` / workflow run **#3146** — **SUCCESS**  
**Certified gates:** full `Build HC4`, theorem axiom audit, negative control, and proof escape-hatch audit all passed.

This handoff supersedes:

- `HANDOFF_2026-09-18_HC4_FIRST_DEFICIT_STAGGERED_BREAK.md` as the live continuation point;
- `HANDOFF_2026-09-17_HC4_FINAL_GLOBAL_ASSEMBLY.md` as the live global-close plan.

Those documents remain useful provenance, but both now miss important source-lift and shortcut work that is **LEAN VERIFIED** at the checkpoint above.

---

## 1. Status vocabulary

Use these labels literally.

- **LEAN VERIFIED** — the theorem/module is rooted into the current build graph where relevant and accepted by the successful exact-head CI above.
- **SOURCE-LANDED / UNROOTED** — source exists but is intentionally not on the current unrestricted-HC4 root path.
- **PAPER CANDIDATE** — mathematical argument exists but has not been formalised.
- **DIAGNOSTIC ONLY** — symbolic/counterexample evidence, not a proof theorem.
- **OPEN** — a genuine mathematical/formal/assembly obligation remains.

Do not use “green” for a paper argument or merely source-landed code.

---

## 2. Public target and preferred final reducer

The public target remains:

```lean
F : MvPolynomial (Fin 4) K
hdet : HC4.Polynomial.hessianDeterminant F = 1
⊢ Function.Injective (mvGradientMap F)
```

under:

```lean
[K : Type u] [Field K] [CharZero K] [IsAlgClosed K]
```

The preferred final reduction is already **LEAN VERIFIED**:

```lean
gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
```

in:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean
```

It is enough to prove:

```lean
∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
  state.repair = rankOneRepairState 0 →
  AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
    canonicalAdaptiveAlignedSmithRepairRanking state 0 →
  False
```

This is the **final logical obligation**.  Prefer this repair-aware reachable-terminal theorem over older stronger APIs that quantify over arbitrary synthetic terminals.

---

## 3. Exact current status in one paragraph

At the certified head, the unrestricted proof is **not yet closed**, but the local strict-low geometry is substantially further than the previous handoff recorded.

The current root now contains:

1. the source-honest first-deficit / staggered interaction chain;
2. the cyclic `.qs -> other facet` source-pivot shortcut;
3. a `.qs` rank-three closure which reduces its lower-ray branch to actual rank-two geometry, an endpoint first-break packet, or a literal quadratic square;
4. a new generic reverse-Rees principal-Hessian-minor covariance/lift;
5. a new endpoint first-break source lift which already turns every **whole-family** first-break minor into an actual represented-source rank-two Hessian chart.

The endpoint source lift leaves exactly one honest auxiliary subcase:

```lean
LayerMinorAtFirstBreak
```

where the nonzero principal minor exists only inside the exact breaking parameter layer.

However, a crucial architectural observation changes the recommended order of attack:

> raw defect zero already has generic exact-active and complete rank-three Hessian geometry in A18.4.104, even without the new `.qs` source-pivot work.

Therefore **do not assume that converting every local branch into an `ActualRankTwoHessianChart` automatically proves terminal impossibility**.  The first task in a fresh context should be to audit the **terminal-facing consumer** of actual/exact-active rank-three geometry.  If that consumer already exists, most remaining local geometry may collapse immediately.  If it does not exist, that missing terminal adapter is the true endgame theorem.

---

## 4. Certification checkpoint

At commit:

```text
3de2689ad2b50003deab6433e1b521be259e6622
```

workflow run:

```text
35399193381 / #3146
```

passed all of:

```text
Build HC4                              PASS
Audit theorem axioms                   PASS
Check negative control is rejected     PASS
Reject proof escape hatches            PASS
```

This is the new base checkpoint for further work.

Do not start by repairing old logs from earlier red commits; they have been superseded.

---

## 5. Recent commit audit

The late 18 September sequence is important because it changes the live route.

### 5.1 Reverse-Rees whole-family Hessian-minor lift

```text
95897906ce729581eb3596ce01dcc6a98602f1d3
    lift reverse-Rees family Hessian minors to source

d807082b5963a6ce86c8817ff11d691fd0e6c55b
    root reverse-Rees Hessian minor lift

170d64f071971c1b475cac77c85958c7373c8a77
    normalize reverse-Rees minor comparison before rewriting
```

File:

```text
HC4/Valuation/ReverseWeightedReesHessianPrincipalMinor.lean
```

Key **LEAN VERIFIED** theorem:

```lean
reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
```

and the covariance lemmas:

```lean
hessianPrincipalMinor_adaptiveSmithInflateHom
hessianPrincipalMinor_C_mul
hessianPrincipalMinor_constantPolynomialFamily
```

This is an important generic reusable theorem.  It proves:

```text
nonzero whole-family principal Hessian minor
of honest bounded reverse Rees
        ->
nonzero principal Hessian minor
of represented source.
```

It deliberately does **not** claim the same for a principal minor built only from one parameter layer.

### 5.2 Endpoint first-break source lift

```text
f6500c384b05d845e480974c7a69c4d8625930b3
    lift endpoint first-break family minors to source

7abce59c08340a31414e99bd60df43eb078f5e29
    root endpoint first-break source lift

81005cfb283e4ca6d4986e4f80269983592fabac
    simplify endpoint first-break source lift

3de2689ad2b50003deab6433e1b521be259e6622
    repair endpoint first-break source lift elaboration
```

File:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointFirstBreakSourceLift.lean
```

Key **LEAN VERIFIED** definitions/theorems:

```lean
LayerMinorAtFirstBreak
actualRankTwo_or_layerMinor
```

The theorem now proves:

```text
endpoint first-break
    ->
actual represented-source rank-two chart
OR
exact breaking-layer principal minor.
```

The `familyMinor` constructor of
`RankOneSpecialFiberFirstBreakOutcome` is fully consumed.

Only the `layerMinor` constructor remains.

### 5.3 The speculative reflected second-source recurrence was intentionally removed from the root

Relevant commits:

```text
ce834f42940df2bd9fd1c33cce0857728df301a7
    prove exact reflected second deficit layer

5245fb12417848e689fc314d645058dc398b5a87
    unroot speculative second-source recurrence from HC4 closure
```

The first-deficit / second-interaction core remains useful verified infrastructure, but the experimental reflected-recurrence extension is not the current unrestricted-HC4 route.

The current `HC4.lean` comment is authoritative:

```text
The experimental FirstDeficitSecondSourceLayer/reflected-recurrence module is
intentionally unrooted here.  The source-pivot/QsRankTwoClosure route below
supersedes it for unrestricted HC4.
```

Do not restart the recurrence unless the source-pivot route fails for a precise reason.

---

## 6. Current rooted shortcut chain

### 6.1 Cyclic other-facet source-pivot closure — LEAN VERIFIED

Files:

```text
...OtherFacetActualRankTwo.lean
...OtherFacetActualRankTwoClosure.lean
```

Key theorem:

```lean
qs_ray_otherFacet_actualRankTwoHessianChart
```

For a lower ray beginning on `.qs`, any actual rank-three outside endpoint on:

```text
.pr
.sp
.rq
```

already lifts by source Schur + reverse-Rees initial-form transport to an actual principal Hessian minor of the represented source, and is packaged as:

```lean
AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
```

This bypasses the old heavy planar/highest-slice `.pr` analysis for this purpose.

### 6.2 `.qs` rank-three closure — LEAN VERIFIED

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowQsRankTwoClosure.lean
```

The rooted theorem:

```lean
qs_rankThree_rankTwoClosure
```

returns:

```lean
inductive QsRankThreeRankTwoClosure
  | actualRankTwo ...
  | facetEndpointFirstBreak ...
  | quadraticSquare ...
```

So every exposed `.qs` rank-three strict-low branch is now:

```text
actual represented-source rank-two chart
OR
pure facet-endpoint reverse-Rees first break
OR
literal x0^2 source term.
```

### 6.3 Endpoint first-break source lift — LEAN VERIFIED

For:

```text
facetEndpointFirstBreak D
```

the new rooted theorem gives:

```text
actualRankTwo
OR
D.LayerMinorAtFirstBreak.
```

Thus the only unresolved endpoint-first-break subcase is now the exact-layer minor.

### 6.4 Literal square already has source codimension-two provenance — LEAN VERIFIED

File:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowQsSquareCodimensionTwo.lean
```

The theorem:

```lean
qs_quadraticSquare_source_codimensionTwo
```

proves the literal `x0^2` source term is a genuine supported codimension-two exponent.

Important: this is **not yet** a full codimension-two carrier or a terminal contradiction.  Do not silently feed one supported exponent into a theorem requiring an exposed/canonical codimension-two face.

---

## 7. Generic raw-zero rank geometry already exists

This point is easy to miss and is strategically important.

### 7.1 Exact active chart at raw defect zero — LEAN VERIFIED

File:

```text
AdaptiveAlignedSmithCanonicalZeroDefectRankThree.lean
```

Key theorem:

```lean
ScaleAwareAdaptiveGeometricRestartState.zeroDefect_exactActiveFourBlock
```

Every raw-defect-zero state already has:

```lean
Nonempty (AdaptiveAlignedSmithCanonicalExactActiveFourBlock s)
```

The chart may be a coordinate-permuted chart or an explicit determinant-one shear chart.

### 7.2 Complete rank-three geometry — LEAN VERIFIED

Key theorem:

```lean
ScaleAwareAdaptiveGeometricRestartState.zeroDefect_completeRankThreeGeometry
```

and:

```lean
AdaptiveAlignedSmithCanonicalExactActiveFourBlock.rankThreeGeometry
```

The exact active block is exhausted into:

```text
constant nonzero actual 3x3 minor
OR
exact zero-Schur source-valued rank-three geometry.
```

Similarly, an older direct `ActualRankTwoHessianChart` has:

```lean
AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart.rankThreeGeometry
```

### 7.3 Why this does not yet prove HC4

These are geometry packages, not terminal contradictions.

The rank-three geometry currently retains:

- actual nonzero `3 x 3` Hessian events;
- zero-Schur nondegenerate/projective exits;
- finite repair progress `rankTwo -> rankThree`.

But there is no currently identified theorem of the form:

```lean
AdaptiveAlignedSmithCanonicalActualRankThreeGeometry ... -> False
```

or:

```lean
AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry ... ->
AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData
```

Therefore the **first task of the next chat is to search for or construct this terminal-facing consumer**.

This audit should happen before further local branch multiplication.

---

## 8. The genuine terminal contradiction interface

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalTerminalImpossible.lean
```

The already-closed RationalRigidity endgame consumes:

```lean
AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData
```

whose substantive fields are:

```text
positive balance weights a,b
actual rank-three exponent-line support
start endpoint coefficient nonzero
end endpoint coefficient nonzero
Hessian determinant zero.
```

Then:

```lean
AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData.impossible
```

gives `False`.

The trace-facing theorem:

```lean
AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.
  terminal_impossible_of_supportedBalancedRankThree
```

is also already present.

### Important implication

The final missing assembly is not “find some rank-two minor.”

It is one of:

1. turn the retained strict-low/rank-three geometry into the exact balanced rank-three-line data above; or
2. derive another honest terminal contradiction / globally recursive successor that is strong enough to replace this interface.

This is the central decision gate for the fresh context.

---

## 9. Global progress: useful but not itself the terminal contradiction

The following are **LEAN VERIFIED**:

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData.exists_globalProgress

AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress

AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress_from_source
```

Files:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowGlobalProgress.lean
AdaptiveAlignedSmithCanonicalRankOneReesGlobalDescent.lean
```

These are honest geometry-backed global macro progress theorems.

But the normalized presented rank-three terminal:

```lean
AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
```

does **not** itself contain a no-successor hypothesis.

Therefore do not argue:

```text
terminal
+ exists global progress
= contradiction
```

unless a genuine global no-successor/minimality certificate has first been produced.

The theorem:

```lean
impossible_of_no_globalProgress
```

is valid only when the caller supplies:

```lean
∀ target, ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state
```

No such certificate is currently part of the reachable presented terminal interface.

---

## 10. Fastest recommended route from the certified head

### STEP 0 — audit the terminal-facing rank-three consumer first

Before writing new algebra, search the current branch for consumers of:

```lean
AdaptiveAlignedSmithCanonicalActualRankThreeGeometry
AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry
AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
AdaptiveAlignedSmithCanonicalThreeByThreeMinorGeometry
```

Target outputs to search for:

```lean
False

AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData

AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal -> False

a fresh rankOneRepairState 0 source with honest counterexample provenance
```

If a consumer already exists but is unrooted, root it and use it.

If not, decide whether the missing adapter can be proved directly from the retained terminal first-contact geometry.

**Do this before closing more local rank-two branches.**

Reason: raw defect zero already gives exact-active rank-three geometry generically.  If exact-active rank-three geometry can close the terminal, the entire `.qs` layer-minor/quadratic-square cleanup becomes unnecessary for unrestricted HC4.

### STEP 1 — if no generic terminal consumer exists, close `LayerMinorAtFirstBreak`

This is the smallest concrete local obligation now isolated.

Suggested generic theorem location:

```text
HC4/Valuation/ReverseWeightedReesHessianPrincipalMinor.lean
```

Suggested theorem shape:

```lean
reverseWeightedReesFamily_sourceMinor_of_parameterLayerMinor_ne_zero
```

with the logical content:

```text
nonzero principal Hessian minor of exact parameter layer n
of bounded reverse Rees
        ->
nonzero principal Hessian minor of represented source.
```

#### Recommended proof

Let:

```text
Q = reverseWeightedReesFamily w D F hbound.
```

The library already proves coefficientwise:

```lean
reverseWeightedReesFamily_parameterLayer_coeff
```

namely:

```text
[d] layer_n(Q)
=
[d] F
iff
d in support(F) and D - weight(d) = n.
```

Use this to prove an exact layer/initial-form identity at level:

```text
D - n.
```

The desired bridge should be coefficientwise:

```text
familyParameterLayer Q n
=
initialForm (fun i => (w i : Z)) (D - n) F
```

under the appropriate nonempty/`n <= D` hypothesis.

Do not assume `n <= D` abstractly.  Derive it from nonvanishing of the layer/minor if needed.

Then:

1. rewrite the `LayerMinorAtFirstBreak` expression as the genuine
   `hessianPrincipalMinor` of that exact layer;
2. rewrite the layer as the weighted initial form;
3. apply the already-existing weighted-initial-form lift:
   ```lean
   hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
   ```
4. package the resulting source minor into an
   ```lean
   AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
   ```
   using the same permutation helpers already written in
   `EndpointFirstBreakSourceLift.lean`.

Acceptance theorem:

```lean
QsRayFacetEndpointFirstBreakData.actualRankTwoHessianChart
```

or:

```lean
Nonempty (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart ...)
```

with **no residual `LayerMinorAtFirstBreak` constructor**.

### STEP 2 — collapse the `.qs` endpoint-first-break constructor

Strengthen or add a thin theorem above:

```lean
qs_rankThree_rankTwoClosure
```

so the former:

```text
facetEndpointFirstBreak
```

constructor is consumed entirely.

The `.qs` frontier then becomes:

```text
actualRankTwo
OR
quadraticSquare.
```

Do not reopen the old nontrivial `.pr` staircase analysis.

### STEP 3 — decide whether the quadratic-square branch still matters

If STEP 0 produced a terminal consumer for generic exact-active/rank-three geometry, stop local work: the square branch is irrelevant to unrestricted HC4.

Otherwise the current verified fact is only:

```lean
qs_quadraticSquare_source_codimensionTwo
```

Do **not** identify one supported codimension-two exponent with the canonical exposed codimension-two carrier.

Preferred order:

1. look for a direct source-Hessian/terminal contradiction from the literal `x0^2` term;
2. only if necessary, build the honest two-zero carrier required by existing codimension-two machinery;
3. do not project to generic planar JC2.

### STEP 4 — audit non-`.qs` starting facets only if still necessary

The exposed strict-low boundary rank-three facet is genuinely arbitrary in the current generic frontier.

The `.qs` route is the most developed, but no theorem currently says all strict-low terminals start on `.qs`.

The existing confinement classification gives:

```text
pure longitudinal:
    confinement facet in {pr, sp, rq}

low-negative-first:
    confinement facet in {pr, rq}

low-negative-second:
    confinement facet in {sp, rq}
```

and excludes complete confinement to `.qs`.

There is polynomial-level coordinate-permutation infrastructure:

```text
HC4/Newton/TerminalCoordinatePermutation.lean
```

including Hessian determinant covariance and gradient injectivity invariance.

However it does **not currently transport the entire strict-low Smith terminal package**.

Therefore:

- first see whether the terminal consumer from STEP 0 is coordinate-free;
- if it is, avoid facet-specific duplication;
- if not, audit whether a whole-terminal permutation adapter is cheaper than separate `.pr/.sp/.rq` proofs;
- do not locally rename only the carrier while keeping the original strict-low/Smith provenance.

### STEP 5 — prove the reachable presented terminal impossible

Once the actual terminal contradiction is available, add the theorem:

```lean
theorem reachablePresentedTerminal_impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hrepair : state.repair = rankOneRepairState 0)
    (T :
      AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0) :
    False := by
  ...
```

Prefer to put this in a final assembly module rather than overloading
`AdaptiveAlignedSmithCanonicalTerminalImpossible.lean`.

### STEP 6 — expose unrestricted HC4

Then:

```lean
theorem gradient_injective_of_hessianDeterminant_one
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
      F hdet reachablePresentedTerminal_impossible
```

Root it in `HC4.lean`.

Run the complete gate:

```text
lake build
axiom audit
negative control
escape-hatch audit
#check / #print axioms of exact public theorem
```

Only then claim unrestricted HC4 is formalised.

---

## 11. Why the old first-deficit reflected recurrence is not the preferred path

The current root intentionally leaves:

```text
...FirstDeficitSecondSourceLayer
```

unrooted.

The verified second-interaction theorem remains useful:

```text
first deficit q
-> primitive opposite opening j
-> forced second kernel interaction
```

but the reflected-source recurrence adds another Hessian/source identification not supplied by the verified interface.

Meanwhile the newer source-pivot / endpoint reverse-Rees lift already converts large parts of the lower-boundary geometry directly into represented-source Hessian minors.

Therefore:

- do not continue the reflected recurrence merely because it is mathematically interesting;
- reopen it only if the source-pivot route reaches a precise obstruction that the recurrence resolves.

---

## 12. Known dead ends / hard prohibitions

These remain binding.

### Do not identify clocks

The following are distinct unless a theorem explicitly equates them:

- raw Hessian defect;
- Smith/blocker clock;
- auxiliary ray clock;
- central total-deficit reverse-Rees order;
- endpoint reverse-Rees order;
- first kernel-break order.

### Do not use naked repair relabelling as progress

`withRepairOnly` alone is bookkeeping, not geometry.

### Do not revive the generic stationary source/profile determinant implication

It is false in the previously attempted generality.

### Do not revive the generic degree-`<=1` shortcut

The known `phi = (5+4T)^2` counterexample remains relevant.

### Do not declare a sparse deleted subpolynomial singular

Use an honest initial form, exact Rees layer, determinant coefficient, or another certified source operation.

### Do not collapse the strict-low endgame to generic JC2

The whole point of the current route is to retain stronger source/contact/ray provenance.

### Do not treat `ActualRankTwoHessianChart` or rank-three repair geometry as `False`

They are geometry packages.  A terminal-facing contradiction still needs to be proved or invoked.

---

## 13. Current status table

| Component | Status | Notes |
|---|---|---|
| Public repair-aware HC4 reducer | **LEAN VERIFIED** | `gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible` |
| Raw-zero exact active chart | **LEAN VERIFIED** | generic, may include shear |
| Raw-zero complete rank-three geometry | **LEAN VERIFIED** | not by itself a contradiction |
| `.qs -> other facet` source-pivot actual rank-two chart | **LEAN VERIFIED** | cyclic `.pr/.sp/.rq` outside endpoint |
| `.qs` rank-three rank-two closure | **LEAN VERIFIED** | actual rank two / endpoint first break / square |
| Whole-family reverse-Rees principal-minor lift | **LEAN VERIFIED** | generic reusable theorem |
| Endpoint first-break whole-family minor -> source chart | **LEAN VERIFIED** | new late-18-Sep shortcut |
| Endpoint `LayerMinorAtFirstBreak` -> source | **OPEN** | likely exact-layer initial-form lift |
| Literal `x0^2` -> source codimension-two exponent | **LEAN VERIFIED** | not yet a full carrier/contradiction |
| Generic terminal-facing consumer of actual/exact-active rank-three geometry | **OPEN / MUST AUDIT FIRST** | likely true critical decision point |
| Arbitrary starting-facet terminal reduction | **OPEN** | do not assume `.qs` without proof |
| Reachable presented terminal impossible | **OPEN** | final logical theorem |
| Public unrestricted HC4 theorem | **OPEN** | follows immediately once previous row is green |
| Reflected second-source recurrence extension | **SOURCE-LANDED / UNROOTED** | superseded for current route |

---

## 14. First actions for the next fresh chat

The fresh chat should start with exactly this instruction:

```text
Continue unrestricted HC4 closure from
docs/HANDOFF_2026-09-18_HC4_GREEN_SHORTCUT_FINAL_CLOSURE.md
on PR #34.

Re-audit the live PR head and exact-head CI first.

Do not reopen the reflected first-deficit recurrence unless the rooted
source-pivot route fails for a precise reason.

First search for an existing terminal-facing consumer of
AdaptiveAlignedSmithCanonicalActualRankThreeGeometry /
AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry /
AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry.

If none exists, decide whether that consumer is the true next theorem.
Only then continue the local fallback:
close LayerMinorAtFirstBreak by identifying the exact bounded reverse-Rees
parameter layer with a weighted initial form and lifting its nonzero Hessian
principal minor back to the represented source.
Distinguish LEAN VERIFIED / SOURCE-LANDED / OPEN throughout.
```

Then inspect, in this order:

```text
1. HC4/Valuation/AdaptiveAlignedSmithCanonicalTerminalImpossible.lean
2. HC4/Valuation/AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree.lean
3. HC4/Valuation/AdaptiveAlignedSmithCanonicalExactActiveFourBlockRankThree.lean
4. HC4/Valuation/AdaptiveAlignedSmithCanonicalSourceZeroSchurRankThree.lean
5. HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowQsRankTwoClosure.lean
6. HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointFirstBreakSourceLift.lean
7. HC4/Valuation/ReverseWeightedReesHessianPrincipalMinor.lean
8. HC4/Valuation/BoundedReverseWeightedRees.lean
9. HC4/Valuation/WeightedHessianPrincipalMinorInitial.lean
10. HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean
```

Do not begin by updating broad documentation again.  Get the next endgame theorem green first.

---

## 15. Definition of success

The project has reached unrestricted HC4 only when all of the following hold at one exact commit:

1. there is a theorem ruling out every **reachable** complexity-zero presented rank-three terminal under inherited `rankOneRepairState 0`;
2. the repair-aware public reducer is instantiated with that theorem;
3. the resulting determinant-one gradient-injectivity theorem is rooted;
4. the full Lean build passes;
5. axiom audit passes;
6. negative control is rejected;
7. escape-hatch audit passes;
8. the exact public theorem has only the expected foundational axioms.

Until then, describe the status as “final terminal closure in progress,” not “HC4 proved.”

---

## 16. One-line current conclusion

At the certified 18 September checkpoint:

> the source-pivot shortcut is real and green, whole-family endpoint first-break minors now lift back to actual source rank-two charts, and the local endpoint residue has collapsed to one exact-layer minor case.  But generic raw-zero rank-two/rank-three geometry already existed, so the fastest remaining route is to identify or build the **terminal-facing consumer** of that geometry first.  If no such consumer exists, close `LayerMinorAtFirstBreak` by exact-layer weighted-initial-form transport, finish the `.qs` frontier, then assemble the remaining facet/terminal cases into the already-verified reachable-terminal HC4 reducer.
