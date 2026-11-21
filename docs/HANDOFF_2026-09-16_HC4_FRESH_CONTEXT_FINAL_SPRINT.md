# HC4 unrestricted closure — fresh-context final sprint handoff

**Date:** 16 September 2026  
**Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`  
**PR:** `#34` — `A18.4.42 collapse final termination frontier`  
**Branch:** `final-assembly/a18-4-42-termination-frontier`

This is the **authoritative continuation document for a fresh chat/context window**.
It supersedes `HANDOFF_2026-09-16_HC4_LAST_MILE_PUBLIC_CLOSURE.md` for live status and TODO order, while that older handoff remains important provenance for the finite-staircase work and failed routes.

The project is genuinely in the final local-closure/assembly phase, but this document deliberately does **not** claim unrestricted HC4 until the public theorem is assembled and the full root certification passes.

---

## 0. Fresh-session operating instructions

A new session should do the following before changing code:

1. Read this document in full.
2. Fetch PR #34 and pin the **current live head SHA**. GitHub Actions may have added a generated proof-inventory commit after the certified code commit.
3. Do **not** reopen the frozen green endpoints or singleton theorem except to inspect their interfaces.
4. Start with:
   - the **boundary-singleton adapter**, then
   - the **unit strict-interior elimination**.
5. Search the existing source for the finite-staircase / `ATwoFibreState` machinery before adding any new global structure.
6. Preserve source/contact/ray provenance throughout.
7. Do not clone `.pr` arguments for `.sp`/`.rq`; use the repository's permutation covariance.
8. Make actual Lean changes and commits. Do not stop at a paper plan if the existing interfaces are sufficient to implement.
9. Use **LEAN VERIFIED** only after the relevant root `Lean CI` run has passed:
   - `Build HC4`,
   - theorem-axiom audit,
   - negative-control rejection,
   - proof escape-hatch audit.

If the live head has moved since this handoff, distinguish generated/documentation movement from substantive code movement before deciding that the proof state changed.

---

## 1. Frozen certified checkpoints

### 1.1 Earlier global baseline — LEAN VERIFIED

Certified code checkpoint:

```text
cf53735baedb4555df9d8a1c6c63cef7cc17fdec
```

CI run:

```text
35139954849
```

This passed the full root build, theorem-axiom audit, negative control, and escape-hatch audit.

It already contained the unrestricted entry and rank-one termination architecture, A19.55 same-carrier codimension-two geometry, lower-`.qs` other-facet reduction, source-honest planar/highest-slice stack, both non-unit finite-staircase closures, presented rank-two chart lifting, and the unit endpoint/contact/staircase/pair-Rees infrastructure.

### 1.2 Right endpoint-only `V = 1` mirror — LEAN VERIFIED

Main repair/final code commit:

```text
9db159b2346736518e0c43138feef954cd39c049
```

CI run:

```text
35149023096
```

Main module:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitRightEndpointClosure.lean
```

Key theorem:

```lean
theorem QsOtherFacetPrUnitRightContactFrontierData.impossible_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) : False := by
  ...
```

The proof reconstructs the four-monomial carrier, transports it by the coordinate swap `2 ↔ 3`, applies Hessian rename covariance, and reduces to the already-verified positive-`V` two-function carrier contradiction at `V = 1`.

The repair commit added explicit finite-swap normalization lemmas:

```lean
private theorem swap23_zero :
    (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by decide
private theorem swap23_one :
    (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by decide
private theorem swap23_two :
    (Equiv.swap (2 : Fin 4) 3) 2 = 3 := by decide
private theorem swap23_three :
    (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by decide
```

This branch is frozen. Do not re-prove it by a new staircase calculation.

### 1.3 Interior singleton highest slice exclusion — LEAN VERIFIED

Substantive commit:

```text
8ca83aa9f6e5a8212eda02fe54458aa16984d902
```

Commit message:

```text
A19 close interior singleton highest slice
```

Main module:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarHighestPairSlice.lean
```

Certified CI run:

```text
35154902934
```

The `Build and verify Lean project` job passed all relevant stages:

```text
Regenerate proof inventory for diagnostic build   SUCCESS
Build HC4                                         SUCCESS
Audit theorem axioms                              SUCCESS
Check that the negative control is rejected       SUCCESS
Reject proof escape hatches                       SUCCESS
```

Key theorem:

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.singleton_on_boundary
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {next : ToricFacet} {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    {d : Fin 4 →₀ ℕ}
    (hsupp : S.slice.support = {d}) :
    HC4.Polynomial.MvExponentOnBoundary d := by
  classical
  have hdmem : d ∈ S.slice.support := by
    rw [hsupp]
    simp
  have hc : MvPolynomial.coeff d S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdmem
  have hsum := MvPolynomial.as_sum S.slice
  rw [hsupp] at hsum
  have hmono :
      S.slice = MvPolynomial.monomial d (MvPolynomial.coeff d S.slice) := by
    simpa using hsum
  by_contra hboundary
  have hpos : ∀ i : Fin 4, 0 < d i :=
    HC4.Polynomial.coordinate_pos_of_not_mvExponentOnBoundary hboundary
  have h0 := hpos (0 : Fin 4)
  have h1 := hpos (1 : Fin 4)
  have h2 := hpos (2 : Fin 4)
  have h3 := hpos (3 : Fin 4)
  have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
    simp [HC4.Polynomial.ordinaryDegree4]
    omega
  have hne := HC4.Polynomial.hessianDeterminant_monomial_ne_zero
    hc hpos hdeg
  have hz :
      HC4.Polynomial.hessianDeterminant
        (MvPolynomial.monomial d (MvPolynomial.coeff d S.slice)) = 0 := by
    rw [← hmono]
    exact S.hessian_zero
  exact hne hz
```

Interpretation:

```text
singleton highest slice
        +
all four coordinates positive
        ↓
literal monomial of ordinary degree >= 3
        ↓
hessianDeterminant_monomial_ne_zero
        ↓
contradiction with S.hessian_zero
```

Therefore a singleton highest slice **must omit at least one coordinate**.

Important: this does **not yet mean every singleton branch is eliminated**. It reduces the singleton branch to the existing coordinate-boundary / facet / vertical residue. The next session should wire that residue into the existing machinery rather than redo the monomial argument.

### 1.4 Live branch state at handoff creation

Immediately before this documentation handoff, the PR head was:

```text
d35ab25c62503a8cffd4b91970fca8b4f0aba513
```

That head followed the singleton proof with a generated proof-inventory refresh. Treat `8ca83aa9...` + CI `35154902934` as the certified substantive singleton checkpoint. Re-fetch the PR head at the start of the next session because this documentation commit itself will move it again.

---

## 2. What remains

The shortest remaining proof graph is now:

```text
boundary singleton adapter ─┐
                            ├──> unit strict-interior elimination
finite-staircase machinery ─┘
                 ↓
           complete `.pr`
                 ↓
      `.sp` / `.rq` by permutation
                 ↓
          A19 terminal splice
                 ↓
      presentedTerminal_impossible
                 ↓
        public unrestricted HC4
                 ↓
       full root build + audits
```

The **unit strict-interior elimination** is now the last clearly substantive local mathematical/formal branch. After it, the expected work is mostly parent assembly, symmetry transport, and connection to the already-existing unrestricted terminal reduction. Lean may expose adapter obligations, but no new global theory should be introduced without a concrete interface obstruction.

---

## 3. Immediate task A — boundary singleton adapter

The new verified theorem gives:

```lean
S.singleton_on_boundary hsupp : HC4.Polynomial.MvExponentOnBoundary d
```

for a singleton highest slice.

The fresh session should now locate and reuse the **existing vertical/facet/singleton consumers for a zero-coordinate exponent**. The intended proof shape is:

```text
slice.support = {d}
      ↓
singleton_on_boundary
      ↓
∃ i, d i = 0
      ↓
existing facet / vertical residue theorem
      ↓
terminal contradiction or reduction already accepted by the A19 stack
```

Do not invent a new global singleton classification until the existing zero-coordinate machinery has been searched thoroughly.

Search terms:

```text
MvExponentOnBoundary
Vertical
vertical
Singleton
singleton
coordinate_eq_zero
support = {
HighestPair
HighestSlice
facet
```

Start from:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarHighestPairSlice.lean
```

and inspect importers/consumers of `QsOtherFacetPlanarHighestPairSlicePackage`.

The success criterion for this task is a theorem that lets the strict-interior/fibre-collapse branch discharge a singleton highest slice without reopening the monomial Hessian calculation.

---

## 4. Immediate task B — unit strict-interior elimination

This is the main remaining local theorem.

### 4.1 Intended structural route

Reuse the already-developed finite-staircase infrastructure:

```text
strict interior
    ↓
legal first split
    ↓
ATwoFibreState
    ↓
exists_first_aSubset_step
    ↓
first terminating outcome
```

Do not build another independent staircase formalism.

The first terminating outcome should fall into one of three existing families.

### A. Stationary / one-sided tail

Expected route:

```text
stationary tail
    ↓
opposite tail becomes one-sided
    ↓
existing two-function carrier reconstruction
    ↓
existing Hessian contradiction
```

The endpoint and two-function carrier infrastructure already exists. Reuse it.

### B. Genuine pair selector

Expected route:

```text
genuine pair selector
    ↓
unit pair-Rees bridge
    ↓
zero-defect / delta = 0 contradiction
```

Again, the unit contact/staircase/pair-Rees stack is already compiled. This should be an adapter into existing theorems, not a new Rees theory.

### C. Fibre collapse

Expected route:

```text
fibre collapse
    ↓
singleton/highest-slice configuration
    ↓
singleton_on_boundary        [LEAN VERIFIED]
    ↓
boundary singleton adapter   [IMMEDIATE OPEN TASK]
    ↓
contradiction
```

The new singleton theorem was added precisely to make this exit literal and local.

### 4.2 Schematic target theorem

The exact current identifiers and field orientations **must be checked in source**. The following is only a shape guide:

```lean
private theorem impossible_of_strictInterior_unit
    (x : WalkerData N)
    (hTop : x.a.1.2.2 = 0)
    (hMid : 0 < x.a.1.2.1)
    (hV : x.V = 1)
    (hLeft : 0 < x.1.1)
    (hRight : 0 < x.1.2) :
    False := by
  -- enter existing two-fibre / first-subset-step machinery
  -- classify the first terminating step
  -- stationary tail -> two-function contradiction
  -- genuine pair -> pair-Rees / delta contradiction
  -- collapse -> singleton_on_boundary -> boundary adapter
  ...
```

Do not paste this blindly. Find the actual state type and current finite-staircase theorem signatures first.

Useful search strings:

```text
ATwoFibreState
exists_first_aSubset_step
first_aSubset
StrictInterior
strictInterior
stationary
pairRees
PairRees
fibre
collapse
WalkerData
```

---

## 5. Complete `.pr` once strict interior is closed

After the strict-interior theorem, the unit `.pr` case should be exhausted by endpoint arithmetic:

```text
left cap = 0      -> existing left endpoint contradiction
right cap = 0     -> verified right endpoint contradiction
both positive     -> new strict-interior contradiction
```

A schematic final dispatcher is:

```lean
private theorem impossible_pr_unit
    (x : WalkerData N)
    (hTop : x.a.1.2.2 = 0)
    (hMid : 0 < x.a.1.2.1)
    (hV : x.V = 1) :
    False := by
  rcases eq_zero_or_pos x.1.1 with hL | hL
  · exact impossible_of_no_range1_capLeft_unit x hTop hMid hV hL
  rcases eq_zero_or_pos x.1.2 with hR | hR
  · exact impossible_of_no_range1_capRight_unit x hTop hMid hV hR
  · exact impossible_of_strictInterior_unit x hTop hMid hV hL hR
```

**Warning:** the existing endpoint theorem names/orientations have historically been easy to read backwards. Verify exact identifiers before implementing. The logical split is authoritative; the schematic names are not.

Likely modules worth inspecting include:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointClosure.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitRightEndpointClosure.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitContactFrontier.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointOrientation.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitNoInteriorSupport.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrLockedSourceCoefficients.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedCarrier.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrCarrierReconstruction.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrTwoFunctionCarrier.lean
```

If a filename has moved, use the live tree/search; do not infer a replacement theorem by name alone.

---

## 6. `.sp` and `.rq`: transport, do not re-prove

Once `.pr` is fully contradictory, close the other toric facets using the existing permutation/cyclic relabelling infrastructure.

Required discipline:

```text
.pr proof
  ↓
coordinate permutation covariance
  ↓
.sp / .rq
```

Do **not** clone the finite-staircase proof twice. In particular, preserve:

- Hessian determinant covariance under variable renaming,
- source/contact/ray provenance under the chosen permutation,
- exact package fields needed by the A19 parent theorem.

Search for existing toric-facet permutation/covariance modules before writing a new map.

---

## 7. Final A19 / terminal assembly

After all three facet cases are impossible, the remaining work should be to feed that result into the existing terminal architecture rather than develop another local theory.

Expected high-level path:

```text
other-facet branch impossible
        ↓
existing strict-low / A19 parent assembly
        ↓
presentedTerminal_impossible
        ↓
existing reachable-terminal reduction
        ↓
public unrestricted HC4 theorem
```

Search live source for:

```text
presentedTerminal_impossible
PresentedTerminal
reachableTerminal
terminal_impossible
A19
OtherFacet
NontrivialAssembly
```

The exact public theorem name should be taken from the existing front-door module rather than invented in this handoff.

Before declaring success, inspect the final theorem signature itself. It must not silently assume a JC2 theorem, a hidden rank condition, a stronger homogeneity hypothesis, or an unproven source adapter.

---

## 8. Failed routes / hard prohibitions

These are not merely style preferences. They encode already-discovered mathematical obstructions and should prevent a fresh context from wasting time or reintroducing false implications.

### 8.1 Do not use global homogeneity

The global family is not homogeneous in the sense earlier drafts assumed. Only the special-fibre/local pointed state has the relevant homogeneous structure. Preserve the degree-adaptive recursion architecture.

### 8.2 Do not assume `j = Δ`

That shortcut failed. Any use of the defect/layer clock must respect the corrected architecture and actual hypotheses.

### 8.3 Do not infer degree `≤ 1` generically

The naive degree-`≤1` shortcut is false. The concrete counterexample recorded during development includes

```text
φ = (5 + 4T)^2
```

Existing degree-`≤1` lemmas apply only under their stronger residual/nonzero-constant-term hypotheses. Never weaken those hypotheses implicitly.

### 8.4 Do not revive the `qNN/qNM` coefficient-cancellation route

The direct `B - A*R` cancellation approach was obstructed. The proof architecture moved to global-progress / finite-staircase / source-honest geometric exits.

### 8.5 Do not revive the generic stationary determinant comparison

The proposed generic source/profile stationary determinant implication was shown false in that generality. See:

```text
docs/STATIONARY_DETERMINANT_COMPARISON_AUDIT_2026-09-15.md
```

### 8.6 Do not use the false first-variation shortcut

Do not infer the needed degree collapse from first variation plus staircase arithmetic alone. See:

```text
docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md
```

### 8.7 Do not collapse the live A19 strict-low branch to generic JC2

The generic two-zero projection is full JC2. The actual A19 branch retains stronger source/contact/ray provenance and has been deliberately closed through that stronger geometry. Do not throw the provenance away.

### 8.8 Auxiliary ray clock is not the zero blocker clock

Never identify these clocks without an explicit theorem.

### 8.9 Naked `withRepairOnly` progress is not a contradiction

A progress object alone is not the terminal contradiction. Use the exact closing theorem that consumes it.

### 8.10 Do not infer superface singularity from a smaller ray

Singularity/provenance must be transported by an explicit theorem at the correct carrier level.

### 8.11 The four-monomial cross-ratio equation is not by itself contradictory

It is structure, not a standalone contradiction.

### 8.12 Preserve source/contact/ray provenance

Do not replace the source-honest local object with a generic polynomial merely because the algebraic shape looks similar. The final proof depends on the retained provenance.

---

## 9. Existing infrastructure that should be treated as reusable

The repository already contains a very large verified stack. A fresh context should search before adding abstractions, especially for:

- source-honest planar carrier packages,
- highest-pair slice construction and Hessian singularity,
- line-supported Hessian rigidity,
- two-function carrier reconstruction and Hessian contradiction,
- locked-source/contact coefficient identities,
- unit endpoint orientation/frontier packages,
- finite-staircase recursion,
- pair-Rees bridges,
- toric-facet permutation covariance,
- presented rank-two geometry lifting,
- A19 terminal/reachable-terminal assembly.

The goal is now **composition**, not another parallel framework.

---

## 10. Status table for the fresh context

| Obligation | Status | Evidence / next action |
|---|---|---|
| unrestricted global entry | **LEAN VERIFIED** | in certified pre-final stack |
| A19.55 same-carrier codim-two local closure | **LEAN VERIFIED** | certified pre-final stack |
| lower `.qs` other-facet reduction | **LEAN VERIFIED** | certified pre-final stack |
| planar carrier / highest-pair slice adapter | **LEAN VERIFIED** | certified pre-final stack |
| line-supported / primitive slice rigidity | **LEAN VERIFIED** | certified pre-final stack |
| non-unit `.pr` finite staircase | **LEAN VERIFIED** | certified pre-final stack |
| left endpoint-only `V=1` | **LEAN VERIFIED** | pre-existing unit closure |
| right endpoint-only `V=1` | **LEAN VERIFIED** | commit `9db159b...`, CI `35149023096` |
| singleton cannot be interior | **LEAN VERIFIED** | commit `8ca83aa9...`, CI `35154902934` |
| boundary singleton adapter | **OPEN** | immediate next adapter into existing vertical/facet machinery |
| unit strict-interior elimination | **OPEN** | main remaining local theorem |
| complete `.pr` parent dispatcher | **OPEN** | expected thin assembly after strict interior |
| `.sp` / `.rq` | **OPEN** | permutation transport from `.pr` |
| A19 terminal splice | **OPEN** | consume impossible other-facet constructors |
| `presentedTerminal_impossible` / equivalent resolver | **OPEN** | connect to existing terminal architecture |
| public unrestricted HC4 theorem | **OPEN** | final front-door assembly |
| final root certification | **OPEN** | build + axioms + negative control + escape-hatch audit |

This table is intentionally conservative. “OPEN” does not imply the mathematics is unknown; several items are expected to be thin formal adapters/assembly. It means they are not yet certified as part of the public unrestricted theorem.

---

## 11. Definition of done

Do not claim unrestricted HC4 until all of the following are true on one coherent final head:

1. The `.pr` unit strict-interior case is impossible.
2. The boundary singleton residue is discharged.
3. `.pr`, `.sp`, and `.rq` other-facet cases are all consumed by the A19 parent.
4. The terminal resolver proves the remaining presented terminal state impossible.
5. The existing unrestricted entry theorem reaches that resolver without additional unproved assumptions.
6. The public HC4 theorem has the intended unrestricted statement.
7. Root CI passes `Build HC4`.
8. The theorem-axiom audit passes.
9. The negative control is rejected.
10. The proof escape-hatch audit passes.
11. The public theorem signature has been manually inspected for hidden hypotheses / JC2 punts.

Only then change documentation from “final sprint” to a proof-completion claim.

---

## 12. Recommended exact opening move in the next chat

After pinning the live head, search the source/tree for these identifiers in one pass:

```text
QsOtherFacetPlanarHighestPairSlicePackage
singleton_on_boundary
MvExponentOnBoundary
ATwoFibreState
exists_first_aSubset_step
StrictInterior
strictInterior
Vertical
Singleton
PairRees
PrNontrivialAssembly
presentedTerminal_impossible
```

Then inspect the importers/consumers of:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarHighestPairSlice.lean
```

The first implementation target should be the **smallest theorem turning `singleton_on_boundary` into the existing zero-coordinate/facet/vertical terminal consumer**. Once that compiles, immediately use it in the unit strict-interior first-step classification.

Do not spend the first session rewriting documentation again. The critical path is code.

---

## 13. Ready-to-paste fresh-chat prompt

```text
Continue the unrestricted HC4 Lean formalisation in
JamieLittle16/HC4_Lean_Canonical_Phase75_4, PR #34,
branch final-assembly/a18-4-42-termination-frontier.

First read:
docs/HANDOFF_2026-09-16_HC4_FRESH_CONTEXT_FINAL_SPRINT.md

Treat that file as authoritative. Pin the live PR head before editing and
separate generated/documentation commits from substantive code changes.

Do not revisit the frozen green checkpoints except to inspect interfaces.
The right endpoint-only V=1 mirror and singleton_on_boundary theorem are
LEAN VERIFIED with the CI runs recorded in the handoff.

Start with the boundary-singleton adapter and then the unit strict-interior
theorem. Reuse the existing finite-staircase / ATwoFibreState /
exists_first_aSubset_step infrastructure. Search existing vertical/facet
machinery before adding anything new.

Do not collapse the branch to generic JC2, do not revive the stationary
determinant or first-variation shortcuts, preserve source/contact/ray
provenance, and do not clone .pr arguments for .sp/.rq: use permutation
covariance.

Make actual commits and run the real build-and-audit workflow. Distinguish
LEAN VERIFIED, SOURCE-LANDED / NOT LEAN VERIFIED, PAPER CANDIDATE, and OPEN
throughout. Use LEAN VERIFIED only for a green root build + theorem-axiom
audit + negative control + escape-hatch audit.

The intended remaining path is:

boundary singleton adapter
  -> unit strict-interior closure
  -> complete .pr
  -> .sp/.rq by permutation
  -> A19 terminal splice
  -> presentedTerminal_impossible (or the exact live resolver)
  -> public unrestricted HC4 theorem
  -> final certification.

Proceed directly with implementation rather than producing another plan-only
handoff.
```

---

## 14. Final perspective

The proof is now past the stage where a fresh context should rediscover the global architecture. The two newest local closures matter because they remove the endpoint asymmetry and the genuinely interior singleton escape:

```text
right V=1 endpoint       CLOSED + CERTIFIED
interior singleton       CLOSED + CERTIFIED
```

The live mathematical seam is therefore concentrated in the **unit strict-interior finite-staircase termination**, with the singleton collapse already reduced to a boundary adapter. If that seam closes as intended, the remaining route is principally symmetry and terminal assembly.

That is the correct starting point for the next context window.
