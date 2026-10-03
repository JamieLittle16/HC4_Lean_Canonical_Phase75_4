# HC4 final global assembly handoff

**Date:** 17 September 2026  
**Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`  
**PR:** #34 — `A18.4.42 collapse final termination frontier`  
**Branch:** `final-assembly/a18-4-42-termination-frontier`  
**Current source checkpoint when this handoff was written:** `cd9b24560468722ff538d2e85626f5af5d5c6336`  
**Historical shortcut proof commit:** `3a7b2848e587156cccc9115e606743c2f6338055`

This document is the authoritative fresh-context continuation point for the
unrestricted HC4 proof after the zero-defect global-progress shortcut. It
supersedes the live TODO in
`HANDOFF_2026-09-17_HC4_UNIT_FINITE_STAIRCASE_FINAL_CLOSURE.md`.

The user reports that the current head compiles cleanly. Treat the mathematical
and Lean source through this checkpoint as the current certified baseline, but
do not claim unrestricted HC4 until the final global assembly and the final
root/audit suite are complete.

---

## 0. Status vocabulary

Use these labels strictly throughout the final work:

- **LEAN VERIFIED** — accepted by Lean at the stated clean/certified checkpoint;
- **SOURCE-LANDED / NOT YET LEAN VERIFIED** — committed source not yet certified
  by the relevant exact-head build;
- **PAPER CANDIDATE** — complete paper mathematics exists but the Lean theorem is
  not yet established;
- **DIAGNOSTIC ONLY** — experiment/counterexample/evidence, not a proof;
- **OPEN** — genuine remaining proof/assembly obligation.

Do not use “done”, “green”, “solved”, or similar language without saying which
of these meanings is intended.

---

## 1. Executive state

The proof has crossed the important boundary from **local mathematical closure**
to **global assembly**.

The difficult A19 strict-low / rank-three / other-facet analysis was developed
through a long sequence of source-honest local reductions. The most recent
advance makes the residual local `qs` frontier unnecessary for the final
unrestricted proof:

```text
strict-low zero-clock terminal data
        |
        | retains repair = rankOneRepairState 0
        | retains rawDefect = 0 on the reached state itself
        v
existing zero-defect rank-two geometry theorem
        |
        v
concrete AdaptiveAlignedSmithCanonicalGlobalMacroProgress
        |
        v
strict-low "terminal" is not globally terminal
```

This is already represented by exact Lean declarations in

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowGlobalProgress.lean
```

Therefore the live critical path is no longer “prove another local Hessian
lemma.” It is:

```text
zero-defect global-progress shortcut                 LEAN VERIFIED
        |
        v
find exact no-successor / global-terminal interface  OPEN
        |
        v
contradict it with exists_globalProgress             OPEN
        |
        v
splice through rank-one Rees final outcome           OPEN
        |
        v
splice through reachable-terminal impossibility      OPEN
        |
        v
existing unrestricted gradient-injectivity entry     OPEN AS ASSEMBLY
        |
        v
public/root unrestricted HC4 theorem                 OPEN
        |
        v
root build + all audits                               OPEN
```

**Expectation:** assuming the existing global termination/reachability APIs
match the reached state without a hidden representation mismatch, the remaining
work should be mostly theorem/interface plumbing. The next context should not
restart local algebra unless an exact Lean type mismatch proves that it is
actually necessary.

---

## 2. Exact verified shortcut now available

The current source contains:

```lean
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
import Mathlib.Tactic

namespace Polynomial

variable {K : Type*}

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

theorem exists_globalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state := by
  let P :=
    ScaleAwareAdaptiveGeometricRestartState.zeroDefect_globalRankTwoProgress
      canonicalAdaptiveAlignedSmithRepairRanking state 0 T.repair_eq T.source_zero
  exact ⟨P.target, P.globalProgress⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress
        target T.trace.reachedRankThree.state := by
  rcases T.globalProgress_or_zeroStrictLowTerminal hsrepair with
    hprogress | hterminal
  · exact hprogress
  · rcases hterminal with ⟨Z⟩
    exact Z.exists_globalProgress

end Polynomial
```

### Status

**LEAN VERIFIED** at the current clean source checkpoint reported by the user.
The theorem was introduced in substantive commit
`3a7b2848e587156cccc9115e606743c2f6338055` and remains in the current branch.

### What this theorem gives us

For every relevant rank-one Rees reduced trace, once the source repair
hypothesis is available, we obtain a genuine

```lean
AdaptiveAlignedSmithCanonicalGlobalMacroProgress
  target T.trace.reachedRankThree.state
```

from the **actual reached rank-three state**.

That is exactly the shape one wants to contradict any assertion that this
reached state is globally terminal / has no admissible global macro successor.

---

## 3. Why this shortcut is source-honest

The shortcut is not an accidental consequence of a weak progress metric. Its
input is geometric information retained on the reached state itself.

The strict-low terminal package retains:

```text
repair_eq   : state.repair = rankOneRepairState 0
source_zero : state.rawDefect = 0
```

The existing finite Hessian rank split says, schematically, that the special
fibre has either:

```text
an actual active 2x2 Hessian chart
```

or

```text
all special-fibre 2x2 Hessian minors vanish.
```

The existing zero-defect rank-two geometry theorem eliminates the second branch
under the determinant-one hypotheses. Hence raw-defect zero supplies genuine
rank-two Hessian geometry, and the existing global-progress constructor turns
that geometry into `AdaptiveAlignedSmithCanonicalGlobalMacroProgress`.

The proof therefore does **not** rely on any of the invalid shortcuts that were
rejected earlier in the project.

---

## 4. Local branches that are no longer on the critical path

Immediately before the shortcut, the `qs` other-facet frontier had effectively
collapsed to:

```text
starting qs ray is codimension two
        OR
actual rank-two Hessian chart
        OR
literal represented-source quadratic square x₀².
```

The actual rank-two chart was already consumable. The codimension-two and
literal-square leaves still carried adapter/provenance work.

**Do not continue those two leaves by default.**

The new global-progress theorem bypasses the later local `qs` frontier entirely:
it acts before those leaves are needed, on the reached raw-defect-zero state.

Only return to a retired local leaf if the exact global assembly exposes a real
state-interface mismatch that cannot be resolved by rewriting/transport through
existing state-equivalence or reachability lemmas.

---

## 5. Hard architectural prohibitions

The final assembly must preserve all of the following.

### 5.1 Do not identify clocks

```text
auxiliary Rees/ray clock != zero-defect blocker clock
```

No theorem may silently identify them.

### 5.2 Do not use naked `withRepairOnly` as a contradiction

The new shortcut already gives genuine global macro progress from rank-two
geometry. There is no reason to revive repair-only progress as the terminal
contradiction.

### 5.3 Do not reduce the strict-low branch to generic JC2

The generic two-zero projection is full JC2. It is neither required nor wanted
for the final HC4 closure now that the source-honest zero-defect progress route
exists.

### 5.4 Do not invent a new termination measure

The existing raw-defect `rankOneTerminationTrace` is the termination mechanism.
Reuse it and its established global/reachable-terminal assembly.

### 5.5 Do not revive false local shortcuts

In particular:

- do not infer superface singularity from a smaller ray;
- do not treat a four-monomial cross-ratio identity as a contradiction by itself;
- do not assert a generic degree-`≤ 1` shortcut; the counterexample
  `φ=(5+4T)^2` remains a prohibition witness;
- do not revive the failed generic stationary source/profile determinant
  implication.

---

## 6. Immediate critical path — detailed plan

### Step 1 — re-pin the exact PR head

At the start of the fresh context:

1. fetch PR #34 metadata;
2. record exact `head_sha`;
3. inspect whether commits above this handoff are proof commits or generated
   inventory/documentation only;
4. if the head differs from this document's `cd9b245...`, inspect the diff before
   changing proof code.

Current source is authoritative. Documentation is guidance only.

### Step 2 — locate the exact terminal/no-successor interface

Search the **current branch source**, not only the default-branch GitHub code
index, for declarations and modules containing:

```text
RankOneReesFinalOutcome
RankOneRees
GlobalMacroTermination
GlobalMacroProgress
ReachableTerminal
reachableTerminal
TerminalImpossible
GlobalTermination
FinalAssembly
noGlobalProgress
noProgress
terminal
```

The target is an exact declaration asserting, directly or through a terminal
package, that

```text
T.trace.reachedRankThree.state
```

cannot admit an

```lean
AdaptiveAlignedSmithCanonicalGlobalMacroProgress target ...
```

Do not guess the predicate name. Fetch the defining source and read its exact
quantifiers, namespace, direction, and state parameter.

### Step 3 — write the thinnest contradiction adapter

Once the no-successor API is known, the proof should be nearly tautological.

**SCHEMATIC ONLY — identifiers below are intentionally placeholders:**

```lean
theorem rankOneReesReducedTrace_not_globalTerminal
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (hterminal : <NoGlobalMacroProgress T.trace.reachedRankThree.state>) :
    False := by
  rcases T.exists_globalProgress hsrepair with ⟨target, hprogress⟩
  exact hterminal target hprogress
```

Possible actual terminal APIs may instead be:

```text
¬ ∃ target, GlobalMacroProgress target state
```

or a structure field such as:

```text
terminal.no_globalProgress
```

or a theorem which directly consumes a progress witness. Adapt to the existing
shape rather than wrapping it in a new general abstraction.

**Acceptance condition for Step 3:** a small theorem, preferably in the existing
rank-one Rees final-outcome/global-assembly module, closes the alleged terminal
reached state using `T.exists_globalProgress hsrepair` and nothing stronger.

### Step 4 — splice through the rank-one Rees final outcome

Find the existing theorem/inductive outcome that receives a
`AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace` at the final rank-one
termination stage.

Likely search terms:

```text
RankOneReesFinalOutcome
RankOneReesReducedTrace
rankOneTerminationTrace
reachedRankThree
zeroStrictLowTerminal
globalProgress_or_zeroStrictLowTerminal
```

The desired logical collapse is:

```text
rank-one Rees reduced trace
        |
        +-- existing immediate global-progress branch -> already nonterminal
        |
        +-- zero strict-low terminal branch
                |
                +-- new zero-defect theorem -> global progress
```

So after the shortcut there should be **no rank-one Rees reduced trace branch
which is genuinely globally terminal**.

Prefer one theorem that consumes the existing final-outcome object rather than
adding duplicate outcome structures.

### Step 5 — propagate to reachable-terminal impossibility

Locate the established A18/A19 theorem that reduces the unrestricted problem to
impossibility of a reachable terminal state.

Do not rebuild reachability. The global restart/descent architecture already
exists and was developed specifically for this stage.

Search for declarations involving:

```text
reachable terminal
reachableTerminal
reachesLosslessSmithFrontier
canonicalGeometricRestart
terminal impossible
FinalAssemblySoundness
GlobalCanonicalExposureNeutrality
GlobalSurvivingTraceReduction
GlobalExposureClockReduction
StateBridge
```

The likely desired proof shape is:

```text
assume reachable terminal state
  -> existing terminal classification / rank-one termination trace
  -> rank-one Rees reduced trace at the reached state
  -> Step 4 says this trace has a global successor
  -> contradict terminality
```

Again, use the exact existing classifier. Do not create a second global terminal
classification.

### Step 6 — feed the existing unrestricted entry theorem

A theorem remembered from the global architecture is named approximately/exactly:

```text
gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible
```

**The exact namespace/signature has not been re-verified in this handoff.**
Search current source and inspect it before use.

If this is indeed the existing final bridge, the remaining theorem should simply
provide its `reachableTerminal_impossible` premise from Step 5.

At this point, do not prove injectivity again from algebra. The point of A18/A19
was to make the final unrestricted entry a consumer of the global terminal
impossibility theorem.

### Step 7 — expose the public unrestricted HC4 theorem

Inspect `HC4.lean` and any current root/final-assembly module. Determine whether:

1. the unrestricted theorem already exists but is missing the final premise;
2. a final theorem exists in a deep namespace but is not re-exported; or
3. one tiny root theorem still needs to be added.

The public theorem should be a direct consequence of the verified final assembly,
not a duplicate proof.

Use the repository's established statement of HC4. Do not casually change its
hypotheses, coefficient field, Jacobian/Hessian normalisation, or injectivity
conclusion while “cleaning up” the root API.

### Step 8 — final exact-head certification

Only after the unrestricted theorem is exposed should we call the project
closed.

Run/check the repository's existing exact certification suite:

```text
Build HC4
Axiom audit
Proof-complete branch negative control
Escape-hatch audit
```

Also verify:

```text
no `sorry`
no `admit`
no new `axiom`
no unsafe bypass
unrestricted theorem imports from the intended root
```

Record the exact final commit and workflow/run identifiers in the final handoff
or repository status ledger.

---

## 7. Efficient source-discovery strategy

A fresh context should not spend a long time rediscovering the repository.
Use this order.

### 7.1 Start from exact known declarations

Fetch:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowGlobalProgress.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry.lean
```

Follow their imports upward/downward to the final rank-one outcome.

### 7.2 Search generated indexes for names, then source for truth

Useful indexes:

```text
docs/generated/DECLARATION_INDEX.md
docs/generated/LEAN_MODULE_INDEX.md
docs/generated/LOCAL_IMPORT_EDGES.md
```

Use them to discover candidate files. Then fetch the actual `.lean` file and
read the declaration itself.

### 7.3 Search the recursive branch tree when default-branch code search is stale

PR #34 is far ahead of `master`, so ordinary GitHub code search may miss branch
only declarations. If a search returns nothing:

1. fetch the recursive git tree at the exact PR head;
2. search filenames for the terms in Step 2;
3. fetch likely modules directly by branch/ref.

Do not conclude “the theorem does not exist” from default-branch search alone.

### 7.4 Follow imports rather than names when terminology differs

The global assembly modules historically include families such as:

```text
ZeroDefectReentry
FinalAssemblySoundness
ZeroSchur
GlobalGeometryCarryingRankTwoFrontier
GlobalPointedRankTwoPresentation
GlobalSurvivingTraceReduction
GlobalExposureClockReduction
StateBridge
GlobalCanonicalExposureNeutrality
```

If the expected `ReachableTerminal` string is absent, inspect these import
chains before adding a new abstraction.

---

## 8. Minimal-patch discipline

The final stage is exactly where unnecessary refactors are most dangerous.
For each step:

1. fetch the exact current head;
2. fetch the exact target file and blob SHA;
3. inspect nearby theorem signatures and namespace;
4. add the smallest theorem/adapter that composes existing declarations;
5. compile/check;
6. only then move to the parent layer.

Prefer:

```text
one adapter theorem
-> one parent splice
-> one root splice
```

over a large new “final closure framework”.

Do not rename foundational definitions or reorganize modules during this sprint.

---

## 9. Failure taxonomy — debug in this order

If the expected two-line contradiction does not typecheck, classify the failure
before doing mathematics.

### Class 1 — import / namespace mismatch

Symptoms:

```text
unknown identifier
ambiguous declaration
namespace not opened
```

Response: locate the exact declaration/import. No mathematical redesign.

### Class 2 — terminal predicate packaging mismatch

Symptoms:

```text
hterminal is a structure rather than a function
terminal theorem expects `¬ ∃ ...`
terminality is phrased via a final-outcome constructor
```

Response: destruct/use the existing package. Add at most a thin local adapter.

### Class 3 — reached-state equality mismatch

Symptoms:

```text
progress is on T.trace.reachedRankThree.state
terminality is on a definitionally/non-definitionally equal state
```

Response: search existing state bridge/equality/transport lemmas; try `simpa`,
`rw`, explicit equality transport. Do **not** reopen geometry first.

### Class 4 — repair-hypothesis packaging mismatch

Symptoms:

```text
exists_globalProgress needs
source.repair = rankOneRepairState 0
```

but the parent theorem stores it under another package.

Response: extract it from the existing trace/terminal data. The strict-low path
was constructed with this invariant; do not introduce a new assumption without
checking provenance.

### Class 5 — reachable-terminal dispatcher mismatch

Symptoms:

```text
local contradiction is proved, but parent classifier has an additional
constructor or wraps the trace differently
```

Response: inspect the complete parent inductive/case split and consume each
existing constructor. Reuse already-verified contradictions for non-rank-one
branches.

### Class 6 — genuine state/provenance gap

Only after Classes 1–5 are ruled out should we consider whether the global
terminal state truly lacks the raw-defect-zero reached-state provenance needed
by the new theorem.

If this occurs, isolate the missing adapter exactly. Do not immediately reopen
all retired `qs` local mathematics.

---

## 10. Expected proof shapes

These are deliberately schematic. They are a map, not declarations to paste
blindly.

### 10.1 Terminal contradiction

```lean
rcases T.exists_globalProgress hsrepair with ⟨target, hprogress⟩
exact hterminal target hprogress
```

or, for existential terminality:

```lean
apply hterminal
exact ⟨target, hprogress⟩
```

### 10.2 Reduced-trace impossibility

```lean
rcases existing_rankOne_final_split T hsrepair with hprogress | hterminal
· exact terminal.reject_progress hprogress
· exact terminal.reject_progress hterminal.exists_globalProgress
```

The actual new theorem may be even shorter because
`T.exists_globalProgress hsrepair` already collapsed the split.

### 10.3 Reachable terminal impossibility

```lean
intro R
obtain ⟨T, hsrepair, hterminal, ...⟩ := existing_terminal_classification R
exact reducedTrace_not_terminal T hsrepair hterminal
```

### 10.4 Final unrestricted entry

```lean
exact gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible
  ... reachableTerminal_impossible
```

Do not trust these argument orders or theorem names until source inspection.

---

## 11. What counts as success at each layer

| Layer | Acceptance condition | Current status |
|---|---|---|
| Zero strict-low terminal | Produces genuine global macro progress on reached state | **LEAN VERIFIED** |
| Rank-one Rees reduced trace | Cannot satisfy existing globally-terminal/no-successor interface | **OPEN** |
| Rank-one terminal outcome | No surviving terminal constructor after existing classification | **OPEN** |
| Reachable terminal | Existing global reachability theorem yields contradiction for every reachable terminal | **OPEN** |
| Unrestricted entry | Existing gradient-injectivity/HC4 bridge consumes reachable-terminal impossibility | **OPEN** |
| Public root theorem | Unrestricted HC4 theorem exposed from intended root import | **OPEN** |
| Final certification | Build + axiom + negative-control + escape-hatch audits pass at exact final head | **OPEN** |

The first row is the last substantive local mathematical obstacle currently
known. Everything below it should be treated first as assembly work.

---

## 12. Existing global architecture to reuse

Do not duplicate these ideas if corresponding current declarations already
exist:

- raw-defect `rankOneTerminationTrace`;
- canonical restart/descent and lossless Smith frontier;
- affine two-fixed `RationalRigidity` contradiction;
- first-contact rank-three elimination;
- adjacent extreme-ray forcing;
- structural trace collapse;
- zero-defect re-entry;
- final-assembly soundness;
- global geometry-carrying rank-two frontier;
- global pointed rank-two presentation;
- surviving-trace reduction;
- exposure-clock reduction;
- state bridge;
- canonical exposure neutrality.

The historical endpoint theorem
`canonicalGeometricRestart_reachesLosslessSmithFrontier` (or its current
renamed equivalent) is part of this architecture. Re-fetch its present
signature before use.

---

## 13. Why the old 17 September unit-staircase handoff is now stale

`HANDOFF_2026-09-17_HC4_UNIT_FINITE_STAIRCASE_FINAL_CLOSURE.md` correctly
records a major earlier checkpoint, but its live critical path still says to
finish unit finite-staircase extremal/equal-k/strict-k algebra and propagate
that through the `qs` frontier.

Subsequent source work went farther:

1. the rank-one Rees strict-low terminal package was completed;
2. the reached state was shown to retain the exact zero-defect/repair data;
3. existing zero-defect rank-two geometry was connected to that package;
4. `AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress`
   now bypasses the residual local frontier.

Therefore the old handoff remains useful mathematical provenance, but **must not
be used as the TODO list** in a fresh context.

---

## 14. Fresh-context restart command

Paste the following into the next context if useful:

> Continue the unrestricted HC4 closure from
> `docs/HANDOFF_2026-09-17_HC4_FINAL_GLOBAL_ASSEMBLY.md` on PR #34. Re-fetch the
> exact PR head first and treat current Lean source as authority. The
> zero-defect strict-low global-progress shortcut is the certified local
> endpoint; do not reopen the retired `qs` codimension-two or `x₀²` leaves by
> default. Start at Critical Path Step 2: locate the exact existing
> globally-terminal/no-global-successor interface for
> `T.trace.reachedRankThree.state`, contradict it with
> `AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.exists_globalProgress`,
> then propagate through the existing reachable-terminal assembly to the
> unrestricted root theorem. Preserve LEAN VERIFIED / SOURCE-LANDED / PAPER
> CANDIDATE / OPEN labels and run the full final audit suite before claiming
> HC4.

---

## 15. Final endpoint

The project is complete only when a single exact head has all of the following:

```text
unrestricted HC4 theorem available from the intended public/root module
+
full HC4 build passes
+
axiom audit passes
+
proof-complete branch negative control passes
+
escape-hatch audit passes
```

At that point record:

```text
final commit SHA
workflow/run ID(s)
exact public theorem name and signature
axiom-audit result
negative-control result
escape-hatch result
```

Until then, the correct project status is:

> **The difficult local strict-low mathematics has a Lean-verified global-progress
> escape; unrestricted HC4 now appears to be in final global assembly, but the
> terminal/reachability/root splice and final exact-head audits remain OPEN.**
