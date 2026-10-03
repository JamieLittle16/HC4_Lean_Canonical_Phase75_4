# HC4 documentation index

**Authoritative map: 18 September 2026.**

The HC4 repository contains many historical phase notes. They are useful for
provenance, but they must not be treated as simultaneous current TODO lists.
Use the ownership rules below.

## Current authoritative continuation point

### `HANDOFF_2026-09-18_HC4_GREEN_SHORTCUT_FINAL_CLOSURE.md`

This is the preferred fresh-context handoff for the live unrestricted-HC4
closure.

Certified substantive code checkpoint:

```text
PR #34
branch final-assembly/a18-4-42-termination-frontier
head 3de2689ad2b50003deab6433e1b521be259e6622
Lean CI run 35399193381 / #3146
Build HC4                              PASS
Axiom audit                            PASS
Negative control                       PASS
Escape-hatch audit                     PASS
```

The handoff itself was added in documentation-only commit:

```text
53608f17b17af5e2a0c04c31eff99967c5d35037
```

CI #3147 on that documentation head was still running when this index entry
was written, so `3de2689...` remains the certified substantive code anchor.

The live proof route has advanced substantially beyond the earlier
first-deficit handoff.  In particular the rooted source-pivot shortcut now
contains:

```text
qs lower-ray / other-facet rank-three endpoint
  -> represented-source principal Hessian minor
  -> AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
```

and the lower-ray pure-endpoint first-break route now has the generic
whole-family reverse-Rees Hessian-minor lift:

```text
whole-family first-break principal minor
  -> represented-source principal Hessian minor
  -> actual rank-two chart.
```

The only endpoint first-break residue is the exact breaking-layer proposition

```lean
LayerMinorAtFirstBreak
```

but **do not automatically attack that first**.  Raw-defect-zero states already
carry generic exact-active and complete rank-three Hessian geometry.  The first
task in a fresh context is therefore to audit for a terminal-facing consumer
of:

```lean
AdaptiveAlignedSmithCanonicalActualRankThreeGeometry
AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry
AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
```

If such a consumer already closes a reachable presented terminal, use it and
skip unnecessary local branch work.

If no such consumer exists, the preferred local fallback is to close
`LayerMinorAtFirstBreak` by proving that an exact bounded reverse-Rees
parameter layer is the weighted initial form of the represented source at the
corresponding level, then apply the existing weighted-initial-form Hessian
principal-minor lift.

The public final reducer is already present:

```lean
gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
```

so the final logical theorem remains impossibility of the **actually reachable**
complexity-zero presented terminal carrying inherited
`state.repair = rankOneRepairState 0`.

### `HANDOFF_2026-09-18_HC4_FIRST_DEFICIT_STAGGERED_BREAK.md`

Historical provenance for the source-honest first-deficit / staggered-break
development.  Its former live continuation point has been overtaken by the
rooted source-pivot and reverse-Rees Hessian-minor shortcuts.  Keep it for the
verified local algebra and provenance discipline, not as the fresh-context
TODO.

### `HANDOFF_2026-09-17_HC4_FINAL_GLOBAL_ASSEMBLY.md`

Historical provenance for the zero-defect global-progress route.  Its
global-successor theorems remain valid infrastructure, but a presented
rank-three terminal does not itself carry a no-global-successor certificate,
so global progress alone is not the final contradiction.

### `HANDOFF_2026-09-17_HC4_UNIT_FINITE_STAIRCASE_FINAL_CLOSURE.md`

Historical provenance for the unit finite-staircase phase.  Do not treat its
former local TODO as current.

### `HANDOFF_2026-09-16_HC4_FRESH_CONTEXT_FINAL_SPRINT.md`

Historical provenance for the route into the unit branch. Its live TODO is
stale.

### `HANDOFF_2026-09-16_HC4_LAST_MILE_PUBLIC_CLOSURE.md`

Historical provenance for finite-staircase and public-closure architecture.
Its live TODO predates the current source-pivot / source-minor shortcut.

## Core architectural documents

### `CURRENT_STATE.md`

Owns the broader repository-level status ledger. It may lag the newest handoff
during the active final sprint; when that happens, the dated current handoff
above wins for the live TODO.

### `PROOF_ARCHITECTURE.md`

Owns the mathematical architecture and the global/local proof shape.

### `PROOF_PATHS.md`

Owns route lookup: given a carrier/interface, which canonical modules should be
used next and which invalid shortcuts should be avoided?

### `CANONICAL_OWNERS.md`

Owns reusable Lean definition/theorem families. Search this before adding a
new generic-looking object.

### `GLOSSARY_AND_INVARIANTS.md`

Owns terminology and provenance rules. In particular, carriers and clocks with
similar roles are not interchangeable without explicit theorems.

### generated indexes

- `generated/LEAN_MODULE_INDEX.md`
- `generated/DECLARATION_INDEX.md`
- `generated/LOCAL_IMPORT_EDGES.md`

These own exhaustive inventory, not mathematical status.

## Current mathematical reference documents

### `HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md`

Owns detailed paper mathematics for the full two-function Hessian, the
singleton/developable fallback, and the original `V=1` endpoint analysis. Use
it for mathematics, not current implementation status. Many of its former open
tasks have since landed in Lean.

### `HANDOFF_2026-09-15_HC4_PAIR_REES_FINAL_CLOSURE.md`

Owns detailed provenance of the locked/contact and highest/pair-Rees
first-variation constructions and the warning that two endpoint first
variations alone do not eliminate every interior staircase fibre. Its TODO is
historical.

### `HANDOFF_2026-09-16_HC4_FINAL_ASSEMBLY.md`

Owns detailed provenance for the right `(V,1)`, `V>1` mirror and an earlier
final-assembly architecture. Its status table is superseded by the current
17 September global-assembly handoff.

### `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

Owns the completed paper-level line-supported Hessian recurrence/rational-map
argument. The relevant primitive highest-slice rigidity is formalized.

### `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`

Owns the state-free algebra behind the A19.55 same-carrier codimension-two
branch. That branch remains useful verified infrastructure but is not the live
terminal contradiction route.

### `A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`

Prohibition/reference document for the false shortcut

```text
first variation + staircase arithmetic -> degree <= 1.
```

The counterexample discipline recorded there remains binding. In particular,
do not revive a generic degree-`≤ 1` shortcut; `φ=(5+4T)^2` remains a known
obstruction to the old argument.

### `STATIONARY_DETERMINANT_COMPARISON_AUDIT_2026-09-15.md`

Reference for the failed generic stationary source/profile determinant
comparison. Do not revive that implication in the final proof.

## Superseded status handoffs

### `HANDOFF_2026-09-15_HC4_FINAL_MULTIFIBER_CLOSURE.md`

Historical checkpoint from before the exposed cross-roof and mirrored nonunit
finite-staircase branches were completed.

### `HANDOFF_2026-09-15_HC4_FINAL_LEAN_CLOSURE.md`

Historical checkpoint for stationary machinery. Its proposed generic
source/profile determinant bridge was subsequently shown false in that
generality and replaced by source-honest work.

### `HANDOFF_2026-09-11_HC4_FINAL_CLOSURE.md`

Historical source/contact/ray provenance checkpoint.

## Historical but still useful

### ray-Schur / Rees obstruction notes

The proved auxiliary `.pr` ray clock, exact clock mismatch, weight bounds and
countertests remain important. Preserve their main lesson:

```text
auxiliary ray clock != zero blocker clock.
```

They are not the direct final terminal contradiction path.

### older JC2 closure plans

Generic two-zero projection is indeed full JC2. The current unrestricted route
does not need it: the reached strict-low state itself gives source-honest
zero-defect rank-two global progress. JC2 modules remain reusable historical
infrastructure but are not the live closure plan.

### historical phase/status files

Files named `FORMALISATION_STATUS_PHASE*`, `PHASE*.md`, old handoffs and similar
notes record real development history. They are not current proof ledgers.

## Hard rules for the final sprint

- do not identify auxiliary Rees clocks with the zero-defect blocker;
- do not use naked `withRepairOnly` progress as the contradiction;
- do not collapse the remaining assembly to generic JC2;
- do not invent a second termination measure: reuse raw-defect
  `rankOneTerminationTrace`;
- do not infer superface singularity from a smaller ray;
- do not use a four-monomial cross-ratio equation as a contradiction by itself;
- do not reopen the retired `qs` codimension-two / literal-square leaves unless
  an exact global state-interface mismatch proves they are needed;
- search current branch source and generated indexes before adding new generic
  infrastructure.

## Status vocabulary

Every new progress document should use only:

- **LEAN VERIFIED** — formalised and accepted by Lean in the stated certified
  build; if a final parent/root splice is still missing, say so explicitly;
- **SOURCE-LANDED / NOT LEAN VERIFIED** — committed source without a known
  successful exact-head build yet;
- **PAPER CANDIDATE** — a complete paper argument or symbolic derivation exists
  but has not yet been formalised;
- **DIAGNOSTIC ONLY** — useful experiment/counterexample/symbolic evidence that
  is not a proof theorem;
- **OPEN** — a genuine mathematical/formal/assembly obligation remains.

Avoid ambiguous labels such as “basically done,” “solved,” or “green” unless
the context makes clear whether this means paper or Lean.

## Current one-line status

At the certified code checkpoint `3de2689...` on 18 September 2026:

> the cyclic source-pivot shortcut and whole-family reverse-Rees Hessian-minor
> lift are Lean verified and rooted, and the endpoint first-break residue has
> collapsed to one exact-layer minor case.  However generic raw-zero
> exact-active/rank-three geometry already exists, so the fastest next move is
> to identify or build the **terminal-facing consumer** of that geometry.  If no
> such consumer exists, close `LayerMinorAtFirstBreak` by exact-layer
> weighted-initial-form transport, finish any genuinely necessary facet
> assembly, prove reachable presented-terminal impossibility, and instantiate
> the already-verified public HC4 reducer.

This is **not yet a claim that unrestricted HC4 has been proved**.
