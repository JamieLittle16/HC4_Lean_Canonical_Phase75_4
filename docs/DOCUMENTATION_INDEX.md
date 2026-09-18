# HC4 documentation index

**Authoritative map: 18 September 2026.**

The HC4 repository contains many historical phase notes. They are useful for
provenance, but they must not be treated as simultaneous current TODO lists.
Use the ownership rules below.

## Current authoritative continuation point

### `HANDOFF_2026-09-18_HC4_FIRST_DEFICIT_STAGGERED_BREAK.md`

This is the preferred fresh-context handoff for the live unrestricted-HC4
closure.

Its substantive source checkpoint is:

```text
PR #34
branch final-assembly/a18-4-42-termination-frontier
head f735921c6f994f1854e155056d55332de62ee165
Lean CI run 35339770347 / #3013
```

The handoff records the provenance-rich replacement for the older
repair-bookkeeping endpoint.  The live source chain now reaches:

```text
central source monomial
  -> honest total-deficit Rees family
  -> first positive binary Hessian-singular layer
  -> homogeneous linear power
  -> adjacent-deficit exclusion
  -> pure-axis singleton source layer
  -> honest rank-three roof at first deficit order q
  -> least later opening of the missing coordinate at order j > q
  -> firstDeficit_oppositeOpening
```

The immediate next task is a thin source-facing adapter from
`FirstDeficitOppositeOpening` plus the existing rank-three roof coefficient
to the already-written generic
`StaggeredSingularFirstKernelBreakFourBlockData`.  Its theorem
`exists_nonzero_principalMinor_at_kernelOrder` should then give honest later
rank-two Hessian geometry without identifying clocks or manufacturing a
singular sparse subpencil.

The handoff also records the recent kernel-inflation duplicate/interface
regressions and their repairs.  Check the exact-head CI status before promoting
newly landed files from SOURCE-LANDED to LEAN VERIFIED.

### `HANDOFF_2026-09-17_HC4_FINAL_GLOBAL_ASSEMBLY.md`

Historical provenance for the zero-defect global-progress shortcut.  Its
global-successor path remains valid infrastructure, but it is not by itself a
terminal contradiction: `rankThreeRepairState 0` cannot be declared
impossible merely from repair bookkeeping.  The 18 September handoff owns the
live continuation point.

### `HANDOFF_2026-09-17_HC4_UNIT_FINITE_STAIRCASE_FINAL_CLOSURE.md`

This is now historical provenance for the unit finite-staircase phase. Its
former local TODO has been overtaken by the strict-low zero-defect global
progress shortcut. Use it when tracing the local algebra, not as the fresh
context continuation point.

### `HANDOFF_2026-09-16_HC4_FRESH_CONTEXT_FINAL_SPRINT.md`

Historical provenance for the route into the unit branch. Its live TODO is
stale.

### `HANDOFF_2026-09-16_HC4_LAST_MILE_PUBLIC_CLOSURE.md`

Historical provenance for finite-staircase and public-closure architecture.
Its live TODO predates the current global-progress shortcut.

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

As of the current clean source checkpoint reported on 17 September 2026:

> the difficult local strict-low mathematics now has a Lean-verified,
> source-honest escape to genuine global macro progress on the reached
> raw-defect-zero state. The residual local `qs` leaves are no longer the live
> blocker. The remaining work is to connect that progress witness to the
> existing global-terminal/no-successor interface, propagate the contradiction
> through the existing rank-one termination and reachable-terminal assembly,
> expose the unrestricted root theorem, and pass the final exact-head audit
> suite.

This is **not yet a claim that unrestricted HC4 has been proved**.
