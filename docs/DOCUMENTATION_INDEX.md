# HC4 documentation index

**Authoritative map: 17 September 2026.**

The HC4 repository contains many historical phase notes. They are useful for
provenance, but they must not be treated as simultaneous current TODO lists.
Use the ownership rules below.

## Current authoritative continuation point

### `HANDOFF_2026-09-17_HC4_UNIT_FINITE_STAIRCASE_FINAL_CLOSURE.md`

This is the preferred and authoritative fresh-context handoff for the live
unrestricted-HC4 final sprint.

Its authoritative certified **code** checkpoint is:

```text
commit e2783035171d173516a33448615f6cccd4ec9feb
message: Add unit finite-staircase extremal fibers
Lean CI: 35237635579
```

That exact code checkpoint passed:

```text
Build HC4
Axiom audit
Proof-complete branch negative control
Escape-hatch audit
```

The branch may have generated-inventory or documentation commits above that
code commit. Re-pin PR #34 at the beginning of a fresh session and distinguish
the current branch head from the last exact-head certified proof checkpoint.

The 17 September handoff records the newest unit finite-staircase progress as
**LEAN VERIFIED**:

```text
exact low/contact selected carrier fibre
exact high/pair-Rees selected carrier fibre
same-k selected multivariate layer equality
same-k staircase-height equality
same-k one-variable profile equality
common nonzero profile satisfying both endpoint Euler equations
same-k degree trichotomy:
    j + 2 = k  OR  j + 1 = k  OR  j = k
low selector = least strict-interior pair fibre
high selector = greatest strict-interior pair fibre
```

The current critical path is therefore:

```text
prove Alo.k <= Ahi.k from the certified extrema
  -> equal-k unit one-fibre contradiction
       (port/factor nonunit lower/middle/upper diagonal closures)
  -> strict-k unit multi-fibre contradiction
       (port/specialize nonunit extrema/cross-roof closure)
  -> unit finite-staircase closure
  -> existing endpoint/no-interior + right-orientation transport
  -> complete .pr parent assembly
  -> .sp/.rq by existing permutation covariance
  -> existing other-facet / A19 / global splice
  -> public unrestricted HC4 theorem
  -> exact-head full certification
```

For **current implementation status and TODO order**, this 17 September handoff
supersedes all earlier dated handoffs.

### `HANDOFF_2026-09-16_HC4_FRESH_CONTEXT_FINAL_SPRINT.md`

This remains useful historical provenance for the route into the unit branch,
but its live TODO is now stale. In particular, the boundary-singleton seam and
the earlier informal two-fibre framing have been overtaken by the certified
unit finite-staircase one-fibre/extrema infrastructure. Do not use it as the
primary continuation point.

### `HANDOFF_2026-09-16_HC4_LAST_MILE_PUBLIC_CLOSURE.md`

This remains valuable historical provenance for finite-staircase and
public-closure architecture, but its live TODO predates the certified unit
one-fibre and extremal-fibre work.

## Core architectural documents

### `CURRENT_STATE.md`

Owns the broader repository-level status ledger. It may lag the newest handoff
during the active final sprint; when that happens, the dated current handoff
above wins for the live local TODO.

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
it for mathematics, not current implementation status. Several of its former
open tasks have since landed in Lean.

### `HANDOFF_2026-09-15_HC4_PAIR_REES_FINAL_CLOSURE.md`

Owns detailed provenance of the locked/contact and highest/pair-Rees
first-variation constructions and, importantly, the warning that the two
endpoint first variations alone do not eliminate all interior staircase
fibres. Its TODO is historical because the nonunit finite staircase is closed
and the unit branch now has a certified common-profile degree trichotomy.

### `HANDOFF_2026-09-16_HC4_FINAL_ASSEMBLY.md`

Owns detailed provenance for the right `(V,1)`, `V>1` mirror and earlier
final-assembly architecture. Its status table is superseded by the current
17 September handoff.

### `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

Owns the completed paper-level line-supported Hessian recurrence/rational-map
argument. The relevant primitive highest-slice rigidity is already formalized.

### `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`

Owns the state-free algebra behind the A19.55 same-carrier codimension-two
branch. That branch has a Lean-verified geometry-bearing local closure.

### `A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`

Prohibition/reference document for the false shortcut

```text
first variation + staircase arithmetic -> degree <= 1.
```

The valid live replacement in the equal-fibre unit branch is the certified
three-way affine-two-root degree trichotomy.

### `STATIONARY_DETERMINANT_COMPARISON_AUDIT_2026-09-15.md`

Reference for the failed generic stationary source/profile determinant
comparison. Do not revive that implication in the final proof.

## Superseded status handoffs

### `HANDOFF_2026-09-15_HC4_FINAL_MULTIFIBER_CLOSURE.md`

Historical checkpoint from before the exposed cross-roof and mirrored nonunit
finite-staircase branches were completed. Use its mathematics only when it
matches the live verified declarations.

### `HANDOFF_2026-09-15_HC4_FINAL_LEAN_CLOSURE.md`

Historical checkpoint for stationary machinery. Its proposed generic
source/profile determinant bridge was subsequently shown false in that
generality and replaced by source-honest finite-staircase work.

### `HANDOFF_2026-09-11_HC4_FINAL_CLOSURE.md`

Historical source/contact/ray provenance checkpoint.

## Historical but still useful

### ray-Schur / Rees obstruction notes

The proved auxiliary `.pr` ray clock, exact clock mismatch, weight bounds and
countertests remain important. The current architecture preserves their main
lesson:

```text
auxiliary ray clock != zero blocker clock.
```

They are not the direct final terminal contradiction path.

### older JC2 closure plans

Generic two-zero projection is indeed full JC2. The current A19.55 branches
retain stronger provenance and close through source-honest geometry instead.
JC2 modules remain valid reusable infrastructure but are not the live
unrestricted closure plan.

### historical phase/status files

Files named `FORMALISATION_STATUS_PHASE*`, `PHASE*.md`, old handoffs and similar
notes record real development history. They are not current proof ledgers.

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

As of certified code checkpoint
`e2783035171d173516a33448615f6cccd4ec9feb` (Lean CI `35237635579`):

> the unrestricted entry and finite rank-one termination architecture, A19.55
> geometry, source-honest other-facet/highest-slice stack, both nonunit
> finite-staircase orientations, unit endpoint/contact/pair-Rees machinery,
> exact unit equal-fibre layer/profile identification, common dual endpoint
> Euler law, unit one-fibre degree trichotomy, and least/greatest unit
> strict-interior selector theorems are Lean verified. The principal remaining
> local mathematics is to eliminate the equal-fibre three diagonal cases and
> the strictly separated unit multi-fibre case using the already-verified
> nonunit finite-staircase closure as the template. Then the remaining work is
> unit endpoint/right-orientation packaging and the existing `.pr` ->
> `.sp/.rq` -> A19/global assembly splice.

This is **not yet a claim that unrestricted HC4 has been proved**.
