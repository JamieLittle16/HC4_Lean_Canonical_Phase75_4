# HC4 documentation index

**Authoritative map: 16 September 2026.**

The HC4 repository contains many historical phase notes. They are useful for
provenance, but they must not be treated as simultaneous current TODO lists.
Use the ownership rules below.

## Current authoritative continuation point

### `HANDOFF_2026-09-16_HC4_LAST_MILE_PUBLIC_CLOSURE.md`

This is the preferred context handoff for starting a new session on the live
unrestricted-HC4 closure.

Its certified code baseline is

```text
cf53735baedb4555df9d8a1c6c63cef7cc17fdec
```

with Lean CI run `35139954849` green through the full build, theorem-axiom
audit, negative control, and proof-escape-hatch audit.

It records the now-complete left and right non-unit finite-staircase closures,
the compiled unit endpoint/contact/staircase/pair-Rees stack, the endpoint-only
left unit contradiction, the remaining unit strict-interior and singleton
adapters, and the shortest assembly path through `.pr`, `.sp/.rq`, the
presented-terminal resolver, and the existing public unrestricted HC4
reduction.

For **current implementation status and TODO order**, this handoff supersedes
the earlier 16 September final-assembly handoff, both 15 September handoffs,
and the 12 September paper handoff.

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

Owns the detailed provenance of the locked/contact and highest/pair-Rees
first-variation constructions and, importantly, the warning that the two
endpoint first variations alone do not eliminate all interior staircase
fibres. Its TODO is historical because the non-unit finite staircase has since
been fully closed.

### `HANDOFF_2026-09-16_HC4_FINAL_ASSEMBLY.md`

Owns detailed provenance for the right `(V,1)`, `V>1` mirror and the earlier
final-assembly architecture. Its status table is superseded by the current
last-mile handoff.

### `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

Owns the completed paper-level line-supported Hessian recurrence/rational-map
argument. The relevant primitive highest-slice rigidity is already formalized.

### `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`

Owns the state-free algebra behind the A19.55 same-carrier codimension-two
branch. That branch now has a Lean-verified geometry-bearing local closure.

### `A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`

Prohibition/reference document for the false shortcut

```text
first variation + staircase arithmetic -> degree <= 1.
```

### `STATIONARY_DETERMINANT_COMPARISON_AUDIT_2026-09-15.md`

Reference for the failed generic stationary source/profile determinant
comparison. Do not revive that implication in the final proof.

## Superseded status handoffs

### `HANDOFF_2026-09-15_HC4_FINAL_MULTIFIBER_CLOSURE.md`

Historical checkpoint from before the exposed cross-roof and mirrored
finite-staircase branches were completed. Do not use its source-honest
exposed-roof adapter as the current TODO.

### `HANDOFF_2026-09-15_HC4_FINAL_LEAN_CLOSURE.md`

Historical checkpoint for the stationary machinery. Its proposed generic
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

As of the certified proof checkpoint
`cf53735baedb4555df9d8a1c6c63cef7cc17fdec`:

> the unrestricted entry and finite rank-one termination architecture, A19.55
> codimension-two geometry, lower-`.qs` other-facet reduction, source-honest
> planar/highest-slice stack, both left and right `V>1` finite-staircase
> closures, actual presented rank-two chart lifting, and the unit
> endpoint/contact/staircase/pair-Rees infrastructure are Lean verified. The
> endpoint-only left `V=1` unit branch is also contradictory in Lean. The
> principal remaining local seams are the right endpoint-only unit mirror, the
> surviving strict-interior unit staircase, and the singleton highest-slice
> adapter. After those, the remaining work is predominantly `.pr` parent
> assembly, `.sp/.rq` permutation transport, the existing-architecture
> terminal-resolver splice, and the public unrestricted HC4 theorem.

This is not yet a claim that unrestricted HC4 has been proved.
