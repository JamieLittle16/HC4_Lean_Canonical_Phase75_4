# HC4 documentation index

**Authoritative map: 15 September 2026.**

The HC4 repository contains many historical phase notes. They are useful for
provenance, but they must not be treated as simultaneous current TODO lists.
Use the ownership rules below.

## Current authoritative continuation point

### `HANDOFF_2026-09-15_HC4_PAIR_REES_FINAL_CLOSURE.md`

This is the preferred context handoff for starting a new session on the live
unrestricted-HC4 closure.

It records the current green pair-Rees checkpoint, the Lean-verified locked
and highest endpoint equations, the formal obstruction to the older generic
stationary determinant bridge, the exact remaining finite-staircase coupling
obligation, and the symmetry/unit/facet/global assembly that follows it.

For **current implementation status and TODO order**, this handoff supersedes
the 12 September handoff and the earlier 15 September stationary handoff.

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

These own exhaustive inventory, not mathematical status.

## Current mathematical reference documents

### `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

Owns the completed paper-level line-supported Hessian recurrence/rational-map
argument. It is an independent mathematical reference, not the first Lean
implementation target after the new pair-Rees endpoint work.

### `HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md`

Owns the detailed paper closure for the rank-three no-singleton/developable
fallback and the `V=1` endpoint coefficient calculation. Use it for
mathematics, not current implementation status.

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
comparison. The current pair-Rees handoff explains the replacement route.

## Superseded handoffs

### `HANDOFF_2026-09-15_HC4_FINAL_LEAN_CLOSURE.md`

Important historical checkpoint for the stationary machinery. Its proposed
generic source/profile determinant bridge was subsequently shown to be false
in that generality and has been replaced by the endpoint-sensitive pair-Rees
route. Do not use its Route A/Commit A--D stationary determinant plan as the
current TODO.

### `HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md`

Still valuable for paper mathematics, but much of its formalisation plan has
already landed.

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

- **LEAN VERIFIED** — formalised, rooted, and compiled;
- **SOURCE-LANDED / NOT LEAN VERIFIED** — committed source without a known
  successful exact-head build yet;
- **PAPER CANDIDATE** — a complete paper argument or symbolic derivation exists
  but has not yet been formalised;
- **DIAGNOSTIC ONLY** — useful experiment/counterexample/symbolic evidence that
  is not a proof theorem;
- **OPEN** — a genuine mathematical/formal obligation remains.

Avoid ambiguous labels such as “basically done,” “solved,” or “green” unless
the context makes clear whether this means paper or Lean.

## Current one-line status

As of the green checkpoint `e121f5c206443ff6345b00c2bf2a8b581ae1c831`
(Lean CI #2318):

> the unrestricted entry/termination architecture, A19.55 codimension-two
> geometry branch, rank-three planar/staircase infrastructure, and both honest
> endpoint first-variation equations are Lean verified; the principal remaining
> local mathematical gap is the finite-staircase coupling that forces
> `NoStrictInteriorSupport`, after which the left non-unit two-function
> contradiction is already formal and the remaining work is symmetry/unit/facet
> wrappers plus the final existing-architecture splice.

This is not yet a claim that unrestricted HC4 has been proved.
