# HC4 documentation index

**Authoritative map: 12 September 2026.**

The HC4 repository contains many historical phase notes. They are useful for
provenance, but they must not be treated as simultaneous current TODO lists.
Use the ownership rules below.

## Current authoritative documents

### `CURRENT_STATE.md`

Owns the answer to:

> What is Lean verified, what is only a paper candidate, and what is still
> genuinely open?

If another document disagrees on current status, `CURRENT_STATE.md` wins.

### `PROOF_ARCHITECTURE.md`

Owns the live mathematical architecture and the global/local proof shape.

### `PROOF_PATHS.md`

Owns route lookup: given a carrier/interface, which canonical modules should be
used next and which invalid shortcuts should be avoided?

### `FORMALISATION_PLAN_2026-09-12.md`

Owns the implementation order for turning the current paper closure into Lean.

### `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`

Owns the precise new state-free algebraic theorem for the final A19.55
same-carrier codimension-two branch.

### `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

Owns the completed paper-level line-supported Hessian recurrence/rational-map
argument used by the rank-three other-facet branch.

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

## Current handoff

`HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md` is the preferred context handoff for
starting a new session after the 12 September paper closure work.

## Historical but still useful

### `HANDOFF_2026-09-11_HC4_FINAL_CLOSURE.md`

Historical checkpoint immediately before the 12 September closure. Its
source/contact/ray provenance remains useful, but any statement that the
source-honest rank-three exclusion or A19.55 same-carrier codimension-two
contradiction is still the current open paper gap is superseded by the
12 September documents.

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
retain stronger provenance and have a paper route that closes before generic
JC2. JC2 modules remain valid reusable infrastructure but are not the live
unrestricted closure plan.

### historical phase/status files

Files named `FORMALISATION_STATUS_PHASE*`, `PHASE*.md`, old handoffs and similar
notes record real development history. They are not current proof ledgers.

## Status vocabulary

Every new progress document should use only:

- **LEAN VERIFIED** — formalised and compiled;
- **PAPER CANDIDATE** — a complete paper argument is currently available but
  has not yet been formalised;
- **OPEN** — a genuine mathematical/formal obligation remains.

Avoid ambiguous labels such as “basically done,” “solved” or “green” unless the
context makes clear whether this means paper or Lean.

## Current one-line status

As of 12 September 2026:

> unrestricted entry and global rank-one termination are Lean built; both
> A19.55 local branches have a complete paper candidate closure; the remaining
> project is to formalise those local arguments, splice them into the existing
> geometry-bearing descent, and obtain a green audited unrestricted HC4 theorem.

This is not yet a claim that HC4 has been proved.
