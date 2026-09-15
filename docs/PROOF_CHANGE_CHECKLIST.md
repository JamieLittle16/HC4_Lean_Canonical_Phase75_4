# Proof change checklist

Use this checklist before adding or substantially changing HC4 Lean infrastructure. The goal is not bureaucracy; it is to prevent duplicate definitions, accidental hypothesis strengthening, provenance loss, and parallel termination machinery.

## Before creating a new file

1. **State the exact input and output interface.** Write down the carrier you have, the carrier you need, and every hypothesis used.
2. **Search the generated indexes.** Run `python3 tools/generate_proof_inventory.py` and search `docs/generated/LEAN_MODULE_INDEX.md` and `docs/generated/DECLARATION_INDEX.md`.
3. **Search source by concept, not only proposed name.** Try mathematical synonyms and representation words such as `support`, `boundary`, `facet`, `crossFacet`, `initialForm`, `rankThree`, `lowLayer`, `Rees`, `repair`, `rawDefect`, `recenter`, `substitution`, `moment`, `line`, `pencil`, `terminal`.
4. **Check `docs/CANONICAL_OWNERS.md`.** Import the owner module whenever possible.
5. **Check both balanced and balance-free routes.** Do not add balance just to reach an older theorem if a finite-support replacement already exists.
6. **Check carrier provenance.** Verify whether the witness belongs to the source, presented family, special fibre, recentered special fibre, top face, contact face, lower carrier, or exposed ray. Similar formulas do not make these objects interchangeable.
7. **Check clock provenance.** Distinguish source raw defect, presented raw defect, endpoint defect, and actual trace-edge raw-defect decrease.
8. **Check whether the desired progress is already an A18.4.109 restart.** If it gives global macro progress + strict raw-defect decrease + unchanged repair, it belongs in the existing rank-one trace.

## Before declaring a generic-looking name

Search exact and suffix forms:

```bash
rg -n 'face_weight_eq|MvExponentOnBoundary|MvRankThreeOnFacet' HC4
rg -n '^\s*(noncomputable\s+)?(theorem|lemma|def|structure|inductive|abbrev)\b' HC4/path
```

For a structure namespace helper, search the fully-qualified conceptual owner. Two files may compile alone and collide only when a later importer brings both into the same environment.

Prefer a specialized name for a specialized route. For example:

```text
CrossFacetInitialData.face_weight_eq
CrossFacetInitialData.ray_face_weight_eq
```

are deliberately distinct because the first belongs to the older balanced affine-line route and the second to the balance-free ray refinement.

## When creating an adapter

An adapter should normally:

- import the canonical owners;
- retain the exact source object or an explicit equality/subset theorem;
- prove only the conversion needed by the next interface;
- avoid restating foundational definitions;
- avoid new existential choices when an actual witness is already retained;
- say in its module docstring what it **does not** assume.

If the adapter starts reproducing a large algebraic calculation, search for a more appropriate owner theorem first.

## When creating a carrier structure

A carrier is useful when several downstream steps need the **same actual witness** and its provenance. It should record facts that would otherwise be repeatedly reconstructed.

Prefer fields such as:

- actual polynomial/family/face;
- source/support membership;
- exact equality defining a transformed carrier;
- positivity/nonvanishing;
- singularity or determinant facts;
- subset/transport maps;
- repair/raw-defect provenance.

Avoid storing a weaker abstract consequence if the stronger actual witness is already available.

## When proving a branch split

A good split should be exhaustive and concrete. Prefer:

```text
condition holds
OR explicit witness to its failure
```

over:

```text
condition holds
OR opaque residual case
```

Examples already in the tree:

- low-degree tame **or literal omitted-coordinate quadratic square**;
- positive Rees coefficient bound **or concrete low layer**;
- positive omitted-coordinate support **or complete facet confinement**;
- boundary exponent **rank three or codimension two**.

## Termination rules

The canonical global recursion is `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace`, by strict decrease of `rawDefect : ℕ`.

Do not add:

- a rational descent clock;
- a second recursive final-assembly object;
- a semantic “repair promotion” used as termination;
- a cross-scale inequality treated as well founded;

unless there is a proof obligation that genuinely cannot be represented in the existing trace. In that exceptional case, document the obstruction first.

## Balanced versus balance-free rules

Use the balanced route only when an actual balance theorem is in context.

For unrestricted zero-clock finite-support geometry, prefer:

```text
FiniteSupportCrossFacetExposure
    -> FiniteSupportCrossFacetRay
    -> PositiveCoordinateSingularBoundaryVertex
    -> SingularBoundaryRankSplit
```

Do not manufacture torus balance, homogeneity, a cocharacter, or an integral finite-segment parameterization merely to reuse older terminal infrastructure.

## Focused compile before full CI

For a changed file:

```bash
lake env lean HC4/path/to/File.lean
```

or the repository's equivalent focused build command. Then run the full project check:

```bash
lake build
```

and, for certification snapshots:

```bash
./verify.sh
```

A focused file build is not enough to detect duplicate environment declarations across sibling import branches. The full import graph matters.

## Documentation required with structural changes

Update documentation in the same change when you:

- introduce a reusable generic definition;
- add a new live proof route;
- supersede an older route;
- add or remove a residual branch;
- introduce a new state/progress/termination object;
- change which carrier owns a witness;
- rename a canonical helper to resolve an import collision.

At minimum update one of:

- `docs/CANONICAL_OWNERS.md`
- `docs/PROOF_ARCHITECTURE.md`
- `docs/MODULE_CATALOG.md`

and regenerate the machine index.

## Before declaring a patch done

Ask:

- Did I reuse the strongest existing theorem?
- Did I accidentally strengthen hypotheses?
- Is every witness still attached to the carrier where it was proved?
- Did I invent a new representation of an existing concept?
- Does the new theorem name collide when sibling branches are imported together?
- Is new progress represented by the existing raw-defect trace?
- Does the module docstring explain the exact role and non-assumptions?
- Did the exhaustive inventory change in the way I expected?

If all answers are satisfactory and the full build is green, the patch is structurally ready.