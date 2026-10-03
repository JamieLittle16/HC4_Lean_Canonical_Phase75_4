# Generated proof inventory

Files in this directory are produced from the Lean checkout by:

```bash
python3 tools/generate_proof_inventory.py
```

The generator creates:

- `LEAN_MODULE_INDEX.md` — one detailed entry for every local Lean module, including path, module-doc purpose, A18/A19 labels, direct imports, reverse importers, and detected declarations.
- `DECLARATION_INDEX.md` — lookup from declaration spelling to defining module(s), with repeated spellings highlighted as duplicate-infrastructure search prompts.
- `LOCAL_IMPORT_EDGES.md` — exhaustive direct local import adjacency list for the Lean proof DAG.

These files are derived artifacts. Do not edit them manually. If they are committed in a checkout, verify freshness with:

```bash
python3 tools/generate_proof_inventory.py --check
```

The parser is deliberately conservative and is a navigation aid, not a Lean elaborator. For fully-qualified names and actual environment contents, Lean is authoritative.