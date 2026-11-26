# Publication and verification record

## Registered result

- [Palomar Registry PALOMAR-2026-11-26-000066, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000066&version=1), reported registered 26 November 2026.
- Local Comparator snapshot: [6b9526a](https://github.com/JamieLittle16/HessianConjecture4/tree/6b9526a446b4f2998307fb8d211436ccfbf723e3). Consult the registry for the authoritative registered commit.
- Lean and Mathlib 4.35.0; new module system.
- Maintainer-reported local build: 9,273 jobs. Comparator accepted both advertised equivalences with Lean, NanoDa and con-ron (40,457 declarations verified by con-ron).
- The Challenge imports only Mathlib. Solution imports the existing proof development, not Challenge. The intentional Challenge holes are not proof assumptions.
- Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`.

## Preserved history

- Full exploratory research: [archive/research-2026](https://github.com/JamieLittle16/HessianConjecture4/tree/archive/research-2026), commit `fe55e3fbb6da0b034f8dd2cc434d262047533ed7`.
- Earlier independent clean reproduction: [GitHub Actions run 45855370863](https://github.com/JamieLittle16/HessianConjecture4/actions/runs/45855370863), commit `1377de427f2801e2f9f6b49ce1a07371e60dabb8`.
- Reduced Lean 4.24 publication checkpoint: `1fc3fc2b986b5afb67dd38621e372e13eb6fe549`.
- Successful Lean 4.35 migration: `7842bc5a537092e3d114bae5a31c43d9d89249aa`.
- Module-system conversion: `0a69d9a9eafe56bc6630010f54849bef327212de`.

## Reproduction

```bash
lake exe cache get
lake build HC4 Challenge Solution
lake env lean HC4/Audit.lean
bash scripts/verify-comparator.sh
```

The registry entry covers the two explicit equivalences. The standalone rational affine-plane theorem is retained as a separate, Lean-audited library result. External mathematical review, detailed priority analysis and manuscript peer review remain outstanding. Neither conjecture is proved unconditionally.

Preserve the historical attribution, including Tang, Mathlib and the substantial AI assistance disclosed in the manuscript and metadata. The registered snapshot is immutable; later documentation changes do not update the registry record.
