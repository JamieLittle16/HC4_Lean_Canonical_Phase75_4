# Phase 93.42 — Exact collision discharges Smith low-pattern hypotheses

This patch closes the interface between the exact-axis collision blocker theorems and the abstract Smith grade/refinement layer.

It proves that on the actual projected support of a homogeneous four-coordinate polynomial, the four forbidden projected Smith patterns reconstruct exactly the already-excluded monomials `x^D`, `x^(D-1)z`, `x^(D-1)y`, and `x^(D-1)w`.

Consequently an exact homogeneous axis collision automatically supplies both `HasGeneralSurvivingSmithFaceShape` and the old-face `¬ IsWLinearSmithPattern` hypothesis. The final wrapper feeds these directly into `poleMinimal_symmetricSmithRestriction_rankOnePacket`.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
