# Phase 93.47 — Local restart classification assembly

Built against the exact green Phase 93.46 restart-assembly checkpoint.

## What is closed in this phase

### 1. Constructive finite restart recursion
`FiniteRepairTermination` now contains:
- `RepairReachable`;
- transitivity and measure monotonicity;
- `HasRepairOrTerminal`;
- `IsTotalRepairClassifier`;
- `repairClassifier_reaches_terminal`.

Thus, once every nonterminal local state supplies `RepairProgress`, Lean
constructively proves that a terminal state is reached after finitely many
repairs.

### 2. One common local branch API
The canonical Smith wall, mixed first departure, and rank-two Schur entry
are each converted to:

    terminal certificate OR exists t, RepairProgress s t.

Entry points:
- `smithFirstWall_hasRepairOrTerminal`
- `mixedDeparture_hasRepairOrTerminal`
- `rankTwoSchurEntry_hasRepairOrTerminal`

### 3. Unified endpoint dispatch under JC2
`CertifiedTerminalEndpoint` packages the currently closed:
- strictly-positive terminal face;
- standard one-zero endpoint;
- standard two-zero endpoint.

Then:
- `certifiedTerminalEndpoint_gradient_injective_of_JC2`
- `certifiedTerminalEndpoint_collision_impossible_of_JC2`

give the single endpoint theorem wanted by the eventual global restart.

### 4. Umbrella import
`HC4/Newton.lean` now imports `HC4.Newton.RestartClassification`, so the
new assembly participates in the ordinary project build.

## Important scope boundary

This phase deliberately does NOT claim the full DVR/global
`RestartClassification` theorem from the handwritten blueprint.

The current tree still needs the global extraction layer that starts from an
HC4 counterexample / exact integral collision datum and proves that every
geometric restart state is represented by one of the local classifiers
formalised above, while preserving the marked collision through
ramification/kernel blow-up.

Phase 93.47 closes the well-founded LOCAL recursion once that geometric
one-step extraction is supplied.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
