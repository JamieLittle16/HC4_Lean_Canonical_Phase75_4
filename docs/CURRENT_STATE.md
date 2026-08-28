# Current HC4 Lean proof state

This document is the authoritative **theorem-level status ledger** for the live HC4 final assembly. It answers one question: **what has actually been reduced or proved in Lean, and what remains a live local obligation?**

It is deliberately not a phase diary. Historical `FORMALISATION_STATUS_PHASE*.md` files record useful checkpoints, but they are not current TODO lists.

For the mathematical architecture see `PROOF_ARCHITECTURE.md`. For exact file-by-file paths see `PROOF_PATHS.md`. For exhaustive source inventory see `generated/LEAN_MODULE_INDEX.md` and `generated/DECLARATION_INDEX.md`.

## 1. What the public theorem is trying to prove

The unrestricted target is determinant-one gradient injectivity in four variables:

```lean
F : MvPolynomial (Fin 4) K
hdet : HC4.Polynomial.hessianDeterminant F = 1
⊢ Function.Injective (mvGradientMap F)
```

with the ambient assumptions used by the A19 front door (`Field`, `CharZero`, `IsAlgClosed`).

The current development does **not** require the public input polynomial to be homogeneous, torus-balanced, pre-normalized, or supplied with an external nonlinear degree cap.

## 2. Unrestricted collision entry is already formalized

The front door from a hypothetical noninjective gradient map is implemented by:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalCollisionNormalization.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalCollisionAutoDegree.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4Reduction.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean`

The important established facts are:

1. a distinct exact gradient collision can be normalized into the canonical axis form;
2. the nonlinear degree cap can be chosen canonically from the polynomial itself;
3. the normalized collision enters the scale-aware canonical Smith/Rees state machine;
4. the reachable-terminal reduction retains the canonical rank-one repair equality instead of quantifying over arbitrary unrelated terminal states.

Therefore the remaining proof is **not** an entry-normalization problem.

## 3. The only rank-one recursion is complete

The global rank-one recursive object is:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean`

`AdaptiveAlignedSmithCanonicalRankOneTerminationTrace` has only two constructors:

```text
terminal geometry
restart globalProgress rawDefect_lt repair_eq tail
```

and recurses only on the natural number `source.rawDefect`.

This is a completed termination mechanism, not a remaining design problem. Final assembly must not invent a second rational clock, cross-scale well-founded order, repair-rank recursion, or parallel trace unless a new theorem first proves the existing trace cannot express the required successor.

Structural consumption of the trace is already isolated in:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean`

## 4. Successful positive Rees steps are already absorbed into that trace

The important A19 correction is implemented by:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceProgress.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction.lean`

A successful positive transverse Rees coefficient bound at an **actual rank-one trace state** gives exactly:

- global macro progress;
- strict decrease of actual `rawDefect`;
- unchanged repair state.

So successful Rees moves are ordinary restart edges of the existing rank-one trace.

`AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace` retains a rank-one trace after all such immediately successful Rees bounds have been consumed.

## 5. Positive reached rank-three states are not local terminal obligations

This is the key current global theorem:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneReesRankThreeClosure.lean` (A19.45)

It proves, at the actual state reached by the Rees-reduced trace:

```text
rawDefect = 0
OR
∃ target, AdaptiveAlignedSmithCanonicalGlobalMacroProgress target reachedState
```

Consequently:

> **Any reached rank-three state which is terminal for the outer global macro order has literal raw defect zero.**

This supersedes older status descriptions in which positive low layers were listed as final local obligations. Positive geometry may still be useful internally for proving the global successor, but it is not the live terminal branch after A19.45.

## 6. The live local terminal is zero-clock strict-low

A19.46 first reduced the locally terminal situation to one zero-clock blocker first-contact producer:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneReesFinalOutcome.lean`

That producer was subsequently removed from the live interface. The producer-free local terminal is:

- `HC4/Valuation/AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean` (A19.53)

It retains the actual:

- reached state;
- canonical rank-one repair equality;
- presented blocker;
- source raw defect equality `= 0`;
- represented strict-low Smith exponent;
- proof that the exponent has one of the three genuinely strict-low patterns.

Thus the current local problem is not “construct some endpoint.” It starts from concrete data already present on the reached terminal state.

## 7. The zero-clock strict-low carrier has already been strengthened substantially

The active chain is:

```text
A19.49  residual normal form
A19.50  exact same-exponent mixed degree
A19.51  zero-clock packet
A19.52  honest first-contact Hessian geometry
A19.53  producer-free zero strict-low terminal
A19.54  retained singular maximal ordinary top face
A19.55  balance-free boundary rank split
A19.56  actual finite-support boundary strata
A19.57  recentered positive longitudinal support
A19.58  rank-three top-face cross-facet/confinement split
A19.59  first-nonfacet source hypotheses
A19.60  direct-cross / lower-outside / confined source split
A19.61  low-negative actual source support
A19.62  low-negative confinement facet elimination
A19.63  pure-longitudinal actual source support
A19.64  pattern-sensitive confinement classification
A19.65  low-degree tame or literal quadratic square
A19.66  honest lower first-nonfacet cross-facet carrier
A19.67  balance-free finite-support affine ray
A19.68  prescribed-positive singular boundary exponent
A19.69  genuine transition away from the starting facet
A19.70  exact rank-three boundary residual reduction
```

The detailed files and inputs/outputs are listed in `PROOF_PATHS.md`.

## 8. Exact current boundary frontier

At A19.55 the singular nonlinear maximal ordinary top face exposes an actual boundary exponent with the exhaustive balance-free split:

```text
rank three on one coordinate facet
OR
codimension two on two coordinate boundaries.
```

The **rank-three branch** has now been refined through A19.70 to the following provenance-honest alternatives:

1. a genuine boundary transition on the actual maximal top face;
2. a genuine boundary transition on an explicitly retained lower first-contact carrier;
3. a literal omitted-coordinate quadratic square in the represented source;
4. complete nonlinear source confinement to the starting facet, with pattern-sensitive restrictions already proved on which facets can survive.

The lower first-contact carrier is intentionally not transported back to the top face.

The **codimension-two branch** remains a distinct boundary branch and should not be silently identified with the rank-three branch or with the two-zero/JC2 route without a theorem that supplies the required hypotheses.

## 9. What is already closed and should not be reopened

The following are not current missing pieces:

- arbitrary-collision normalization;
- automatic nonlinear degree-cap entry;
- rank-one well-founded termination;
- structural trace collapse;
- successful positive Rees restart integration;
- positive reached rank-three local elimination (A19.45 sends it to outer global progress);
- surviving zero-clock strict-low constructor case;
- zero-clock no-strict-low terminal case;
- construction of concrete strict-low residual factorizations;
- existence of same-exponent mixed-degree support and first longitudinal departure;
- zero-linear-jet first-contact Hessian exposure;
- existence of a singular maximal ordinary top face;
- generic balance-free boundary rank split;
- generic finite two-sided cross-facet exposure;
- generic balance-free finite-support affine ray extraction;
- forcing a singular boundary exponent to retain positivity in a prescribed coordinate;
- low-degree-tame versus literal quadratic-square exhaustiveness.

Before creating infrastructure in one of these categories, find and reuse the existing owner.

## 10. Older residual-resolver interfaces are milestones, not the live TODO list

Several A19 files deliberately record successive reductions. They remain proved and useful, but newer theorems are stronger.

### A19.24 — `AdaptiveAlignedSmithCanonicalFinalResidualResolver`

Had three fields:

- zero strict-low;
- positive low layer;
- positive Rees re-entry.

### A19.26 — constructor-specific refinement

Separated blocker/surviving constructors and discharged crossed impossible cases.

### A19.34b — Rees-reduced resolver

Deleted the successful positive Rees-reentry field by inserting success into the existing raw-defect trace.

### A19.35 — source-order low-layer refinement

Split a positive low layer into actual special-fibre support or a genuinely earlier positive actual parameter layer.

### A19.45 — global rank-three closure

Stronger still: a positive reached rank-three state is outer global progress, so positive low-layer cases are no longer terminal local obligations.

### A19.46 → A19.53

A19.46 isolated one zero-blocker first-contact producer. A19.53 removed the producer and retained the actual strict-low terminal data directly.

**Rule:** when deciding what remains, start from A19.45/A19.53 and the newest zero-strict-low modules, not from the older resolver structures.

## 11. Current proof claim

The repository contains a very large, kernel-checked reduction and local-geometry development, but this status document should not claim unrestricted HC4 until a top-level theorem closes **every** live terminal branch and is included in the audited root build.

The correct final milestone will be an unconditional theorem of the public determinant-one gradient-injectivity form, with no resolver/producer/terminal-impossibility argument supplied by the caller.

Until that theorem exists, describe the project as being in final local assembly, not as a completed proof of unrestricted HC4.

## 12. How to update this document

Update `CURRENT_STATE.md` whenever a change does one of the following:

- removes a residual branch;
- replaces a producer/hypothesis with constructed data;
- changes the strongest global/local split;
- changes the active terminal carrier;
- produces the final unconditional HC4 theorem.

Do **not** update it for ordinary compile repairs or helper lemmas that do not change the proof frontier.