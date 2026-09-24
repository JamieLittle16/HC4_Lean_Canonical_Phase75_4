# HC4 final-resolution closing plan — 24 September 2026

## Purpose

This is the authoritative closing plan for the current unrestricted HC4 final-assembly branch.

**Branch:** `final-assembly/a18-4-42-termination-frontier`  
**Plan anchor:** PR #34 head `a870782df2ccf43fdb9ca0d210e7d0cbfb6659fb`  
**Last substantive Lean-green head before this plan:** `7c9add8731b824de4f71e6f03d55d319cf632dae`

A checkbox in the implementation ledger is marked **only after the corresponding Lean theorem/file has compiled successfully on the branch**. Paper arguments, plausible routes, or documentation-only commits do not earn a checkmark.

### Verified checkpoints added under this plan

- **A green:** rooted build commit `03398974de19849ea6c9615b308e67aa7ae2d1a9`.
- **B green:** `10674ec6763f87db769b0af8d5448c1ac19eebf9`.
- Both passed the full **Build and verify Lean project** workflow before their boxes were checked.

## Soundness boundary

The unrestricted front door reduces HC4 to

```lean
∀ {state},
  AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData state → False
```

and the existing theorem
`planarJC2_of_zeroStrictLowSingularTerminal_impossible`
shows that a uniform proof of this remaining singular-terminal impossibility implies the planar JC2 injectivity interface.

Therefore the remaining unrestricted endpoint is genuinely JC2-hard in the present formal architecture. In particular:

- do **not** close the singular terminal by a bare `RepairProgress`;
- do **not** use a no-global-successor hypothesis: the sound final singular carrier has no such assumption;
- an `ActualRankTwoHessianChart` is useful geometry, but is **not by itself** a contradiction at this endpoint;
- auxiliary Schur/Rees clocks must retain enough provenance to produce an honest source/polynomial endpoint;
- unrestricted closure is claimed only after the public theorem, root build and final axiom/proof audits are green.

## Green prerequisites already available

- [x] Unrestricted determinant-one HC4 reduces soundly to zero-strict-low singular-terminal impossibility.
- [x] The hardness guard `planarJC2_of_zeroStrictLowSingularTerminal_impossible` is Lean verified.
- [x] The top-kernel ordinary reverse-Rees family is source-honest and carries the exact determinant clock.
- [x] The first physical kernel-row opening is lifted to an exact nonlinear mixed source layer.
- [x] The tangent first-break branch is reduced to a linear-power kernel derivative and explicit staircase seed.
- [x] A strictly later projected kernel-column opening `J > j` is retained.
- [x] The three-Schur tail transport and positive-tail collapse are Lean verified.
- [x] The positive-tail residual reaches either explicit rank-two coefficient geometry, determinant closing, or an explicit oriented exact rank-one binary Schur clock with pivot provenance.
- [x] Whole-family reverse-Rees principal Hessian minors lift back to represented-source principal minors.
- [x] Existing actual-rank-two and actual-rank-three geometry consumers are available, but must not be mistaken for final contradiction at the sound singular endpoint.

## Implementation ledger

### A. Final local resolution interface

- [x] **A1.** Add a definitive singular-terminal resolution type carrying only sound final objects:
  - an honest unconditional polynomial obstruction/contradiction object; or
  - an honest `TerminalAssociatedGradedCollisionData` endpoint suitable for the existing JC2 consumer.
- [x] **A2.** Add the corresponding consumer theorem:
  under planar JC2, every value of this resolution type is contradictory.
- [x] **A3.** Add a singular-terminal-to-resolution property and splice it to a clean conditional `JC2 ⇒ HC4` theorem.

**Rule:** no repair-only constructor and no global-progress-only constructor.

### B. Replace the coarse tail split by the exact relative-order split

Let `J` be the retained later projected kernel opening and `q` the common first positive three-Schur quotient order. Set

```
r = J - q.
```

- [x] **B1.** Package the exact dichotomy `r = 0 ∨ 0 < r`.
- [x] **B2.** Show the `0 < r` branch is exactly the already-developed positive-tail branch, without losing physical-order provenance.
- [x] **B3.** Expose the `r = 0` branch as a constant normalised 3x3 kernel-column opening.

The older `q ≤ j` versus fully-tangent split remains useful internally but is no longer the assembly-facing split.

### C. Positive relative tail: exact rank-one clock to honest endpoint

- [ ] **C1.** Consume `TopKernelThreeSchurPositiveTailRankOneFrontier.activeRankTwo` source-honestly.
- [ ] **C2.** Consume the binary determinant-closing branch source-honestly.
- [ ] **C3.** For the exact rank-one-clock branch, use `pivot0`/`pivot1` provenance plus the retained later opening to transport the first nonzero binary Schur coefficient back to honest represented-source geometry.
- [ ] **C4.** Convert the preterminal rank-one-clock outcome to either an actual represented-source principal Hessian minor or a final polynomial/associated-graded endpoint.
- [ ] **C5.** Convert the exact-closing rank-one-clock outcome to a final polynomial/associated-graded endpoint. Reuse the existing negative-square / wedge pattern where possible rather than exporting `RepairProgress`.
- [ ] **C6.** Assemble: every `0 < r` branch produces the final local resolution interface.

### D. Zero relative tail: finite constant-tail closure

When `r = 0`, the first normalised 3x3 coefficient matrix already contains a nonzero kernel-column entry.

- [ ] **D1.** Run the existing principal second-stage frontier directly on the constant tail.
- [ ] **D2.** Principal rank-two case -> honest represented-source geometry / final resolution.
- [ ] **D3.** Rank-one constant block -> explicit diagonal pivot -> exact binary zero-Schur clock, with source provenance retained.
- [ ] **D4.** Close the resulting finite binary alternatives without introducing another unbounded staircase.
- [ ] **D5.** Assemble: every `r = 0` branch produces the final local resolution interface.

### E. Singular terminal -> final resolution

- [ ] **E1.** Assemble the non-top-kernel branches already closed by existing A19 geometry.
- [ ] **E2.** Insert C and D for the residual top-kernel branch.
- [ ] **E3.** Prove the canonical producer

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  -> Nonempty ZeroStrictLowSingularFinalResolution
```

(or the equivalent indexed theorem).

- [ ] **E4.** Audit that every constructor retains genuine source/polynomial provenance and that no auxiliary rank label is identified with a terminal polynomial endpoint.

### F. Rigorous conditional endpoint

- [ ] **F1.** Use E plus the existing terminal JC2 consumer to prove a clean current-architecture theorem `PlanarJC2Injectivity K -> HC4(K)`.
- [ ] **F2.** Route the theorem through the public determinant-one gradient-injectivity entry.
- [ ] **F3.** Root build green.
- [ ] **F4.** Axiom/proof audit green for the conditional theorem.

At F4 the project has a rigorous, current, source-honest conditional endpoint. This does **not** claim unconditional HC4.

### G. Unconditional JC2-hard endpoint

After F is green, freeze the four-dimensional global machinery.

- [ ] **G1.** Starting from a hypothetical planar Keller counterexample, use `planarDoublingPotential` and the canonical HC4 reduction to extract the exact additional normal-form restrictions imposed by the singular terminal.
- [ ] **G2.** State the resulting canonical planar counterexample property `P` as a standalone theorem/interface.
- [ ] **G3.** Prove `PlanarJC2 counterexample -> P`.
- [ ] **G4.** Prove `P -> False`.
- [ ] **G5.** Deduce planar JC2.
- [ ] **G6.** Deduce unrestricted HC4 from the already-green HC4 reduction.
- [ ] **G7.** Full root build, `#print axioms`/proof audit and public theorem audit green.

Only G7 licenses an unrestricted-HC4 claim.

## Preferred commit order

```text
A  FinalResolution interface
B  exact r = J-q split
C  r>0: exact rank-one-clock -> honest endpoint extraction
D  r=0: constant-tail finite closure
E  singular terminal -> final resolution
F  clean JC2 => HC4 splice + audits
G  isolate and solve the canonical JC2-hard planar endpoint
```

## Stop conditions / anti-detours

Do not start a new global recursion or arbitrary SL4 state-level covariance layer unless C/D demonstrate that the retained pivots are insufficient. Do not extend the old generic blocker endgame merely to manufacture repair progress. Do not call an auxiliary layer minor a source minor without either whole-family reverse-Rees lifting or an explicit noncancellation theorem.

The immediate objective is now **C**: transport the explicit positive-relative binary/rank-one Schur data back to an honest source or terminal endpoint without using repair progress as the conclusion.
