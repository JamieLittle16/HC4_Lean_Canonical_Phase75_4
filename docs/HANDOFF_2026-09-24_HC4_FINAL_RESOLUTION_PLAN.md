# HC4 final-resolution closing plan — 24 September 2026

## Purpose

This is the authoritative closing plan for the current unrestricted HC4 final-assembly branch.

**Branch:** `final-assembly/a18-4-42-termination-frontier`  
**Plan anchor:** PR #34 branch `final-assembly/a18-4-42-termination-frontier`  
**Current positive-tail verification frontier:** C1--C3 are Lean-verified on the rooted branch. The exact source-honest rank-one endpoint split is also locally Lean-verified: the rooted build reached `AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailTimedFrontier` at target `8627/8631`, so `PositiveTailRankOneSourceHonestEndpointSplit` and its dependencies compiled before the timed-adapter constructor-name failure. That timed-adapter drift was repaired in `b16c11a66232f0b5bdd49d36b74e90c444969283` without discarding the retained nonzero coefficient/source geometry. Since then the branch has added the represented-source exact collision `b3849a482d3bcdc4125646e2c2bfb18a473edbcb`, evaluated represented-source Schur geometry `a1724d42d4654da50b9be6e2ea06768b3ab20176`, explicit represented-source 3x3 point-minor geometry `0090cf32e98589b11fc4db1496d681794e02f2f5`, and the rooted `TopKernelThreeSchurPositiveTailGeometricFrontier` in `d5852129e7ff6358809830c828d5768129aa3729` / `b49894d9dc81de515e227991c5d85b970f4ee90f`. Those newer geometric modules are **not** checked as complete until a real Lean build runs green; the current GitHub Actions run is `action_required` with no jobs, so it is not verification evidence.

A checkbox in the implementation ledger is marked **only after the corresponding Lean theorem/file has compiled successfully on the branch**. Paper arguments, plausible routes, or documentation-only commits do not earn a checkmark.

### Verified checkpoints added under this plan

- **A green:** rooted build commit `03398974de19849ea6c9615b308e67aa7ae2d1a9`.
- **B green:** `10674ec6763f87db769b0af8d5448c1ac19eebf9`.
- Both passed the full **Build and verify Lean project** workflow before their boxes were checked.
- **C3 source-provenance chain green:** substantive head `8409236e1afd24adc0a3e4d5357bbcb1cdde88f5`. The rooted closing target set reaches `8624/8624` locally, including represented-source Schur provenance, dependent rank-one source departure, and exact whole-family first-transverse opening transport.
- **Exact rank-one endpoint split locally green:** the later rooted build reached target `8627/8631` before failing in the downstream timed adapter, so the strengthened `PositiveTailRankOneSourceHonestEndpointSplit` itself is compiled. This is C4/C5 infrastructure only; C4 and C5 remain unchecked.

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
- [x] Whole-family positive-tail binary Schur provenance is retained through the common three-Schur and binary factors.
- [x] Every positive-tail explicit binary clock yields a genuine nonzero Schur polynomial on the represented determinant-one source.
- [x] Every nonzero transverse coefficient of the final oriented rank-one clock is traced back to honest represented-source Schur geometry; in particular the canonical first transverse coefficient is source-honest.
- [x] The canonical first transverse event is transported back through both removed common factors to an exact whole-family first opening at its physical parameter order.
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

- [x] **C1.** Consume `TopKernelThreeSchurPositiveTailRankOneFrontier.activeRankTwo` source-honestly.

  **Lean-verified:** `TopKernelThreeSchurClockData.activeRankTwo_representedSourceSchurWitness` turns the nonzero active 2×2 tail minor into a branch-independent nonzero represented-source Schur polynomial. Lean CI #3907 compiled this theorem.
- [x] **C2.** Consume the binary determinant-closing branch source-honestly.

  **Lean-verified:** `PositiveTailExplicitBinaryClockData.representedSourceSchurWitness` forgets every explicit binary clock, including the determinant-closing branch, to a represented-source `schurA`/`schurB`/`schurC` witness. Lean CI #3907 compiled this theorem.
- [x] **C3.** For the exact rank-one-clock branch, use `pivot0`/`pivot1` provenance plus the retained later opening to transport the first nonzero binary Schur coefficient back to honest represented-source geometry.

  **Lean-verified C3 chain:**
  - `PositiveTailExplicitBinaryClockData.wholeFamilySchurProvenance`;
  - `PositiveTailExplicitBinaryClockData.representedSourceSchurGeometry`;
  - `PositiveTailExplicitRankOneClockData.transverseCoeff_representedSourceGeometry`;
  - `PositiveTailExplicitRankOneClockData.firstTransverse_representedSourceGeometry`;
  - `PositiveTailExplicitRankOneClockData.wholeFamilyFirstTransverseOpening`.

  This is source/provenance closure only: it does **not** by itself prove C4/C5 or the final singular-terminal contradiction.

  **Verified / pending C4-C5 infrastructure:** `PositiveTailRankOneSourceHonestEndpointSplit` is locally compiled and removes the final exact-clock timing ambiguity while retaining the decisive nonzero coefficient, represented-source geometry, and whole-family opening.

  **Rooted/source-complete but still awaiting a permitted green CI run:** the branch now additionally contains:
  - preterminal opening as a literal source-point binary block with determinant `-b^2 ≠ 0`;
  - exact closing as a literal nonzero source-point kernel-curvature event;
  - branch-independent represented-source Schur witnesses as evaluated nonzero 3x3 Hessian minors;
  - `TopKernelThreeSchurPositiveTailGeometricFrontier`, which packages the complete positive-relative finite geometry;
  - a distinct exact marked collision on `T.topKernelReesSource`;
  - exact collision transport through the honest bounded reverse-Rees family;
  - `topKernelMarkedAxisFirstContactFamily`, whose special fibre retains the literal distinct collision `0 ~ e₀`.

  The current GitHub Actions state for the newest heads is `action_required`, so none of these newer declarations earns an additional checked C4/C5 box yet.

  **Exact remaining C4/C5 seam:** construct/certify a genuine weighted associated-graded polynomial fibre from this collision-bearing first-contact geometry and prove that fibre has a `CertifiedTerminalDirectJumpEndpoint` (or produce the other permitted `FinalResolution` constructor). The evaluated Schur block is not itself a polynomial potential.

  Two tempting shortcuts are invalid:
  - the first-contact source scaling should not be called a standard one-zero terminal endpoint merely because one coordinate has been separated; the certified standard weight is `(0,d,a,d-a)` with `0<a<d`, so terminal classification still has to be proved;
  - `AdaptiveAlignedSmithRankOneClosingSourceCarrier` is tied to the legacy right-recentered aligned-endpoint clock, not definitionally to the present ordinary reverse-Rees rank-one clock. Do not populate that carrier by identifying the two clocks.

- [ ] **C4.** Convert the preterminal rank-one-clock outcome to either an actual represented-source principal Hessian minor or a final polynomial/associated-graded endpoint.
- [ ] **C5.** Convert the exact-closing rank-one-clock outcome to a final polynomial/associated-graded endpoint. Reuse the existing negative-square / wedge pattern where possible rather than exporting `RepairProgress`.
- [ ] **C6.** Assemble: every `0 < r` branch produces the final local resolution interface.

### D. Zero relative tail: finite constant-tail closure

When `r = 0`, the first normalised 3x3 coefficient matrix already contains a nonzero kernel-column entry.

- [ ] **D1.** Run the existing principal second-stage frontier directly on the constant tail.

  **Source-implemented and rooted; awaiting permitted CI:** `TopKernelThreeSchurZeroRelativePrincipalFrontier` retains the physical zero-relative kernel opening and reduces the branch to exactly determinant closing / one of three coordinate-principal rank-two pivots / exact binary zero-Schur.
- [ ] **D2.** Principal rank-two case -> honest represented-source geometry / final resolution.

  **Source-implemented and rooted; awaiting permitted CI:** `TopKernelThreeSchurPrincipalPivot.toRepresentedSourceSchurWitness` source-lifts all three principal orientations. The existing `01` lift is reused; the new `02` and `12` lifts use the nested kernel entries plus common-scale noncancellation in the correct `ThreeSchurActivePair` chart. `TopKernelThreeSchurZeroRelativeSourceFrontier` therefore leaves only determinant closing / represented-source Schur geometry / binary zero-Schur.
- [ ] **D3.** Rank-one constant block -> explicit diagonal pivot -> exact binary zero-Schur clock, with source provenance retained.

  The underlying generic theorem already constructs the exact binary clock from `AllTwoByTwoMinorsZero` + nonzero symmetric constant tail, but the current packaged frontier forgets which nonzero diagonal pivot was selected. Retain that pivot explicitly before checking D3.
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

Do not start a new global recursion or arbitrary SL4 state-level covariance layer unless C/D demonstrate that the retained pivots are insufficient. Do not extend the old generic blocker endgame merely to manufacture repair progress. Do not call an auxiliary layer minor a source minor without either whole-family reverse-Rees lifting or an explicit noncancellation theorem. Do not identify the ordinary top-kernel reverse-Rees clock with the legacy right-recentered blocker clock. Do not label the marked-axis first-contact fibre as a certified one-zero endpoint until its actual integral terminal weight is proved.

The immediate objective is now **C4/C5/C6**, while finishing the finite **D3/D4** branch in parallel. C1--C3 and the exact source-honest rank-one endpoint split are already compiled. The branch now retains the represented determinant-one source, moving collision through the reverse-Rees family, a collision-bearing marked-axis first-contact special fibre, evaluated 3x3 Hessian-minor geometry, and the preterminal/closing source-point events. The shortest remaining C seam is therefore the terminal associated-graded **classification/extraction** theorem, not another Schur provenance wrapper. In parallel, D has already been reduced source-level to a finite determinant-closing / represented-Schur / binary-zero-Schur frontier; retain the binary diagonal pivot explicitly and close those alternatives without another staircase. Repair progress is not an acceptable conclusion.
