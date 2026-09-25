# HC4 final-resolution closing plan — audited 25 September 2026

## 0. Exact audit anchor

This is the authoritative handoff for the current final-assembly branch.

**Branch:** `final-assembly/a18-4-42-termination-frontier`  
**Mathematical head audited:** `52169d950f4ea5a231e2b01f6850728da3c68a15`  
**Head message:** `HC4: repair marked-axis first-contact support extraction`

At audit time:

- the maintainer reports the exact head builds green locally;
- GitHub **Proof inventory export #2241 is green** on the exact head;
- GitHub **Lean CI #4028 is still in progress** on the exact head;
- the most recent completed remote green runs immediately below the latest support-extraction work include:
  - `5a567af2e5872cf5c6f1caabbd4ac5f0cf2590bc` — Lean CI #4021 green;
  - `56d12e296bc79588ec993b7984911e8e73885e5c` — Lean CI #4019 green;
  - `2834326b93d8cbafe07d3b30fb26dfab6af3f4b3` — Lean CI #4017 green;
  - `07eb6f3c8ed4ea96de885311aed5590da147fbd3` — Lean CI #4016 green;
  - `bbdc9563b2a0f3c3f569592ba4862fa9386b6cfe` — Lean CI #4015 green;
  - `3bcb1a419c06d41cf771e2747aff3e0dd0535c4e` — Lean CI #4011 green.

The later commits from `56d12e…` through `52169d…` add coefficient/support provenance for the marked-axis first-contact face and repair compiler/API drift. They do **not** change the soundness boundary below.

A checkbox is marked only for mathematics that has already compiled on the branch. For the latest exact-head additions, distinguish **local green / remote CI pending** from completed remote CI.

---

## 1. Soundness boundary — do not weaken this

The unrestricted determinant-one HC4 front door reduces to proving

```lean
∀ {state},
  AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData state → False
```

and the existing theorem

`planarJC2_of_zeroStrictLowSingularTerminal_impossible`

shows that a uniform contradiction of this remaining singular terminal implies the planar JC2 injectivity interface.

Therefore the final unrestricted endpoint is genuinely **JC2-hard in the present formal architecture**.

Consequences:

- a bare `RepairProgress` is not a contradiction;
- absence of a global successor is not available at the sound carrier;
- an `ActualRankTwoHessianChart` or `ActualRankThreeHessianChart` is geometry, not by itself a contradiction;
- an auxiliary Schur/Rees clock is not a source polynomial endpoint unless source provenance is explicitly retained;
- the marked-axis first-contact face is **not** itself a certified terminal endpoint merely because it carries a distinct collision;
- unrestricted HC4 may be claimed only after the separate planar JC2-hard endpoint is solved and the final root/axiom audits are green.

The project should first finish the four-dimensional **FinalResolution producer** and obtain a clean current-architecture theorem

```
PlanarJC2Injectivity K → HC4(K)
```

then freeze the 4D machinery and solve the isolated planar endpoint.

---

## 2. FinalResolution interface already fixed and green

The only permitted local outputs are:

```lean
inductive AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution (T)
  | polynomialObstruction
      (O : AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction)
  | associatedGradedCollision
      (A : TerminalAssociatedGradedCollisionData K)
```

The consumer is already green:

- `polynomialObstruction` is unconditionally impossible;
- `associatedGradedCollision` is impossible under `PlanarJC2Injectivity K`.

The existing theorem

`gradient_injective_of_hessianDeterminant_one_of_JC2_of_zeroStrictLowSingularFinalResolution`

already performs the final conditional splice once

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty
```

is proved.

No new final-resolution constructor should be added unless there is a genuine polynomial-level endpoint theorem that consumes it.

---

## 3. What is now Lean-verified: the C/D geometric seam is finished

### A. Final local interface

- [x] FinalResolution type.
- [x] JC2 consumer for every permitted constructor.
- [x] Conditional HC4 wrapper from a total FinalResolution producer.

### B. Exact relative-order split

For the retained later kernel opening `J` and common first positive three-Schur order `q`, set `r = J - q`.

- [x] `r = 0 ∨ 0 < r`.
- [x] Positive-relative branch is the existing positive-tail geometry.
- [x] Zero-relative branch exposes a constant normalised 3x3 kernel-column opening.

### C. Positive-relative branch

The positive branch is source-honest through the entire Schur/rank-one pipeline.

- [x] active rank-two branch source-lifts to represented-source Schur geometry;
- [x] binary determinant-closing branch source-lifts;
- [x] exact rank-one clock retains pivot provenance;
- [x] first transverse nonzero coefficient source-lifts;
- [x] first transverse event transports through both removed common factors to the whole family;
- [x] preterminal/exact-closing timing split is finite and source-honest;
- [x] evaluated represented-source point geometry is retained;
- [x] `TopKernelThreeSchurPositiveTailGeometricFrontier` packages the complete positive-relative geometry.

There is **no remaining positive-tail clock/staircase problem**.

The old ledger labels C4/C5/C6 remain conceptually “not yet FinalResolution” only because the geometry has not been converted to one of the two permitted final polynomial-level constructors. Do not reopen C1–C3 or rebuild the rank-one clock.

### D. Zero-relative branch

This branch is also finished geometrically.

- [x] D1 principal second-stage finite frontier.
- [x] D2 all three principal rank-two orientations source-lift.
- [x] D3 rank-one constant tail retains provenance and canonically selects pivot 2 from the physical column-2 opening.
- [x] D4 exact pivot-2 binary clock is reduced to determinant closing / left-right preterminal / left-right exact closing without an unbounded staircase.
- [x] represented-source kernel principal minor is recovered.
- [x] that minor yields represented-state actual rank-two Hessian geometry through a Prop-safe `Nonempty` interface.
- [x] `TopKernelThreeSchurZeroRelativeGeometricFrontier` packages the complete zero-relative geometry.

There is **no remaining zero-relative clock analysis**.

### Unified exact relative geometry

The two branches are already joined by

`TopKernelThreeSchurRelativeGeometricFrontier`

and

`ThreeSchurTangentAtFirstBreak.relativeGeometricFrontier`.

This is now the single top-kernel geometric interface that the E-stage must consume.

---

## 4. New E-stage carrier now present: marked-axis first contact

The branch has moved beyond the older “find an associated-graded collision” sketch.

The exact head contains an honest first-contact construction tied to the represented determinant-one source.

### 4.1 Honest whole-family identity

The natural marked-axis weight is

```
topKernelMarkedAxisNatWeight = (0,1,1,1)
```

and the branch proves

`topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees`:

the marked-axis source inflation of the ordinary reverse-Rees family is exactly the bounded reverse-Rees family for this weight at level `T.topFace.degree`.

### 4.2 Exact associated-graded fibre

The special fibre is exactly

```
initialForm (0,1,1,1) T.topFace.degree T.topKernelReesSource
```

via

`topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm`.

It is proved:

- integral weighted homogeneous;
- independent of coordinate 0;
- Hessian-singular;
- collision-bearing at the literal points `0` and `e₀`;
- those two points are distinct.

These data are packaged by

`TopKernelMarkedAxisFirstContactFaceData`.

### 4.3 Exact relation to the retained singular top face

The latest support/coefficient work proves:

- the transverse `X₀^0` slice of the first-contact fibre equals the corresponding slice of `T.topFace.face`;
- every supported exponent of the first-contact fibre has `d 0 = 0`;
- most importantly:

```
d ∈ firstContactFibre.support
  ↔ d ∈ T.topFace.face.support ∧ d 0 = 0
```

through

`topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero`.

The top-face API now also exposes the exact source provenance needed by this statement:

- `ordinaryDegree_eq_of_mem_support`;
- `source_mem_of_face_mem`;
- `coeff_eq_source_of_ordinaryDegree_eq`.

### 4.4 Critical non-shortcut

Do **not** turn the marked-axis fibre itself into
`TerminalAssociatedGradedCollisionData`.

It is independent of coordinate 0, hence its Hessian has a zero row. Therefore:

- it cannot satisfy the scalar `CertifiedTerminalDirectJumpEndpoint` constructor, which requires a nondegenerate actual Hessian;
- weight `(0,1,1,1)` is not automatically one of the already-certified positive/one-zero/two-zero terminal weight families;
- the collision `0 ~ e₀` on this fibre is expected from coordinate-0 independence and is not itself the terminal contradiction.

The first-contact fibre is a **classification carrier**, not the final endpoint.

---

## 5. Exact current mathematical frontier: E-stage support/refinement classification

The project is no longer blocked on Schur provenance. The next theorem must convert the unified relative geometry plus the marked-axis/top-face support carrier into a permitted FinalResolution object.

The shortest route is to reuse the already-green singular-top-face classification machinery rather than create another Rees hierarchy.

Existing relevant infrastructure includes:

- `T.topFace` is a genuine nonzero ordinary-homogeneous singular face of degree at least 3;
- `T.exposedSingularBoundaryVertex` and the existing rank-three/extreme-boundary machinery;
- `rankThree_crossFacetInitial_or_topFaceOnFacet`;
- `rankThree_crossFacet_or_nonlinearOutside_or_nonlinearConfined`;
- the lower first-nonfacet source/contact pipeline;
- the specialised `.qs` exposed-rank-three reductions;
- existing unconditional terminal polynomial obstruction constructors:
  - `positiveSingleton`;
  - `complementarySupported`;
  - `complementaryExposed`;
  - `balancedRankThree`.

The new support equivalence lets those finite-support/top-face arguments be applied to the **actual collision-bearing marked-axis slice** without guessing which monomials came from the represented source.

### Next theorem family to build

Create a small E-stage interface, for example conceptually

```
TopKernelMarkedAxisFirstContactResolutionFrontier T
```

whose constructors are already-consumable polynomial outcomes, not clocks or repair labels.

The proof should branch only on genuine support geometry and should aim to return one of:

1. an `AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction`; or
2. a refinement to a **different** associated-graded fibre carrying
   `CertifiedTerminalDirectJumpEndpoint` plus a retained distinct exact collision.

Prefer (1) whenever the existing singular-support theorems already give it.

Do not add a generic “rank-two geometry” constructor to FinalResolution.

---

## 6. Recommended next commits — shortest route to conditional HC4

### E0 — status audit / interface adapter

- [x] unified positive/zero relative geometric frontier exists;
- [x] marked-axis collision-bearing first-contact family exists;
- [x] its special fibre is the exact `(0,1,1,1)` initial form;
- [x] exact support identity with `T.topFace.face ∩ {d₀ = 0}` exists;
- [x] exact source coefficient/support provenance exists.

No more E0 infrastructure should be added unless a concrete E1 proof requires it.

### E1 — classify the marked-axis slice using existing top-face geometry

**Immediate next mathematical commit.**

Prove a finite support/refinement split for

`T.topKernelMarkedAxisFirstContactFaceData.fibre`

using

`topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero`

and the existing singular top-face boundary/source machinery.

The split must retain enough data to feed a known endpoint theorem.

Important discipline:

- do not manufacture a torus balance certificate;
- if using a balanced-rank-three consumer, obtain balance from already-retained geometry first;
- otherwise prefer the balance-free rank-three/source split already present in the strict-low chain;
- do not classify the marked-axis face merely from its Hessian singularity, since that singularity is partly forced by coordinate-0 independence.

### E2 — map every E1 branch to a permitted FinalResolution constructor

For each support branch:

- first try `AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction`;
- only if no unconditional obstruction applies, build a further honest associated-graded fibre with a **proved** `CertifiedTerminalDirectJumpEndpoint`.

A useful target theorem shape is

```lean
theorem AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
    .topKernel_finalResolution
    (T : ...)
    : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
```

or an equivalent theorem indexed by the unified top-kernel frontier.

### E3 — splice non-top-kernel branches

Reuse the already-closed A19 geometry for branches outside the residual top-kernel seam.

Do not re-run global restart/descent machinery.

### E4 — total singular-terminal producer

Prove

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty
```

equivalently

```lean
∀ T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData ...,
  Nonempty
    (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
```

### E5 — provenance audit

Before calling E complete, verify:

- every obstruction constructor receives the exact hypotheses of its green endpoint theorem;
- every associated-graded collision has an honest polynomial fibre;
- collision points are genuinely distinct;
- the endpoint certificate is actually `CertifiedTerminalDirectJumpEndpoint`;
- no Schur rank label is silently treated as a polynomial endpoint;
- no legacy right-recentered clock is identified with the present ordinary reverse-Rees clock.

---

## 7. F-stage: finish the rigorous conditional theorem immediately after E

Once E4 is green, the conditional theorem is essentially already wired.

### F1

Instantiate the existing

`gradient_injective_of_hessianDeterminant_one_of_JC2_of_zeroStrictLowSingularFinalResolution`.

### F2

Expose a clean public theorem of the current architecture:

```lean
PlanarJC2Injectivity K →
  ∀ F : MvPolynomial (Fin 4) K,
    hessianDeterminant F = 1 →
    Function.Injective (mvGradientMap F)
```

### F3

Root `HC4.lean`, full build green.

### F4

Run:

- proof inventory;
- escape-hatch audit;
- `#print axioms` / theorem-axiom audit for the public conditional theorem.

At F4 the 4D reduction should be frozen. Further work should move to the isolated planar endpoint.

---

## 8. G-stage: the genuinely unrestricted HC4 step

This remains separate and must not be hidden inside E/F.

The present architecture proves that a uniform contradiction of the singular terminal implies planar JC2. Therefore unrestricted HC4 requires solving the induced planar JC2-hard endpoint.

### G1 — extract the canonical planar counterexample normal form

Start with a hypothetical planar Keller counterexample and use:

- `planarDoublingPotential`;
- the now-frozen HC4 reduction;
- the exact singular-terminal/top-face/first-contact restrictions

to state the strongest standalone planar property `P` forced on any remaining counterexample.

Do not attack arbitrary JC2 before extracting `P`.

### G2 — prove counterexample -> P

This should be mostly reuse of already-green 4D machinery, now read backwards as a normal-form theorem.

### G3 — solve P directly in dimension two

This is the actual new JC2-hard mathematics.

Use the strongest restrictions carried by the final singular terminal—especially the exact top-face and associated-graded support restrictions—rather than a generic planar Jacobian attack.

### G4 — deduce planar JC2

```
PlanarJC2Injectivity K
```

### G5 — deduce unrestricted HC4

Feed G4 into the already-green F theorem.

### G6 — final audit

- root build green;
- no `sorry`, `admit`, new axioms, or unsafe proof escape;
- `#print axioms` clean for the public unrestricted theorem;
- verify the public theorem statement is the intended unrestricted determinant-one HC4 statement.

Only G6 licenses the claim that unrestricted HC4 is formally proved.

---

## 9. What not to do from this head

Do **not**:

- reopen positive-tail rank-one clocks;
- reopen zero-relative binary clocks;
- build another unbounded staircase;
- add another global restart/descent measure;
- use repair progress as a terminal contradiction;
- certify the marked-axis first-contact face itself as a terminal endpoint;
- assume torus balance merely from ordinary homogeneity;
- identify the ordinary reverse-Rees clock with the legacy right-recentered blocker clock;
- add a new FinalResolution constructor just to accommodate unfinished geometry.

The current bottleneck is **support classification / terminal refinement at the E-stage**, not valuation bookkeeping.

---

## 10. One-paragraph fresh-context handoff

At audited head `52169d950f4ea5a231e2b01f6850728da3c68a15`, the positive-relative and zero-relative Schur/clock branches are already source-honest and unified by `TopKernelThreeSchurRelativeGeometricFrontier`; do not reopen C/D. The branch now constructs `topKernelMarkedAxisFirstContactFamily`, proves it is exactly the bounded reverse-Rees family for weight `(0,1,1,1)`, and packages its special fibre as an honest weighted-homogeneous Hessian-singular polynomial with the literal distinct exact collision `0 ~ e₀`. The latest support theorem proves that this fibre has exactly the exponents of `T.topFace.face` with `d₀ = 0`, with exact source coefficient provenance. This marked-axis fibre is **not** itself a certified terminal endpoint because it is independent of coordinate 0. The next task is therefore to use the existing strict-low singular-top-face boundary/source classification to classify/refine this exact zero-longitudinal slice into either an existing `AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction` or a further honest associated-graded collision with a proved `CertifiedTerminalDirectJumpEndpoint`. Once that gives a total `AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty`, the existing wrapper immediately yields the rigorous conditional theorem `PlanarJC2Injectivity K -> HC4(K)`. Freeze the 4D machinery there; unrestricted HC4 then requires the separate JC2-hard G-stage: extract the canonical planar counterexample normal form forced by the singular terminal, prove that normal form impossible, deduce planar JC2, and feed it through the green conditional HC4 theorem.
