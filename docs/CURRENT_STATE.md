# Current HC4 Lean proof state

This document is the authoritative **theorem-level status ledger** for the live HC4 final assembly. It answers one question: **what has actually been reduced or proved in Lean, and what remains a live local obligation?**

It is deliberately not a phase diary. Historical `FORMALISATION_STATUS_PHASE*.md` files record useful checkpoints, but they are not current TODO lists.

For the mathematical architecture see `PROOF_ARCHITECTURE.md`. For exact file-by-file paths see `PROOF_PATHS.md`. For exhaustive source inventory see `generated/LEAN_MODULE_INDEX.md` and `generated/DECLARATION_INDEX.md`.

## Ray Schur route: local clock proved, source connection open (2026-09-08)

The sharp coefficient bounds now have an actual `.pr` ray-Rees adapter in
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRaySchurWeightBounds`:
all three raw Schur entries vanish at every parameter order at least the ray
defect. Both complementary weights are strictly below half the source level.
The local ray rank-one Schur clock is now constructed in
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayExactSchurClock`.
Its theorem
`QsOtherFacetRayReverseReesPackage.pr_exists_exact_preterminal_schurClock`
takes only the retained ray Rees package and the actual `.qs`/`.pr` endpoint
hypotheses. It returns an exact clock with the ray defect, a literal left or
right constant alignment of the actual ray Hessian Schur block, strict
`firstOrder < defect`, and a nonzero off-diagonal coefficient at that order.

The missing constant pivot is supplied by
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayConstantSchurMinor`.
The principal Hessian minor on coordinates (1,2,3) has constant longitudinal
coefficient `c0^3*A*B*C*(A+B+C-1)` after the established ray specialisation.
Positive integral A,B,C and the retained nonzero endpoint coefficient make
this nonzero. The file identifies this same minor with the constant
`.pr` Schur C entry on the ray reverse Rees. No Hessian-rank assumption,
division, source-presentation assumption or closing-order exclusion is added
to the clock theorem. The existing all-three coefficient bounds rule out
closing after either constant alignment.

The local clock and constant-minor modules compiled in Lean CI #1587 at
`27d0b0c59d8f754896f903c610fa31d6ceca9290`.

The proposed direct use of stationary `GlobalStationaryRankTwoProgress.ofGeometry`
is blocked by an exact clock mismatch, not an elaboration problem.
`ZeroStrictLowTerminalData.zeroClockFirstContactPacket.2.1` gives
`terminal.blocker.blocker.aligned.endpoint.defect = 0`.
The ray package gives `0 < 4*level - 2*sum weight`.
The new `AdaptiveAlignedSmithCanonicalZeroStrictLowRaySchurClockCompatibility`
proves that no exact rank-one Schur clock, and hence no corresponding recentered
rank-one Schur chart, exists on the retained original blocker. It also proves
that the ray defect differs from the original blocker defect and from every
natural ramification multiple of the source defect.

These facts do not refute an auxiliary ray clock. They rule out identifying it
with the original stationary clock. A viable global route must construct a
new certified source transition and show that the resulting geometric progress
is consumed by the terminal-exclusion argument. Merely constructing a state
with a smaller repair tag does not do this: `GlobalMacroProgress` is an order
relation, and the local terminal record has no assertion that all such smaller
states are impossible. No direct reverse-Rees source-transition adapter was
found in the global/certified progress owners audited here.

**Status:** the actual `.pr` ray clock and strict preterminal departure are proved.
Source-honest terminal exclusion remains open.
The exact Hessian-one countertest in [RAY_FULL_TO_BINARY_OBSTRUCTION.md](RAY_FULL_TO_BINARY_OBSTRUCTION.md)
shows why full determinant-layer vanishing, positive Rees weights, the quadratic
margin and Euler identities do not by themselves imply binary profile-layer
vanishing. The test does not satisfy the retained rank-three endpoint geometry;
using that additional geometry to control coupling remains the missing argument. No `.pr` impossibility or unrestricted HC4 theorem is claimed.
The same-carrier codimension-two contradiction remains a separate obligation.

A new model calculation is recorded in
[RAY_KERNEL_EXTREMAL_ELIMINATION.md](RAY_KERNEL_EXTREMAL_ELIMINATION.md).
Two successive extremal determinant equations eliminate the nonlinear
first-layer coefficient in a rank-three model, even with all permitted later
corrections in the tested weight system. The scalar elimination is compiled and verified in Lean: full CI #1591 passed
at `d7467cc39d36aefe5e0ff40e3b67fdba68b6ca51`, including the axiom audit,
negative control and escape-hatch checks. The generic quadratic/cubic elimination and first-order boundary corollary
also passed full CI #1593 at `9cd89d77c5a81c550cc966bdd567ae8c73545e10`.
The first-order model excludes its two-coordinate quadratic boundary terms,
but a mixed `x^2*z*w` term survives and can affect later layers. The source
coefficient extraction and coverage of arbitrary terminal rays remain open.

**Omitted-term resolution in the model:** the missing `k*y*u^2` term is now
eliminated by the highest longitudinal coefficient
`[t^4*x^4] det Hess = 14580*k^2*w^4*z^4`. The exact symbolic check includes
all 27 first-layer kernel monomials and every permitted later correction.
This supplies `k=0` before the earlier six equations are applied.
`LongitudinalRankTwoInitialCoefficient.lean` records the finite-block identity
with arbitrary polynomial tails (CI pending). The source identification and
coverage of arbitrary terminal geometry remain open; this is a model result.
See the resolution and the historical scope correction in
`RAY_KERNEL_EXTREMAL_ELIMINATION.md`.

The product-coordinate branch now has a source-level Lean implementation in
`HC4/Newton/ProductCoordinateHessian.lean` (full CI #1596 passed at
`fb223970a284a82ca64634fb11c6c451c30cfe64`): for an actual
`F=f(x,y,z*w)`, determinant one forces the substituted `f_h` to be constant.
This is conditional on the whole source having that form; the terminal support
argument needed to invoke it remains open. A follow-up adds coefficient
exclusion and `QsOtherFacetRayReverseReesPackage.source_ne_productCoordinateLift`,
which applies the obstruction to the actual retained terminal source. Full
CI #1601 passed at `8cab1f3d01147470d687db6fa6802ae228fb1f3c`, including
the axiom audit, negative control and escape-hatch checks.

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

In particular, `gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible` already provides the unrestricted determinant-one conclusion once final assembly supplies an unconditional contradiction for every canonical presented terminal. The live mathematical task is therefore terminal closure, not construction of another global HC4 entry theorem.

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
A19.71  exhaustive zero-clock terminal residual assembly
A19.72  contact-zero affine ray to RationalRigidity terminal or codimension two
A19.73  `.qs` strict-low ray reduction with retained carrier provenance
```

The detailed files and inputs/outputs are listed in `PROOF_PATHS.md`. A19.72 and A19.73 are kernel-checked on the live final-assembly branch; their residual types deliberately retain light geometric carriers and reconstruct the large RationalRigidity certificate only when consumed.

## 8. Exact current boundary frontier

At A19.55 the singular nonlinear maximal ordinary top face exposes an actual boundary exponent with the exhaustive balance-free split:

```text
rank three on one coordinate facet
OR
codimension two on two coordinate boundaries.
```

A19.71 combines the rank-three reduction with the original codimension-two half, leaving only five provenance-honest zero-clock alternatives:

1. a genuine boundary transition on the actual maximal top face;
2. a genuine boundary transition on an explicitly retained lower first-contact carrier;
3. a genuine codimension-two boundary exponent;
4. a literal omitted-coordinate quadratic square in the represented source;
5. complete nonlinear source confinement to the starting facet.

For the marked `.qs` rank-three branch, A19.73 strengthens this further. The complete nonlinear-confinement branch is impossible from the actual strict-low source witnesses. Each cross-facet branch retains an exact contact-coordinate-`0` balance-free affine ray. By A19.72 its facet endpoint is either:

```text
rank three on `.qs`, hence carrying the complete general affine RationalRigidity terminal certificate
OR
codimension two.
```

The RationalRigidity certificate is reconstructed canonically from the retained ray rather than duplicated inside the A19.73 residual type. This avoids expensive dependent normalization while preserving all support, first-contact, endpoint and affine-slope provenance.

The **codimension-two branch** remains a distinct boundary branch and should not be silently identified with the rank-three branch or with the two-zero/JC2 route without a theorem that supplies the required carrier hypotheses.

The subsequent A19.80--A19.95 reductions and the current contact calculation
are recorded below. The older affine-direction task is not the current
closing gate.

### 8a. Current exposed-`qs` frontier and exact PR calculation

`qs_rankThree_startCodimensionTwo_or_lockedOtherFacet_or_quadraticSquare`
in `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetLockedFrontier.lean`
retains three alternatives:

1. an actual lower ray whose **starting** endpoint is codimension two;
2. an actual lower ray starting rank three on `.qs` and ending rank three on
   `.pr`, `.sp`, or `.rq`, with the strict transverse direction lock;
3. a literal coordinate-zero quadratic square in the represented source.

Eliminating the other-facet branch does not by itself eliminate alternative 1.
A19.91 eliminates the **outside** codimension-two endpoint under a rank-three
starting hypothesis; it does not eliminate a codimension-two starting endpoint.
A19.86 turns the square into supported codimension-two data, but does not
construct an entire two-zero polynomial carrier.

The current finite-calculation owner is
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrLeadingSelfCoefficient.lean`.
R18.36--R18.37 are included in the root build and were checked by Lean CI #1538
at `2e4c8ef3f67fb764b239d073d2a638a14e3389a0`, including the axiom audit,
negative control, and proof-escape check.

Write `N = E.next.N`, `t = E.leading.transverseDegree`, `q = E.qN`, and
`S = E.leading.slice`. At exact contact parameter order `2q` and longitudinal
index `2N`, the proved identities are:

| Quantity | Exact coefficient |
| --- | --- |
| Straightened raw complementary determinant | `C(-N*t*(N+t-1)) * S * S` |
| `contactProfileParameterResidual` | `C(N*q*(q+N+2*t-1)) * S * S` |

The longitudinal convolution collapses to `(N,N)` by the support ceiling;
the parameter convolution then collapses to `(q,q)` by leading-order
minimality. Both collapses are proved, not assumed.

The residual coefficient is zero **if and only if `q = 0`**. This follows
from `N >= 2`, characteristic zero, and the retained nonzero slice. Thus
extremality does not permit discarding the parameter residual at positive
contact deficit.

The later affine-carrier and single-coefficient modules were checked by Lean
CI #1556 at `ef0e54a47f1d595bd759636fd8967ec7b3adc39c`. The first exposure
bounds the entire contact support by `d0 + d1 <= 1`. Consequently the leading
contact order is positive, and the displayed leading residual is **nonzero**
in the surviving PR branch. `PrAffineHessian.lean` also proves the zero `(0,1)`
Hessian block and zero mixed determinant on that same contact carrier. This
mixed determinant is distinct from the retained nonzero active principal minor.

`PrOneCoefficient.lean` shortens the conditional PR consumer: `hprodNN` alone
suffices. Its vanishing would force `D = N*r`, contradicting the leading grade
`D = qN + r*N + t` and `qN > 0`. The N--M product coefficient is therefore not
required for this conditional PR closure. The leading product-zero premise
has not been supplied.

The new `PrFirstVariation.lean` derives the first two necessary parameter-layer
equations from the actual contact determinant clock. For the raw permuted
contact Hessian block H it states

    H.x[1] * H.schurC[0] + H.z[1] * H.schurA[0]
      - 2 * H.y[1] * H.schurB[0] = 0.

Here brackets denote parameter coefficients. The affine carrier and its zero
mixed determinant eliminate the other first-order contributions. At order two,
write `L2` for the same left-hand expression with the complementary entries
at order two. The exact second equation is

    L2 = H.activeDet[0] * (H.x[1]*H.z[1] - H.y[1]^2)
       - (H.x[1]*H.schurC[1] + H.z[1]*H.schurA[1]
          - 2*H.y[1]*H.schurB[1])
       - (H.p*H.s - H.q*H.r)[1]^2.

The right side is retained, not asserted zero. Both equations are on the
actual contact family and require no new geometric hypothesis beyond the
surviving PR endpoint hypotheses. They do not yet yield terminal impossibility.
The indices are literally 1 and 2, not `qN` and `2*qN`. They can be
vacuous when the first actual layer occurs later. Applying analogous equations
at extremal contact orders still requires the appropriate lower-layer
convolution control; replacing these indices without that proof is invalid.
In particular R18.32 gives vanishing only at longitudinal index `N`, not
vanishing of every earlier source layer. Lower longitudinal indices may
contribute to the four-factor bordered correction. The extended exact Rees
support test in `PR34_REES_EXTREMAL_OBSTRUCTION.md` exhibits this distinction.
Lean CI #1564 passed at `c50b3c1f275ad97b31909a974b8b5b525712bb94`,
including the full build, axiom audit, negative control and proof-escape check.

The exact symbolic investigation in [PR34_REES_EXTREMAL_OBSTRUCTION.md](PR34_REES_EXTREMAL_OBSTRUCTION.md)
shows why the full clock must enter substantively: even an honest Rees family
with common-monomial contact coefficients and identically zero mixed coupling
can have a surviving bordered correction. In the documented example, clock
orders two and three give incompatible constraints on every possible later
Rees continuation. This restricted symbolic result is not a general Lean
terminal theorem.

**The geometric zero is still unproved.** In particular,
`contactLeadingRawComplementDetLayer_eq` is a coefficient identity; it does
not establish `t = 0`. The existing
`leading_transverseDegree_eq_zero_of_selfSlice` will establish that conclusion
only after its zero hypothesis has genuinely been supplied.

The exact remaining correction must be kept visible. Put `A = H.activeDet`,
`P = contactProfileHessianDetReduction`, `R = contactProfileParameterResidual`,
and let `B` be the sum of the three bordered Schur contributions and the mixed
coupling square. The already-proved whole-family identities give

```text
A * P = B - H.determinantCore - A * R.
```

At the appropriately transported binary layer the determinant clock kills
the full determinant contribution. Obtaining an active-pivot/profile product
zero still requires cancellation of the remaining `B - A * R` coefficient.
Neither full-determinant vanishing nor the identity for the leading residual
alone supplies this cancellation. Contact/binary coefficient transport must
retain its transverse-degree shift.

Consequently `hprodNN`, unconditional `.pr/.sp/.rq` impossibility,
and unconditional presented-terminal impossibility are not yet proved by this
calculation. A fixed remaining commit count is not justified while this
geometric gate remains open.

### 8b. Final import audit remains an explicit obligation

The A19.1 public statement has no JC2 hypothesis. Its current transitive
imports nevertheless include the older conditional owner
`HC4.Newton.TerminalTwoZeroJC2Endpoint`, for example along:

```text
AdaptiveAlignedSmithCanonicalHC4Reduction
  -> AdaptiveAlignedSmithCanonicalCollisionAutoDegree
  -> NonlinearDegreeBoundPreservation
  -> IntegralKernelBlowup
  -> PolynomialFamilyKernelRestart
  -> KernelBlowupCertificate
  -> HC4.Newton.RestartClassification
  -> HC4.Newton.TerminalTwoZeroJC2Endpoint
```

This is an import dependency, not evidence of an assumed JC2 axiom in A19.1.
It must still be separated if the final public owner is required to have no
transitive imports from the conditional JC2 route. Merely choosing a new
filename for the final theorem does not achieve that isolation.

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
- contact-zero affine realization as an honest `RankThreeAffineLineData`;
- affine RationalRigidity terminal certification for a rank-three `.qs` ray endpoint;
- forcing a singular boundary exponent to retain positivity in a prescribed coordinate;
- low-degree-tame versus literal quadratic-square exhaustiveness;
- unrestricted collision-to-terminal reduction under an unconditional terminal-impossibility theorem.

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

### A19.71 → A19.73

A19.71 assembles the exhaustive zero-clock boundary residual. A19.72 supplies the balance-free affine RationalRigidity terminal bridge for a contact-zero `.qs` ray. A19.73 specializes the `.qs` strict-low rank-three branch, removes complete nonlinear confinement, and retains only top/lower affine rays, codimension-two endpoints, or the literal quadratic-square branch.

**Rule:** when deciding what remains, start from A19.45/A19.53 and the newest zero-strict-low modules, not from the older resolver structures.

## 11. Current proof claim

The repository contains a very large, kernel-checked reduction and local-geometry development, but this status document should not claim unrestricted HC4 until a top-level theorem closes **every** live terminal branch and is included in the audited root build.

The global unrestricted front door itself is already available: once final assembly proves every `AdaptiveAlignedSmithCanonicalTerminalData` impossible without caller-supplied hypotheses, `gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible` yields determinant-one gradient injectivity for an arbitrary four-variable polynomial.

Therefore the remaining proof should be described precisely as **final unconditional terminal closure plus public theorem export**, not as a missing global reduction.

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
