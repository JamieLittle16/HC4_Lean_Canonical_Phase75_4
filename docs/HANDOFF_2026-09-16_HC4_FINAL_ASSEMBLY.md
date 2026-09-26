# HC4 unrestricted final-assembly handoff — 16 September 2026

> **Purpose.** This is the implementation-grade handoff for finishing the
> unrestricted HC4 proof on PR #34 in a fresh context window. It is deliberately
> written as a direct execution plan: what is already Lean-verified, what remains,
> which files/theorems to reuse, the exact order in which to implement the last
> adapters, and the acceptance criteria for finally claiming unrestricted HC4.
>
> This document supersedes the **status/TODO sections** of the 12 and 15 September
> handoffs. Those older documents remain valuable for detailed paper mathematics
> and provenance, especially the finite-staircase and `V=1` calculations.

---

## 0. Repository checkpoint — start here

Repository:

```text
JamieLittle16/HC4_Lean_Canonical_Phase75_4
```

PR / branch:

```text
#34 — A18.4.42 collapse final termination frontier
final-assembly/a18-4-42-termination-frontier
```

Green proof checkpoint audited for this handoff:

```text
fb896bb7766d5586af89377fa1efb1641f9c3859
```

At this checkpoint the root target is green as reported in the proof session,
and `HC4.lean` explicitly imports the newest central and nontrivial `.pr`
assembly stack. Therefore every theorem described below as **LEAN VERIFIED** is
rooted through the live final-assembly import graph, not merely present in an
orphan source file.

The documentation commit containing this handoff will move the branch head.
On resume, re-fetch PR #34 and compare against the checkpoint above before
editing.

### Exact root tail at the checkpoint

`HC4.lean` deliberately roots:

```lean
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofAffineTerminalRealisation

import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo

import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly
```

The last import transitively checks the new right-side source/hull groundwork as
well.

---

# 1. Executive status

The shortest accurate picture is now:

```text
unrestricted HC4 entry / normalization / collision reduction       LEAN VERIFIED
rank-one termination trace and public resolver reduction           LEAN VERIFIED
A19 same-carrier codimension-two -> real rank-two geometry          LEAN VERIFIED
lower .qs boundary -> actual other-facet endpoint                  LEAN VERIFIED
source-honest planar carrier + highest singular pair slice          LEAN VERIFIED
primitive highest-slice classification                             LEAN VERIFIED
normalized .pr frontier: unit / left V>1 / right V>1               LEAN VERIFIED

left (1,V), V>1 finite-staircase hull                               LEAN VERIFIED
left exposed cross-roof branch -> False                            LEAN VERIFIED
left central branch -> exact monomial initial                       LEAN VERIFIED
left central initial -> actual presented rank-two chart             LEAN VERIFIED
left non-unit branch consumed in parent assembly                    LEAN VERIFIED

right (V,1), V>1 source deficits / lower hull                       LEAN VERIFIED
right exposed cross-roof source package                             LEAN VERIFIED
right central exact rank-two initial                                LEAN VERIFIED
state-free mirror terminal algebra                                  LEAN VERIFIED
right affine-line realization + terminal certificates               OPEN
right central minor -> actual presented rank-two chart              OPEN
right branch parent closure                                         OPEN

nontrivial .pr after non-unit closure                               OPEN after right splice
unit V=1 source-facing closure                                      OPEN
highest-slice singleton/trivial case audit                          OPEN
.pr local parent closure                                            OPEN
.sp/.rq cyclic/permutation wrappers                                 OPEN
other-facet -> terminal resolver splice                             OPEN
public unrestricted HC4 theorem                                     OPEN
final axiom/negative-control/escape-hatch certification             OPEN
```

The important strategic point is:

> **Do not reopen the left finite-staircase mathematics.**
>
> The difficult multi-fibre exposed-roof problem from the 15 September handoff
> has been solved in Lean. The left `V>1` branch is already consumed into an
> actual Hessian rank-two chart. The right branch is now the same construction
> with source coordinates `2` and `3` exchanged; most of its source-honest hull
> infrastructure is already compiled.

After the right mirror is completed, the only likely substantive local
mathematics left is the source-facing `V=1` endpoint coefficient extraction.
Everything above and below that seam is mature infrastructure.

---

# 2. Status vocabulary — use literally

Use only:

- **LEAN VERIFIED** — rooted and known to compile at the stated checkpoint;
- **SOURCE-LANDED / NOT LEAN VERIFIED** — committed but not yet accepted by the
  relevant root build;
- **PAPER CANDIDATE** — paper argument exists but the corresponding Lean bridge
  is not compiled;
- **DIAGNOSTIC ONLY** — symbolic/computational evidence, not a proof theorem;
- **OPEN** — a genuine implementation or mathematical seam remains.

Do not say unrestricted HC4 is proved until the final public determinant-one
injectivity theorem compiles **without** a caller-supplied terminal resolver,
JC2 hypothesis, balance assumption, global homogeneity assumption, or
repair-only contradiction.

---

# 3. Non-negotiable architectural rules

Carry these through the final sprint.

1. **Do not identify auxiliary Rees clocks with the zero blocker.** Contact,
   pair-degree, stationary, ordinary reverse-Rees and determinant clocks remain
   distinct unless an explicit theorem identifies them.

2. **Do not use naked `withRepairOnly` as a contradiction.** Rank promotion is
   usable only after actual Hessian/Schur geometry has been produced.

3. **Do not infer singularity of a chosen subpolynomial from singularity of a
   larger carrier.** Every singular face in the final proof must be an honest
   initial form, Rees layer, or otherwise have its own determinant theorem.

4. **Do not collapse the A19 strict-low branch to generic JC2.** The actual
   source/contact/ray provenance is stronger and the codimension-two branch is
   already closed through genuine rank-two geometry.

5. **Do not add another global/rank-one recursion.** The existing finite
   rank-one termination trace is the public reduction mechanism.

6. **Do not revive the false stationary determinant implication or the false
   first-variation degree shortcut.** Both were explicitly killed by
   counterexamples and superseded by the finite-staircase route.

7. **Do not use the four-monomial cross-ratio equation as a contradiction by
   itself.**

8. **Do not conflate different codimension-two constructors.** The A19.55
   same-carrier branch and the later lower-`.qs` boundary endpoint have separate
   existing consumers.

9. **Search before adding infrastructure.** The repository already contains
   canonical owners for affine line realization, terminal certificates,
   coordinate permutations, weighted-initial Hessian minors, primitive endpoint
   moments, rank-two charts, rank-two-to-rank-three geometry, and the public
   terminal-resolver reduction.

10. **Root new final-seam files immediately.** The recent central helper bug was
    discovered only when the source was imported through `HC4.lean`. A local or
    orphan-file compile is not the final acceptance test.

---

# 4. Public end-to-end architecture

The verified public reduction is already:

```text
arbitrary F with det Hess F = 1
        + distinct gradient collision
        |
        v
canonical collision normalization
        |
        v
positive Rees presentation
        |
        v
existing finite rank-one termination trace
        |
        v
normalized presented rank-three terminal
        |
        v
[ONLY REMAINING RESOLVER]
presentedTerminal_impossible
        |
        v
contradiction
        |
        v
gradient injective
```

The exact verified theorem is in
`AdaptiveAlignedSmithCanonicalHC4Reduction.lean`:

```lean
theorem gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          canonicalAdaptiveAlignedSmithRepairRanking state 0 → False) :
    Function.Injective (mvGradientMap F)
```

So the final sprint should **finish the terminal resolver and feed it into this
existing theorem**. Do not redesign the public reduction unless the live import
graph forces it.

---

# 5. What the left `V>1` work now gives us — LEAN VERIFIED

The left normalized direction is

```text
(1,-1,-1,-V),   V > 1.
```

The old 15 September handoff stopped at a multi-fibre exposed-roof problem.
That problem is now formally solved.

## 5.1 Honest left source split

For

```lean
F : QsOtherFacetPrLeftVContactFrontierData C P S R
```

we now have

```lean
F.central_or_exposedCrossRoof hthree houtThree
```

with two outcomes:

```text
central source point e1=e2=0
OR
honest exposed singular cross-roof face.
```

## 5.2 Exposed cross-roof is impossible

The actual singular face is realized in both orientations as a
`RankThreeAffineSupportData` / `RankThreeAffineLineData`.

Canonical terminal theorem:

```lean
E.impossible hthree houtThree : False
```

Owner:

```text
...PrVGreaterOneFiniteStaircaseCrossRoofAffineTerminalRealisation.lean
```

It preserves literal endpoint coefficients, transports Hessian singularity
under the required coordinate permutations, obtains both terminal certificates,
forces both cross-roof residuals to one, and invokes the already-verified
staircase contradiction.

Important permutation detail — do not regress it:

```lean
highPerm = swap 0 1
lowPerm  = highPerm.trans (swap 0 2)
```

The reverse permutation is **not** a bare `swap 0 2`.

## 5.3 Central point produces honest rank-two geometry

The central monomial is the unique coordinate-`0` maximum. Its exact initial
face is literally

```lean
monomial c (coeff c P.carrier)
```

and has nonzero principal Hessian minor `(0,3)`.

Canonical package:

```lean
QsOtherFacetPrLeftVCentralRankTwoGeometry F
```

Canonical producer:

```lean
F.centralRankTwoGeometry hthree houtThree
```

Owner:

```text
...FiniteStaircaseCentralClosure.lean
```

## 5.4 The central minor has been lifted to the real represented state

`...FiniteStaircaseCentralActualRankTwo.lean` proves:

```lean
G.carrier_hessianPrincipalMinor_ne_zero
G.presented_specialFiber_hessianPrincipalMinor_ne_zero
G.actualRankTwoHessianChart
G.actualRankThreeGeometry
```

The nonzero minor is transported twice by the generic maximal-initial theorem:

```text
central monomial face
  -> P.carrier
  -> polynomialFamilySpecialFiber T.terminal.blocker.presented.family.
```

The generic chart identity is now also available:

```lean
scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor
```

Thus the branch produces an actual

```lean
AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
  T.terminal.blocker.presented
```

before any repair/progress label is attached.

---

# 6. Current parent frontier — LEAN VERIFIED

The key new parent theorem is:

```lean
QsOtherFacetPlanarHighestPairSlicePackage.pr_nontrivial_after_left_closure
```

in

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly.lean
```

For a nontrivial `.pr` highest slice, it returns the **same honest contact-Rees
package** `R` and exactly:

```lean
Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1)
OR
Nonempty (QsOtherFacetPrRightVContactFrontierData C P S R)
OR
Nonempty (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
  T.terminal.blocker.presented)
```

Interpretation:

```text
unit (1,1)
OR right non-unit (V,1), V>1
OR left branch has already become actual rank-two geometry.
```

This is the correct starting interface for the next session.

---

# 7. Right `(V,1)`, `V>1`: most of the mirror is already formal

The right normalized direction is

```text
(1,-1,-V,-1),   V > 1.
```

Do **not** start by implementing a general coordinate-permutation framework.
The source-honest right hull has already been built directly and compiled.

The following are **LEAN VERIFIED** and transitively rooted by the parent
assembly:

```text
...FiniteStaircaseRightSourceDeficits.lean
...FiniteStaircaseRightLowerHull.lean
...FiniteStaircaseRightCrossRoofExposure.lean
...FiniteStaircaseRightCrossRoofSourceData.lean
...FiniteStaircaseRightCentralRankTwo.lean
```

## 7.1 Right source split already exists

Canonical theorem:

```lean
F.central_or_exposedCrossRoof hthree houtThree
```

for

```lean
F : QsOtherFacetPrRightVContactFrontierData C P S R
```

returns

```lean
(∃ e ∈ P.carrier.support, e 1 = 0 ∧ e 3 = 0)
OR
Nonempty (QsOtherFacetPrRightVExposedCrossRoofData F).
```

## 7.2 Right central geometry already exists

Canonical theorem:

```lean
F.central_coordinateMax_face_rankTwo
```

for a central point `c` with

```text
c1 = 0,
c3 = 0
```

returns an honest coordinate-`0` max initial monomial with

```lean
hessianDeterminant D.face = 0
hessianPrincipalMinor D.face 0 2 != 0.
```

This is the exact mirror of the compiled left `(0,3)` theorem.

## 7.3 Right exposed package already has all staircase arithmetic

`QsOtherFacetPrRightVExposedCrossRoofData F` stores:

```text
kLo, jLo, kHi, jHi, q, v
kLo < kHi
q > 0
v > 0
q = jLo + 1 - kLo
v = kHi - jHi - 1
wall_lo
wall_hi
```

Literal source endpoints are

```text
low  = (kLo, 0, V*jLo, q)
high = (jHi+1, v, V*(kHi-1), 0).
```

Therefore the remaining right branch is **not a new Newton problem**. It is
only the affine-line/certificate layer that has already been implemented on the
left.

## 7.4 State-free mirror terminal algebra already exists

Owner:

```text
HC4/RationalRigidity/FiniteStaircaseCrossRoofMirrorTerminal.lean
```

Canonical theorem:

```lean
finiteStaircase_crossRoof_lowResidual_eq_one
```

The ordinary forward cross-roof terminal theorem forces

```text
v = 1
```

and the mirror theorem forces

```text
q = 1.
```

The final arithmetic contradiction is already the same verified
`crossRoof_residual_sum` plus
`staircase_heightDrop_gt_pairGain` argument used on the left.

---

# 8. FIRST TASK NEXT CHAT: finish the right branch in six thin commits

This should be done before touching `V=1` or the global assembly.

The fastest route is to copy the **structure**, not the mathematics, of the
left files and replace the source transverse coordinate `2` by `3` where
appropriate.

## R1 — right affine coordinates

Create:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofAffineCoordinates.lean
```

Mirror the left owner:

```text
...FiniteStaircaseCrossRoofAffineCoordinates.lean
```

Prove only:

```lean
QsOtherFacetPrRightVExposedCrossRoofData.face_eq_of_one_eq
QsOtherFacetPrRightVExposedCrossRoofData.face_eq_of_three_eq
QsOtherFacetPrRightVExposedCrossRoofData.face_one_le_v
QsOtherFacetPrRightVExposedCrossRoofData.face_three_le_q
```

Use the existing right hull cost equation and

```lean
F.support_eq_of_deficits_eq
```

from `RightSourceDeficits`. No new injectivity lemma is needed.

### Acceptance

Root or import from R2 immediately. Do not leave this file orphaned.

## R2 — right affine interpolation

Create:

```text
...FiniteStaircaseRightCrossRoofAffineInterpolation.lean
```

Mirror left interpolation.

For every `e` on the right exposed face, prove the exact transverse relation

```text
v * e3 + q * e1 = q * v.
```

Then derive:

```text
coordinate 0 interpolation using e1 as parameter;
coordinate 2 interpolation from the right staircase curve.
```

The right source curve is the left formula with old coordinates `2` and `3`
interchanged. The low/high literal values are already fields of `E`.

Do not derive a new staircase equation; call the existing right
`support_staircase_equations` / source-deficit lemmas.

## R3 — right affine support realization

Create:

```text
...FiniteStaircaseRightCrossRoofAffineRealisation.lean
```

Use the existing generic

```lean
HC4.Polynomial.RankThreeAffineSupportData
```

and the exact same profile-degree helper pattern as the left implementation.

You need two orientations of the **same exact singular face**.

### Forward/high orientation

Parameter: old coordinate `1`.

Retained rank-three base coordinates must be ordered so the base is

```text
(kLo, q, V*jLo)
```

and the coefficient-profile degree is

```text
v.
```

Because in the right source the low residual `q` sits in old coordinate `3`,
choose the permutation so the new retained coordinates are schematically

```text
(old0, old3, old2)
```

after moving old `1` to new coordinate `0`.

### Reverse/low orientation

Parameter: old coordinate `3`.

The retained base should be

```text
(jHi+1, v, V*(kHi-1))
```

and the profile degree should be

```text
q.
```

Choose explicit `Equiv.Perm (Fin 4)` compositions and prove each value and
inverse value with `by decide`. This is much less fragile than relying on
unfolding/simp to discover the permutation.

### Required outputs

```lean
highSupportData
lowSupportData
highProfile_natDegree : ... = E.v
lowProfile_natDegree  : ... = E.q
```

Reuse the left private helper idea:

```lean
coefficientProfile_natDegree_eq_of_bound_endpoint
```

Copy it locally if necessary; do not generalize the whole architecture just to
share five lines.

## R4 — right terminal certificates and exposed contradiction

Create:

```text
...FiniteStaircaseRightCrossRoofAffineTerminalRealisation.lean
```

Mirror the thin left terminal file.

Prove:

```lean
highProfile_coeff_zero_ne
lowProfile_coeff_zero_ne
highAffineLine_hessian_zero
lowAffineLine_hessian_zero
highTerminalCertificate
lowTerminalCertificate
```

For Hessian singularity, use:

```lean
HC4.Newton.hessianDeterminant_rename_perm
```

on the exact source face. Do not infer singularity from a chosen line.

Then either add a tiny right terminal-composition theorem or directly prove:

```lean
E.impossible hthree houtThree : False
```

using:

```lean
finiteStaircase_crossRoof_highResidual_eq_one   -- v = 1
finiteStaircase_crossRoof_lowResidual_eq_one    -- q = 1
crossRoof_residual_sum
staircase_heightDrop_gt_pairGain
```

The final contradiction should be `omega`-level arithmetic after the two unit
residuals.

## R5 — lift the right central minor to the actual chart

Create:

```text
...FiniteStaircaseRightCentralActualRankTwo.lean
```

Mirror left `CentralActualRankTwo.lean` exactly.

Starting from the already-verified central `(0,2)` minor:

```text
right central monomial face
 -> P.carrier
 -> polynomialFamilySpecialFiber T.terminal.blocker.presented.family
```

using twice:

```lean
hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
```

Then use the already-verified generic chart constant-coefficient theorem:

```lean
scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor
```

Choose a chart permutation with

```text
rho 0 = 0
rho 1 = 2
```

for example `Equiv.swap 1 2` if it gives exactly those values; verify with
`by decide` before writing the final `simpa`.

Define:

```lean
actualRankTwoHessianChart
```

and, if useful for a downstream consumer,

```lean
actualRankThreeGeometry
```

via the existing

```lean
rankThreeGeometry 0.
```

## R6 — collapse the whole right branch

Add a small parent-facing closure file, e.g.

```text
...FiniteStaircaseRightClosure.lean
```

The theorem should have the simple interface:

```lean
theorem QsOtherFacetPrRightVContactFrontierData.actualRankTwoHessianChart
    (F : ...)
    (hthree : ...)
    (houtThree : ...) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented)
```

Proof:

```text
central_or_exposedCrossRoof
  central -> R5 actual chart
  exposed -> R4 False.elim
```

Then update/add a parent theorem so the nontrivial `.pr` frontier becomes

```text
unit (1,1)
OR
actual presented rank-two chart.
```

Suggested name:

```lean
pr_nontrivial_after_nonunit_closure
```

### Gate

Import the top right closure / updated nontrivial assembly in `HC4.lean` and
require a clean root build before moving to `V=1`.

---

# 9. SECOND TASK: audit the trivial/singleton highest-slice case

The current parent theorem assumes

```lean
hnontrivial :
  ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b.
```

Do **not** silently assume every highest slice is nontrivial.

The highest-slice constructor itself proves only:

```text
slice != 0;
pairLevel > 1;
hessianDeterminant slice = 0.
```

Before building the final `.pr` wrapper, search for an existing theorem that
already excludes or consumes a singleton highest slice.

Search first in/around:

```text
AdaptiveAlignedSmithSingletonRankThreeImpossible.lean
AdaptiveAlignedSmithSingularSingletonContradiction.lean
AdaptiveAlignedSmithSingletonRankThreeTerminal.lean
RankThreeVerticalContradiction.lean
PlanarPrimitiveSlice.lean
MonomialHessian.lean
```

### If a consumer exists

Add only the thin adapter from `S.slice` and its source provenance to that
consumer.

### If no consumer exists

Prove the weakest correct branch theorem, not an overgeneralized monomial
claim.

A likely split is:

```text
singleton highest monomial has all four positive exponents
  -> hessianDeterminant_monomial_ne_zero contradiction;

or one coordinate vanishes
  -> route to the existing rank-three vertical/singleton terminal machinery.
```

Do not assume positivity without deriving it from the actual source/facet
relations.

Desired parent result:

```text
trivial highest slice -> False
```

or, if the existing architecture naturally produces geometry,

```text
trivial highest slice -> actual rank-two/rank-three geometry.
```

Keep whichever conclusion matches the mature consumer.

---

# 10. THIRD TASK: close the unit `V=1` branch

After both non-unit orientations are consumed, the nontrivial `.pr` branch is
reduced to

```lean
Q : QsOtherFacetPrQuotientCarrierData C P 1 1.
```

This is the most likely final genuinely mathematical source-facing seam.

The paper mathematics is already recorded in

```text
docs/HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md
```

and should be treated as the reference, not re-derived from scratch.

## 10.1 Existing verified ingredients

The highest slice is already primitive:

```lean
S.primitive_of_nontrivial ...
```

and `.pr` has a source-honest endpoint orientation theorem:

```lean
A.pr_primitive_endpoint_orientation hthree houtThree D
```

with direct entry:

```lean
S.exists_pr_primitive_orientation
```

The locked ray has exact source coefficients/provenance through:

```lean
S.pr_locked_source_data_of_nontrivial
```

The contact-Rees package `R` is already produced by the parent assembly.

The state-free mixed endpoint contradiction is **LEAN VERIFIED**:

```lean
HC4.Polynomial.mixedOrientation_endpoint_coefficients_impossible
```

It consumes nonzero endpoint coefficients and

```text
2*A*D = B*C
A*D   = 2*B*C.
```

## 10.2 First search before coding

Search the existing A19 contact/moment files for the two required extremal
coefficient identities. There is a large mature stack around:

```text
PrCarrierReconstruction
PrLockedSourceCoefficients
PrPrimitiveEndpointOrientation
PrimitiveBinomialHessianEndpoint
PrimitiveBinomialAffineMoment
RankThreeEndpointActiveMinor
PrLeadingSelfCoefficient
PrOneCoefficient
PrFirstVariation
```

Do not recompute a four-variable determinant if the coefficient extraction is
already present under a different theorem name.

## 10.3 Unit branch case split

The paper closure separates:

```text
same orientation
mixed orientation.
```

### Mixed orientation

This should be the clean branch.

1. Bind the four literal nonzero endpoint coefficients from the locked and
   primitive-highest source packages.
2. Extract the two extremal determinant equations from the actual singular
   carrier / exact layer.
3. Normalize them to

   ```text
   2*A*D = B*C
   A*D   = 2*B*C.
   ```

4. Apply

   ```lean
   mixedOrientation_endpoint_coefficients_impossible
   ```

No JC2 theorem is involved.

### Same orientation

The paper argument says this is killed by the full two-function determinant
factorization.

Existing verified end theorem:

```lean
HC4.Polynomial.twoFunctionCarrier_hessian_impossible
```

but its current public hypotheses include

```text
1 < V.
```

For `V=1`, do **not** blindly call it or weaken hypotheses without checking the
factorization theorem it uses.

Preferred options, in order:

1. **Best:** find an existing underlying factorization theorem that only needs
   `0 < V`, and add a tiny `V=1` endpoint theorem using it.
2. If the current proof of `twoFunctionCarrier_hessian_impossible` genuinely
   only uses positivity except for a factorization theorem stated with `1<V`,
   generalize the state-free theorem carefully and re-run its existing callers.
3. If generalization causes churn, add a dedicated state-free
   `twoFunctionCarrier_V_one_hessian_impossible` specialization using the same
   factors/coefficient extraction.

Do not create another source-carrier classification.

## 10.4 Desired unit interface

Keep the parent theorem small:

```lean
theorem QsOtherFacetPrUnitQuotientCarrierData.impossible ... : False
```

or an equivalent theorem directly on `Q : QsOtherFacetPrQuotientCarrierData C P 1 1`.

Once compiled, the nontrivial `.pr` branch contains **only actual rank-two
geometry**.

---

# 11. FOURTH TASK: close `.pr`

After:

```text
right V>1 consumed;
unit V=1 impossible;
singleton highest slice consumed;
```

the `.pr` other-facet branch should expose no unresolved algebraic case.

Build one parent theorem at the highest source-honest level already used by the
A19 boundary machinery.

A good output type is likely geometry-bearing, not necessarily `False`, because
left/right central branches intentionally produce actual rank-two charts.

For example, for the nontrivial route:

```lean
Nonempty
  (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
    T.terminal.blocker.presented)
```

The final terminal/A19 consumer should then use the repository's existing
rank-two geometry/progress machinery rather than pretending the chart itself is
contradictory.

Search before wiring:

```text
AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree.lean
AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry.lean
AdaptiveAlignedSmithCanonicalZeroStrictLowDirectRankTwoProgress.lean
AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoFinalGeometry.lean
```

The A19 same-carrier codimension-two branch already solved this exact
architectural problem: geometry first, then a certified successor. Reuse that
pattern.

---

# 12. FIFTH TASK: `.sp` / `.rq` by cyclic relabelling

The verified lower-`.qs` reduction already ends in

```lean
∃ next : ToricFacet,
  next ≠ .qs ∧
  MvRankThreeOnFacet next C.ray.outsideExponent.
```

Thus `next` is `.pr`, `.sp`, or `.rq`.

Do not clone the `.pr` staircase proof for the other two facets.

Existing infrastructure to search/use:

```text
HC4/Newton/TerminalCoordinatePermutation.lean
HC4/Valuation/PermutedPolynomialHessianFourBlock.lean
HC4/Valuation/PermutedFamilyHessianFourBlock.lean
cyclic other-facet direction-lock lemmas
```

Recommended implementation:

1. `fin_cases next` after excluding `.qs`.
2. `.pr`: call the new `.pr` closure directly.
3. `.sp` / `.rq`: explicitly rename coordinates into the `.pr` configuration.
4. Transport only the source-honest packages actually needed by the `.pr`
   theorem.
5. Use Hessian covariance under permutation; do not reprove determinant
   identities.

If transporting the deeply dependent `P/S/R` package is awkward, write a thin
facet-generic wrapper around the `.pr` theorem rather than duplicating its
proof body.

---

# 13. SIXTH TASK: splice into A19 / terminal resolver

Important verified upstream theorem:

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.
  qs_ray_boundaryOutcome_otherFacet
```

It compresses the lower ray to an actual rank-three different-facet endpoint.

The next verified layer

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.
  qs_rankThree_startCodimensionTwo_or_otherFacet_or_quadraticSquare
```

retains exactly:

```text
start codimension two
OR actual other-facet rank-three endpoint
OR literal coordinate-zero quadratic square.
```

Do not erase the sibling constructors. Each has existing dedicated machinery.

After the new all-other-facet theorem exists, use reverse-import search / the
module index to locate the narrowest theorem still expecting that constructor.
The expected route is approximately:

```text
...FirstNonfacetOtherFacetReduction
...QsReducedLowerFrontier
...CrossFacetBoundaryTransition
...RankThreeBoundaryReduction
...TerminalResidualReduction
...RankOneReesZeroStrictLowTerminal
...HC4ReachableTerminalReduction
...ReachableHC4Reduction
...HC4Reduction
```

But do not mechanically edit each file. Add the new theorem as high as possible
and let the typechecker show the next unmatched constructor.

### Architecture warning

`AdaptiveAlignedSmithCanonicalGlobalMacroTermination.lean` contains a genuine
well-founded global macro relation, and
`ZeroStrictLowDirectRankTwoProgress.lean` contains geometry-backed progress.
Those are useful existing consumers, but the current public HC4 theorem still
reduces to **presented-terminal impossibility**. Do not start a second recursion
just because a global-progress theorem exists.

The desired final local theorem is conceptually:

```lean
theorem presentedTerminal_impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0) :
    False
```

The exact namespace/name may differ; choose a name consistent with the current
terminal files.

---

# 14. SEVENTH TASK: public unrestricted HC4 theorem

Once `presentedTerminal_impossible` is green, the public proof should be almost
boilerplate.

Semantic target:

```lean
theorem gradient_injective_of_hessianDeterminant_one
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
      F hdet (by
        intro state T
        exact presentedTerminal_impossible T)
```

Use the repository's preferred final theorem name if a public namespace already
owns the determinant-one statement.

Also add the equivalent no-distinct-collision theorem only if it is already part
of the public API pattern; do not delay the main theorem for cosmetic wrappers.

---

# 15. Certification gate — only after the theorem compiles

Before saying “unrestricted HC4 is Lean proved”, require all of:

```text
1. HC4.lean full root build green.
2. Final public theorem imported by the root.
3. #print axioms / workflow axiom audit clean.
4. Negative control rejected.
5. Escape-hatch audit clean:
   no sorry
   no admit
   no native_decide proof escape
   no unsafe proof bridge.
6. Public theorem has no:
   terminal resolver argument
   JC2 hypothesis
   balance assumption
   source homogeneity assumption
   repair-only contradiction.
```

The existing CI workflow already has dedicated steps for theorem axioms,
negative control, and proof escape hatches. Let them run on the final rooted
head.

---

# 16. Detailed current theorem/file inventory — do not duplicate

## Left finite staircase

```text
...FiniteStaircaseSourceDeficits.lean
...FiniteStaircaseLowerHull.lean
...FiniteStaircaseLowerHullExposure.lean
...FiniteStaircaseCrossRoofExposure.lean
...FiniteStaircaseCrossRoofSourceData.lean
...FiniteStaircaseCrossRoofAffineCoordinates.lean
...FiniteStaircaseCrossRoofAffineInterpolation.lean
...FiniteStaircaseCrossRoofAffineRealisation.lean
...FiniteStaircaseCrossRoofTerminalClosure.lean
...FiniteStaircaseCrossRoofAffineTerminalRealisation.lean
...FiniteStaircaseCentralRankTwo.lean
...FiniteStaircaseCentralClosure.lean
...FiniteStaircaseCentralActualRankTwo.lean
```

All **LEAN VERIFIED** at the checkpoint.

## Right finite staircase already present

```text
...FiniteStaircaseRightSourceDeficits.lean
...FiniteStaircaseRightLowerHull.lean
...FiniteStaircaseRightCrossRoofExposure.lean
...FiniteStaircaseRightCrossRoofSourceData.lean
...FiniteStaircaseRightCentralRankTwo.lean
```

All **LEAN VERIFIED** at the checkpoint.

Missing right files should mirror only the thin affine/certificate/chart layers
listed in Section 8.

## State-free cross-roof terminal algebra

```text
HC4/RationalRigidity/FiniteStaircaseCrossRoofTerminal.lean
HC4/RationalRigidity/FiniteStaircaseCrossRoofMirrorTerminal.lean
HC4/Polynomial/FiniteStaircaseCrossRoofArithmetic.lean
HC4/Polynomial/FiniteStaircaseCrossRoofMirrorArithmetic.lean
```

Already **LEAN VERIFIED**. Never reprove these inside A19 state packages.

## Monomial / weighted-initial Hessian bridge

```text
HC4/Polynomial/MonomialHessian.lean
HC4/Polynomial/MonomialHessianPrincipalMinor.lean
HC4/Valuation/WeightedHessianPrincipalMinorInitial.lean
HC4/Polynomial/UniqueMaximalInitialMonomial.lean
```

The principal-minor formula correctly assumes distinct coordinates.

## Actual rank-two chart / rank-three bridge

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalScaleAwareHessianRankSplit.lean
HC4/Valuation/AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree.lean
```

Use the exact existing chart type; do not introduce a second rank-two geometry
record for the represented state.

## `.pr` primitive/source package stack

```text
...PrNormalizedCarrier.lean
...PrPrimitiveEndpointOrientation.lean
...PrLockedSourceCoefficients.lean
...PrCarrierReconstruction.lean
...PrVGreaterOneContactFrontier.lean
...PrNontrivialAssembly.lean
```

This should be the substrate for `V=1`; do not reconstruct endpoint
coefficients from scratch.

## State-free `V=1` endpoint contradiction

```text
HC4/Polynomial/TwoFunctionMixedOrientationRigidity.lean
```

Canonical scalar end theorem:

```lean
mixedOrientation_endpoint_coefficients_impossible
```

## Non-unit concrete two-function contradiction

```text
HC4/Polynomial/TwoFunctionCarrierHessianRigidity.lean
HC4/Valuation/...PrTwoFunctionCarrier.lean
```

Current state-free public theorem assumes `1 < V`; check the underlying
factorization before adapting it to `V=1`.

---

# 17. Paper mathematics references

Use these instead of reconstructing old arguments from memory.

## Finite staircase / multi-fibre history

```text
docs/HANDOFF_2026-09-15_HC4_FINAL_MULTIFIBER_CLOSURE.md
```

Sections 4–12 contain the staircase coordinates, roof residuals, extremal
ordering, cross-roof arithmetic, and terminal exceptional-factor analysis.
Most of its formerly-open left tasks are now **superseded by compiled Lean**.

## `V=1` and overall rank-three paper closure

```text
docs/HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md
```

The key `V=1` facts are:

```text
same orientation:
  killed by the full two-function Hessian determinant factorization;

mixed orientations:
  extremal coefficients give
      2*A*D = B*C
      A*D   = 2*B*C,
  with nonzero endpoint products,
  contradiction in characteristic zero.
```

The state-free mixed scalar contradiction is already formal.

## Historical routes not to revive

```text
docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md
docs/STATIONARY_DETERMINANT_COMPARISON_AUDIT_2026-09-15.md
docs/HISTORICAL_AND_SUPERSEDED_ROUTES.md
```

---

# 18. Fresh-context command sequence

In the next chat, do this immediately.

```text
A. Re-audit PR #34 head and HC4.lean.
B. Confirm the current root is still green.
C. Open side-by-side:
   left CrossRoofAffineCoordinates
   right CrossRoofSourceData
   left CrossRoofAffineInterpolation
   left CrossRoofAffineRealisation
   left CrossRoofAffineTerminalRealisation
   right CentralRankTwo
   left CentralActualRankTwo
D. Implement R1-R6 with no redesign.
E. Root the top right closure and compile.
F. Compress PrNontrivialAssembly to unit | actual-rank-two-chart.
G. Search/close singleton highest-slice branch.
H. Implement V=1 same/mixed source-facing closure.
I. Build .pr parent closure.
J. Add .sp/.rq permutation wrappers.
K. Splice to presentedTerminal_impossible.
L. Add public unrestricted theorem.
M. Run full certification.
```

When a compiler failure appears, fix it **in place** and continue. Do not pause
to rewrite documentation until the final theorem is green.

---

# 19. What would count as a genuine surprise now?

The proof is close, but there are still two places where a new mathematical
issue could honestly appear:

1. **`V=1` source-facing coefficient extraction.** The scalar contradiction is
   proved, but the exact two equations still need to be extracted from the live
   carrier unless they are already hidden in existing moment/contact files.

2. **Singleton highest slice.** It must be explicitly consumed rather than
   silently assuming nontriviality.

The right `V>1` branch is not expected to contain new mathematics: all source
hull geometry and state-free terminal algebra already exist. `.sp/.rq` should
be coordinate transport, and the final public theorem is already reduced to a
terminal resolver.

So if the right mirror compiles cleanly and the two unit/singleton seams use the
existing infrastructure as expected, the remaining work really is final
assembly rather than another research programme.

---

# 20. Final target

The project is finished only when the repository contains a rooted, audited
hypothesis-free theorem semantically equivalent to:

```lean
∀ (F : MvPolynomial (Fin 4) K),
  HC4.Polynomial.hessianDeterminant F = 1 →
  Function.Injective (mvGradientMap F)
```

for characteristic-zero algebraically closed `K`, with no external HC4/JC2
resolver or local terminal assumption.

Until that exact endpoint compiles and passes the certification workflow, keep
the status as **final assembly in progress**, not “HC4 proved”.
