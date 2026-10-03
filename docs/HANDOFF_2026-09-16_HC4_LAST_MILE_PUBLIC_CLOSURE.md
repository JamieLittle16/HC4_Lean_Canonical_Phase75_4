# HC4 last-mile public closure handoff — 16 September 2026

> **Purpose.** This is the implementation-grade handoff for the final unrestricted
> HC4 sprint on PR #34. It starts from the exact green checkpoint reached after
> the unit-staircase and unit endpoint-only work on 16 September and is intended
> to let a fresh chat finish the proof without reconstructing the preceding
> finite-staircase, unit, codimension-two, or global-termination developments.
>
> This document supersedes the **status and TODO sections** of the 12, 15, and
> earlier 16 September handoffs. Those documents remain authoritative for paper
> calculations, counterexamples, and provenance, especially where explicitly
> referenced below.

---

# 0. Exact checkpoint — start here

Repository:

```text
JamieLittle16/HC4_Lean_Canonical_Phase75_4
```

PR / branch:

```text
#34 — A18.4.42 collapse final termination frontier
final-assembly/a18-4-42-termination-frontier
```

Exact certified code checkpoint for this handoff:

```text
cf53735baedb4555df9d8a1c6c63cef7cc17fdec
```

Commit message:

```text
Normalize unit endpoint coordinate projections
```

Lean CI for that exact SHA:

```text
run 35139954849
job 104941701425 — Build and verify Lean project
```

All relevant gates passed:

```text
Build HC4                         SUCCESS
Audit theorem axioms             SUCCESS
Negative control rejected        SUCCESS
Reject proof escape hatches      SUCCESS
```

The documentation commit containing this file will move the branch head. In a
fresh chat **re-fetch PR #34 first** and compare its head against the checkpoint
above before editing. If the head has advanced, inspect the intervening commits
instead of assuming this document is literally current.

## Important root/import nuance

The exact full-project build at `cf537...` compiles the new unit modules, so the
unit declarations listed below are genuinely Lean-checked at this checkpoint.
However `HC4.lean` still ends its explicit final-assembly tail at

```lean
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly
```

and does **not yet explicitly root the top unit closure or the eventual all-PR
closure**. Therefore distinguish:

```text
module theorem compiled in the certified full build     LEAN VERIFIED
final parent/root/public splice                          still OPEN
```

Do not confuse an unperformed parent splice with missing local mathematics.

---

# 1. Executive status

The shortest accurate state is now:

```text
unrestricted determinant-one entry / collision normalization       LEAN VERIFIED
finite rank-one termination trace                                  LEAN VERIFIED
public reduction to presented-terminal impossibility               LEAN VERIFIED

A19 same-carrier codimension-two -> concrete rank-two geometry      LEAN VERIFIED
lower .qs far codimension-two elimination                          LEAN VERIFIED
lower .qs -> actual different-facet rank-three endpoint             LEAN VERIFIED

source-honest planar carrier                                       LEAN VERIFIED
highest singular pair slice                                        LEAN VERIFIED
nontrivial highest slice -> primitive two-monomial pair             LEAN VERIFIED
normalized .pr direction frontier                                  LEAN VERIFIED

left (1,V), V>1 finite-staircase branch completely consumed        LEAN VERIFIED
right (V,1), V>1 mirror completely consumed                        LEAN VERIFIED
nontrivial .pr -> unit (1,1) OR actual presented rank-two chart     LEAN VERIFIED

unit endpoint orientation / normalization                          LEAN VERIFIED
unit source/contact frontier                                       LEAN VERIFIED
unit staircase equations / separation / classification             LEAN VERIFIED
unit pair-degree reverse Rees                                      LEAN VERIFIED
unit first positive pair-Rees layer is strict interior             LEAN VERIFIED
unit endpoint-only support reconstruction                          LEAN VERIFIED
unit endpoint-only LEFT carrier -> False                           LEAN VERIFIED

unit endpoint-only RIGHT mirror                                    OPEN, thin
unit strict-interior elimination                                   OPEN, likely last local algebra
singleton/trivial highest-slice adapter                            OPEN
complete .pr closure                                               OPEN, assembly
.sp/.rq transport by coordinate permutation                        OPEN, assembly
all-other-facet A19 splice                                         OPEN, assembly
hypothesis-free presentedTerminal_impossible                       OPEN, assembly
public gradient_injective_of_hessianDeterminant_one                OPEN, boilerplate after resolver
final certification                                                OPEN
```

The strategic conclusion is important:

> **Do not reopen the left or right `V>1` finite-staircase mathematics.**
>
> Both non-unit orientations are finished. The local rank-three branch is now
> concentrated in the genuine unit staircase and the trivial/singleton highest
> slice. Once those are consumed, almost all remaining work is transport and
> assembly through infrastructure which already exists.

---

# 2. Status vocabulary — use literally

Use only:

- **LEAN VERIFIED** — accepted by Lean in the certified full-project build at
  the stated checkpoint;
- **SOURCE-LANDED / NOT LEAN VERIFIED** — committed, but no successful build of
  that exact head is known;
- **PAPER CANDIDATE** — paper mathematics exists but the corresponding Lean
  bridge is not compiled;
- **DIAGNOSTIC ONLY** — symbolic/computational evidence, not a proof theorem;
- **OPEN** — a genuine implementation, mathematical, or final-assembly seam
  remains.

For the final theorem, do not claim unrestricted HC4 until the public theorem
compiles **without**:

```text
a caller-supplied terminal resolver;
a JC2 hypothesis;
a balance hypothesis;
a global/source homogeneity hypothesis;
a repair-only contradiction.
```

---

# 3. Non-negotiable architectural rules

Carry these rules through the last sprint.

1. **Do not identify auxiliary Rees clocks with the zero blocker.** Contact,
   pair-degree, stationary, ordinary reverse-Rees, and determinant parameters
   remain distinct unless an explicit theorem identifies them.

2. **Do not use naked `withRepairOnly` as a contradiction.** Produce actual
   Hessian/Schur geometry first; only then use an existing certified repair or
   macro-progress consumer.

3. **Do not infer singularity of a chosen subpolynomial from singularity of a
   larger carrier.** Every singular face/layer in the final route must be an
   honest initial form, exact Rees layer, or have its own determinant theorem.

4. **Do not collapse the strict-low branch to generic JC2.** The source/contact
   provenance is stronger, and the same-carrier codimension-two branch is
   already closed by genuine rank-two geometry.

5. **Do not revive the four-monomial cross-ratio equation as a contradiction.**
   It is not one by itself.

6. **Do not conflate codimension-two branches.** The A19.55 same-carrier branch
   and the later lower-`.qs` outside-endpoint codimension-two branch have
   separate existing consumers and are already handled.

7. **Do not add a second global/rank-one recursion.** The existing finite
   `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace` is the public
   termination mechanism.

8. **Do not revive the false first-variation degree shortcut.** See
   `docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`.

9. **Do not revive the false generic stationary determinant implication.** See
   `HC4/Polynomial/StationaryDeterminantComparisonObstruction.lean` and
   `docs/STATIONARY_DETERMINANT_COMPARISON_AUDIT_2026-09-15.md`.

10. **Search before adding infrastructure.** There are already canonical owners
    for pair/contact Rees families, affine-line realization, finite-staircase
    arithmetic, terminal certificates, monomial Hessians, coordinate
    permutations, actual rank-two charts, rank-two-to-rank-three geometry,
    well-founded macro progress, and the public HC4 reduction.

11. **Root the last seam immediately.** Once a unit/singleton parent theorem is
    added, import its top owner in `HC4.lean` before moving farther up the proof.

---

# 4. Public end-to-end theorem is already reduced

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4Reduction.lean
```

Verified theorem:

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

This already performs:

```text
arbitrary F, det Hess F = 1
        + exact gradient collision
        ↓
canonical collision normalization
        ↓
positive canonical presentation
        ↓
existing finite rank-one termination trace
        ↓
normalized presented rank-three terminal
        ↓
ONLY REMAINING PUBLIC INPUT:
presented terminal is impossible
```

So the final public proof is not a new global theorem. It is only:

```text
finish local terminal resolver
        ↓
feed resolver into existing theorem
        ↓
unrestricted HC4 gradient injectivity
```

The trace consumer is already verified in

```text
AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean
```

with

```lean
AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.
  impossible_of_presentedTerminal_impossible
```

Do not redesign this layer.

---

# 5. Same-carrier codimension-two side is finished

Do not restart the codimension-two programme.

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoFinalGeometry.lean
```

Verified theorem:

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.
  exposedCodimensionTwo_resolvedRankTwoGeometry
```

Its output has no unresolved/default constructor. It produces concrete
rank-two geometry in one of four source-honest ways:

```text
1. nonzero 2x2 Hessian minor on the honest maximal top face;
2. nonzero 2x2 minor on an exact coordinate-max opening child;
3. rank-two geometry at the first kernel-row break of that opening child;
4. rank-two geometry at the first ordinary-degree reverse-Rees break from a
   rank-one top face back to the represented source.
```

The later lower-`.qs` outside-endpoint codimension-two branch is separately
eliminated by

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoElimination
```

and compressed into the different-facet endpoint by

```lean
C.qs_ray_boundaryOutcome_otherFacet
```

in

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetReduction.lean
```

Therefore the remaining proof should spend no time on JC2 or old
codimension-two casework.

---

# 6. Non-unit `.pr` branch is completely finished

For a nontrivial `.pr` highest slice, the parent assembly now gives:

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.
    pr_nontrivial_after_nonunit_closure
    ...
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ R : QsOtherFacetContactQuadraticReesPackage C,
      Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1) ∨
        Nonempty
          (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
            T.terminal.blocker.presented)
```

Owner:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly.lean
```

Interpretation:

```text
nontrivial .pr
   ↓
unit quotient (1,1)
OR
actual Hessian rank-two chart on the represented presented state
```

Both non-unit orientations are gone:

```text
left  (1,V), V>1       LEAN VERIFIED and consumed
right (V,1), V>1       LEAN VERIFIED and consumed
```

Do not reopen the finite-staircase cross-roof or central-rank-two proofs.

---

# 7. The unit stack now present in Lean

The unit direction is

```text
(1,-1,-1,-1).
```

The key discovery is that much of the old “special V=1 paper branch” is now
ordinary existing infrastructure specialized at `V=1`.

## 7.1 Endpoint orientation

Owner:

```text
...PrUnitEndpointOrientation.lean
```

The source-facing orientation package is compiled. Its `V=1` equalities are
proved from the quotient fibres without assuming a false non-unit bound.

## 7.2 Mixed bookkeeping labels normalize away

Owner:

```text
...PrUnitEndpointNormalization.lean
```

Canonical theorem:

```lean
QsOtherFacetPrUnitEndpointOrientationData.sameOrientation_normalForm
```

At `V=1`, left- and right-locked source exponents coincide after the literal
transverse bookkeeping normalization. Therefore the four bookkeeping cases
reduce source-honestly to two genuine orientations:

```text
highest-left  + locked-left
highest-right + locked-right
```

with endpoint/source/contact coefficient provenance retained.

This means the old paper scalar contradiction

```text
2 AD = BC,
AD = 2 BC
```

from `TwoFunctionMixedOrientationRigidity.lean` is now a **fallback**, not the
main route. Do not rebuild those extremal coefficient equations unless the
normalization interface later proves insufficient.

## 7.3 Unit contact frontier

Owner:

```text
...PrUnitContactFrontier.lean
```

Structures:

```lean
QsOtherFacetPrUnitLeftContactFrontierData
QsOtherFacetPrUnitRightContactFrontierData
```

Entry theorem:

```lean
S.pr_unitContactFrontier R Q hthree houtThree hnontrivial
```

returns one of these two exact orientations with literal endpoint provenance
and exact honest contact orders.

## 7.4 Unit staircase equations

Owner:

```text
...PrUnitStaircaseSupport.lean
```

Left orientation:

```text
(n-1)(r-1) = ell(n-k),
s = k+r-1.
```

Right orientation is the transverse swap.

The state-free generic staircase arithmetic is reused at `V=1`; the recent
compile repairs merely restored explicit `1 * (...)` forms expected by generic
lemmas.

## 7.5 Unit source/contact separation

Owner:

```text
...PrUnitContactSeparation.lean
```

Both orientations prove:

```lean
F.topFace_degree_eq :
  T.topFace.degree = 2 * (F.locked.ell + 1) + 1
```

and

```lean
F.highest_n_lt_locked_height hthree houtThree :
  F.highest.n < F.locked.ell + 1
```

Hence

```text
n <= ell.
```

This exact inequality is notably the hypothesis used by much of the
state-free finite-staircase transition/resonance library.

## 7.6 Exhaustive unit staircase classification

Owner:

```text
...PrUnitStaircaseClassification.lean
```

Both orientations have:

```lean
F.support_pair_pos hthree houtThree
```

and

```lean
F.support_staircase_classification hthree houtThree he
```

For each actual carrier support point, there is a finite staircase index `j`
with:

```text
pair <= n;
j <= ell;
j = 0   <-> pair = n;
j = ell <-> pair = 1.
```

Thus every non-endpoint point is a genuine strict interior staircase point.

## 7.7 Source-honest unit pair-degree reverse Rees

Owner:

```text
...PrUnitPairRees.lean
```

Constructors:

```lean
F.pairRees hthree houtThree
```

for both left and right orientations, returning the existing generic

```lean
QsOtherFacetPrPairReesData C P S F.highest.n.
```

The package retains:

```text
zero layer = actual highest slice;
Hessian determinant identically zero by reverse-Rees covariance;
a positive actual parameter layer.
```

## 7.8 Failure of endpoint-only support exposes a genuine interior first layer

Owner:

```text
...PrUnitPairReesFirstInterior.lean
```

Theorems:

```lean
D.firstPositiveLayer_pair_strictInterior_unitLeft  ...
D.firstPositiveLayer_pair_strictInterior_unitRight ...
```

If

```lean
hnot : ¬ F.NoStrictInteriorSupport
```

then every exponent in the first positive actual pair-Rees layer satisfies

```text
1 < e0+e1 < n.
```

This is already the honest “highest surviving interior fibre” selector needed
by the old pair-Rees programme.

## 7.9 Endpoint-only support reconstruction

Owner:

```text
...PrUnitNoInteriorSupport.lean
```

Definitions:

```lean
QsOtherFacetPrUnitLeftContactFrontierData.NoStrictInteriorSupport
QsOtherFacetPrUnitRightContactFrontierData.NoStrictInteriorSupport
```

Conditional support theorem in both orientations:

```lean
F.support_eq_locked_highest_of_noStrictInterior hno
```

with exact support:

```text
P.carrier.support =
  {C.ray.facetExponent,
   C.ray.outsideExponent,
   F.highest.e0,
   F.highest.e1}.
```

Important: this file **consumes** `NoStrictInteriorSupport`; it does not prove
it unconditionally.

---

# 8. Endpoint-only `V=1` algebra is essentially solved

The state-free two-function theorem was already generalized correctly.

Owner:

```text
HC4/Polynomial/TwoFunctionCarrierHessianRigidity.lean
```

Canonical theorem now assumes only positivity:

```lean
twoFunctionCarrier_hessian_impossible
    (V ell : ℕ)
    (hV : 0 < V)
    (hell : 0 < ell)
    ...
```

The old `1 < V` restriction is gone. Therefore `V=1` needs **no new Hessian
factorization**.

Source-facing package:

```text
...PrTwoFunctionCarrier.lean
```

with

```lean
QsOtherFacetPrTwoFunctionCarrierData.impossible : False
```

works at `V=1` directly.

## 8.1 Left unit endpoint-only branch — already compiled

Owner:

```text
...PrUnitEndpointClosure.lean
```

Canonical theorems:

```lean
QsOtherFacetPrUnitLeftContactFrontierData.
  twoFunctionCarrierData_of_noStrictInterior

QsOtherFacetPrUnitLeftContactFrontierData.
  impossible_of_noStrictInterior
```

The file reconstructs the literal four source monomials as

```text
twoFunctionCarrier 1 ell a b Ppoly Qpoly
```

with nonzero source coefficients and `Qpoly.derivative != 0`, then invokes the
existing state-free contradiction.

This is **LEAN VERIFIED** at `cf537...`.

## 8.2 FIRST SMALL TASK: right unit endpoint-only mirror

This is expected to be a thin coordinate-transport commit.

The right unit highest exponents are obtained from the left ones by swapping
source coordinates `2` and `3`. At `V=1` the locked pair has the same symmetry.

Prefer:

```lean
private def unitTransverseSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap (2 : Fin 4) 3
```

Use the already-verified covariance theorem in

```text
HC4/Newton/TerminalCoordinatePermutation.lean
```

```lean
HC4.Newton.hessianDeterminant_rename_perm
```

together with exact monomial renaming to put the right endpoint-only carrier
into the standard left two-function form.

Desired theorem:

```lean
theorem QsOtherFacetPrUnitRightContactFrontierData.
    impossible_of_noStrictInterior
    (F : ...)
    (hno : F.NoStrictInteriorSupport) : False
```

Implementation choices, in preference order:

1. Rename the actual carrier by `swap 2 3`, prove the renamed four monomials
   are exactly the left `twoFunctionCarrier` at `V=1`, transfer Hessian
   singularity by `hessianDeterminant_rename_perm`, invoke
   `twoFunctionCarrier_hessian_impossible`.
2. If the dependent rename is syntactically awkward, mirror the four short
   exponent-equality lemmas from the left file and use a renamed
   `twoFunctionCarrier`; still delegate all determinant algebra to the
   existing state-free theorem.

Do **not** duplicate `TwoFunctionCarrierHessianRigidity`.

Acceptance gate:

```text
right endpoint-only theorem compiled
+ imported by the next unit parent theorem
+ full root build green
```

---

# 9. The likely last genuine local mathematics: unit strict-interior support

After the endpoint-only mirror, the unit branch has exactly one unresolved
possibility:

```text
¬ F.NoStrictInteriorSupport.
```

That means one or more actual strict-interior staircase fibres survive.

This should be attacked using existing finite-staircase infrastructure, not by
starting a new determinant programme.

## 9.1 What NOT to do

The 15 September pair-Rees handoff established that the following is
insufficient by itself:

```text
locked-end first variation
+
highest-end first variation
-> contradiction.
```

The endpoint equations may concern different occupied fibres, and translated
two-mode solutions genuinely exist.

Also do **not** try:

```text
source Hessian singular
+ two Euler rows
-> stationary profile Hessian singular.
```

That implication has an explicit counterexample.

## 9.2 Reuse the finite-staircase library added after that audit

Search first in:

```text
HC4/Polynomial/FiniteStaircase*.lean
HC4/RationalRigidity/FiniteStaircaseCrossRoofTerminal.lean
HC4/RationalRigidity/FiniteStaircaseCrossRoofMirrorTerminal.lean
HC4/Valuation/...PrVGreaterOneFiniteStaircase*.lean
```

Much of the strongest state-free arithmetic does not mention `V` at all.
Examples already verified include:

```lean
no_left_staircase_unit_transition
```

in

```text
HC4/Polynomial/FiniteStaircaseTransitionArithmetic.lean
```

and the one-fibre resonance theorems in

```text
HC4/Polynomial/FiniteStaircaseOneFiberResonanceArithmetic.lean.
```

The unit contact separation gives exactly

```text
2 <= n <= ell,
```

which is the arithmetic regime consumed by these theorems.

## 9.3 Reuse the pair-Rees interior selector

For left unit:

```lean
rcases F.pairRees hthree houtThree with ⟨Dpair⟩
```

Under

```lean
hnot : ¬ F.NoStrictInteriorSupport
```

you already have

```lean
Dpair.firstPositiveLayer_pair_strictInterior_unitLeft
  F hthree houtThree hnot
```

so the highest surviving interior pair fibre is selected honestly.

The generic non-unit source adapters below were written with a `V` parameter
and should be audited for specialization at `V=1` before copying anything:

```text
...PrVGreaterOnePairReesFirstInteriorAffineLayer.lean
...PrVGreaterOnePairReesFirstInteriorMomentRealisation.lean
...PrVGreaterOnePairReesFirstVariation.lean
...PrVGreaterOnePairReesHighestFirstVariation.lean
```

In particular the assembly-facing first-variation proof used `F.V_gt_one`
only to obtain `0 < F.V`; the state-free bridge itself is positive-`V`
mathematics. At the unit endpoint that positivity is simply `by norm_num`.

## 9.4 Preferred implementation route for unit interior

Do this in small source adapters.

### U1 — unit first-interior affine layer

Create or factor a unit-capable affine-layer theorem using the already-proved
unit staircase classification and generic pair-Rees parameter-layer support.

Desired data are the same as the non-unit package:

```text
k, j,
1 < k < n,
0 < j < ell,
```

and for every selected source exponent, exact fixed quotient coordinates and
literal equality of layer coefficients with `P.carrier` coefficients.

Do not duplicate the generic coefficient-profile machinery if the existing
record can be generalized from a `LeftVContactFrontierData` parameter to the
smaller fields it actually uses. If changing that structure would cause wide
churn, make a small unit-specific record instead.

### U2 — exact affine/moment realization

Reuse the `RankThreeAffineLineData` construction pattern from

```text
...PairReesFirstInteriorMomentRealisation.lean
```

with `V=1`.

Expected output:

```lean
specialisedEulerHessian_eq_parallelStaircaseMomentHessian
```

for the actual selected unit layer.

### U3 — highest-end first variation at V=1

Reuse the state-free owner:

```text
HC4/Polynomial/HighestBinomialParallelFirstVariation.lean
```

and the generic bridge:

```text
HC4/Valuation/PlanarHighestFirstVariationBridge.lean
```

The expected equation is the same affine two-root Euler equation, now with
`V=1` supplied only to the harmless nonzero prefactor.

Do not stop here; this equation alone is not a contradiction.

### U4 — couple occupied unit fibres with the mature finite-staircase endgame

Before writing new algebra, inspect the deepest state-free theorems used by:

```text
...FiniteStaircaseOneFiberImpossible.lean
...FiniteStaircaseMultiFiberExtrema.lean
...FiniteStaircaseDualExtrema.lean
...FiniteStaircaseCrossRoof*.lean
```

The goal is to reuse their scalar/polynomial terminal statements at `V=1` and
write only the source-facing unit adapter.

A useful split is:

```text
only one occupied strict-interior pair fibre
OR
at least two occupied strict-interior pair fibres.
```

For one fibre, reuse the state-free one-fibre resonance/second-variation
contradictions already factored under `HC4/Polynomial/FiniteStaircase*`.

For multiple fibres, reuse the finite ordered staircase, extremal fibres,
cross-roof/transition arithmetic, and the already-verified forward/mirror
terminal algebra. The unit wall still has the same strictly ordered `(k,j)`
chain, and `n <= ell` remains available.

If an existing valuation theorem is blocked only because its structure stores
`1 < V`, **do not weaken a large non-unit structure globally**. Instead expose
the underlying state-free theorem or add a thin unit wrapper around the
smaller positive-`V` data it actually consumes.

### U5 — parent-facing no-interior theorem

The useful boundary is:

```lean
theorem QsOtherFacetPrUnitLeftContactFrontierData.noStrictInterior
    (F : ...)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.NoStrictInteriorSupport := by
  by_contra hnot
  ... finite staircase contradiction ...
```

Then close immediately:

```lean
theorem QsOtherFacetPrUnitLeftContactFrontierData.impossible
    ... : False := by
  exact F.impossible_of_noStrictInterior
    (F.noStrictInterior hthree houtThree)
```

### U6 — right unit strict-interior by transverse swap

Prefer transporting the completed left unit argument under `swap 2 3` rather
than rebuilding a second finite staircase proof.

If the dependent packages make full transport harder than mirroring two or
three source lemmas, mirror only those adapters; keep all state-free algebra
shared.

## 9.5 Fallback only: old paper V=1 coefficient route

The 12 September paper handoff records a separate mixed-orientation extremal
coefficient contradiction. Keep it as a fallback if the normalized source
packages unexpectedly block the finite-staircase specialization.

Owner:

```text
HC4/Polynomial/TwoFunctionMixedOrientationRigidity.lean
```

Final scalar theorem:

```lean
mixedOrientation_endpoint_coefficients_impossible
```

Do not use this unless necessary: `sameOrientation_normalForm` now removes the
bookkeeping distinction before the main algebra.

---

# 10. Collapse the entire nontrivial unit quotient

Once left/right unit contact frontiers are impossible, add a small theorem at
the quotient/parent level.

Suggested shape:

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_unit_impossible
    (S : ...)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 1)
    (hthree : ...)
    (houtThree : ...)
    (hnontrivial : ...) : False := by
  rcases S.pr_unitContactFrontier
      R Q hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with ⟨F⟩
    exact F.impossible hthree houtThree
  · rcases hright with ⟨F⟩
    exact F.impossible hthree houtThree
```

Then consume the unit alternative in

```lean
S.pr_nontrivial_after_nonunit_closure
```

to get the clean parent-facing theorem:

```lean
Nonempty
  (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
    T.terminal.blocker.presented)
```

for every **nontrivial** `.pr` highest slice.

Root this theorem in `HC4.lean` immediately.

---

# 11. SECOND LOCAL TASK: highest-slice singleton/trivial case

The current nontrivial theorem assumes

```lean
hnontrivial :
  ∃ a ∈ S.slice.support,
    ∃ b ∈ S.slice.support,
      a ≠ b.
```

Do not silently assume this for every highest slice.

The package itself only supplies:

```text
S.slice != 0;
S.pairLevel > 1;
hessianDeterminant S.slice = 0;
```

The complement is therefore a genuine singleton-support case which still must
be consumed.

## 11.1 Existing infrastructure to reuse

Source/slice provenance:

```lean
S.support_parent_and_pairLevel
S.support_affine_levels
S.support_source_and_finalLevel
S.coeff_eq_source_of_mem
```

from

```text
...OtherFacetPlanarHighestPairSlice.lean
```

Monomial obstruction:

```text
HC4/Polynomial/MonomialHessian.lean
```

canonical theorem:

```lean
hessianDeterminant_monomial_ne_zero
```

for a nonzero coefficient, all four positive exponents, and degree at least
three.

Mature singleton/vertical consumers:

```text
HC4/Valuation/AdaptiveAlignedSmithPositiveSingletonContradiction.lean
HC4/Valuation/AdaptiveAlignedSmithSingularSingletonContradiction.lean
HC4/Valuation/AdaptiveAlignedSmithSingletonRankThreeImpossible.lean
HC4/Valuation/AdaptiveAlignedSmithSingletonRankThreeTerminal.lean
HC4/RationalRigidity/RankThreeVerticalContradiction.lean
```

Useful terminal statements include:

```lean
smithSingleton_hessian_impossible_of_positive
impossible_of_singular_singletonSmithFiber
positive_singletonSmithFiber_impossible
```

## 11.2 Recommended singleton adapter

### S1 — turn singleton support into a literal monomial

From `S.slice_ne_zero` and the negation of nontrivial support, choose the unique
support exponent `e` and prove, with

```text
c := coeff e S.slice,
c != 0,
```

that

```lean
S.slice = MvPolynomial.monomial e c.
```

Keep `e` accompanied by:

```text
e ∈ P.carrier.support;
e ∈ represented source support;
pair degree = S.pairLevel > 1;
both planar affine equations.
```

### S2 — split on coordinate zeros

If every coordinate of `e` is positive, then ordinary degree is automatically
at least four. Apply

```lean
HC4.Polynomial.hessianDeterminant_monomial_ne_zero
```

to contradict `S.hessian_zero` directly.

This should be the shortest branch and should be attempted first.

### S3 — zero-coordinate branch

Do not assume this branch is impossible without proof.

Use the retained planar affine equations and the locked source-ray sign
relations to identify which coordinate can vanish. Search the existing
first-nonfacet/singleton/vertical endpoint machinery before creating a new
record.

Preferred conclusion is one of the existing Smith/vertical singleton
interfaces with:

```text
positive transverse exponents;
exact singleton singular restriction;
a genuine longitudinal departure/nonconstant coefficient polynomial.
```

Then invoke an existing singleton contradiction theorem.

If the planar affine constraints themselves rule out every zero coordinate in
the highest `pairLevel>1` slice, prove that directly and avoid Smith repackaging.

### S4 — parent theorem

Desired interface:

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.trivial_impossible
    ...
    (htrivial :
      ¬ ∃ a ∈ S.slice.support,
          ∃ b ∈ S.slice.support,
            a ≠ b) : False
```

If the mature singleton consumer naturally yields actual rank-two/rank-three
geometry instead of `False`, retain that geometry and adapt the parent output
accordingly. Do not throw away source geometry merely to manufacture a local
contradiction.

---

# 12. Complete `.pr` closure

After:

```text
unit nontrivial quotient impossible;
singleton/trivial highest slice consumed;
```

the `.pr` branch should have no unresolved algebraic case.

The parent proof should split only on whether `S.slice.support` contains two
distinct exponents.

Schematic:

```lean
by_cases hnontrivial :
    ∃ a ∈ S.slice.support,
      ∃ b ∈ S.slice.support,
        a ≠ b
· -- nontrivial
  rcases S.pr_nontrivial_after_nonunit_closure
      hthree houtThree hnontrivial with ⟨R, hunit | hrank⟩
  · exact (S.pr_unit_impossible R ...).elim
  · exact hrank
· -- singleton
  exact (S.trivial_impossible ... hnontrivial).elim
```

Preferred final output for `.pr`:

```lean
Nonempty
  (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
    T.terminal.blocker.presented)
```

rather than `False`, because the finite-staircase central branches deliberately
produce real rank-two Hessian geometry.

Do not pretend an actual rank-two chart is itself contradictory.

---

# 13. Consume actual rank-two geometry through existing infrastructure

Canonical owner:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree.lean
```

Verified method:

```lean
AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart.rankThreeGeometry
```

This yields actual rank-three geometry by an honest split:

```text
nonzero constant 3x3 Hessian minor
OR
exact zero-Schur four-block with complete source rank-three geometry.
```

This is the right architecture: **geometry first**.

The repository already contains geometry-backed progress patterns, including

```text
AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry.lean
AdaptiveAlignedSmithCanonicalZeroStrictLowDirectRankTwoProgress.lean
AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoFinalGeometry.lean
```

Search for the narrowest existing consumer of an

```lean
AdaptiveAlignedSmithCanonicalActualRankThreeGeometry
```

or actual rank-two chart before adding a new progress record.

The final local `.pr` theorem may either:

```text
return the actual rank-two chart to an existing higher consumer;
```

or

```text
immediately attach the existing rankThreeGeometry/global successor packet.
```

Choose whichever requires the least new dependent plumbing. Do not create a
second rank-two geometry type.

---

# 14. `.sp` / `.rq`: transport, do not clone

The lower `.qs` reduction already gives an actual different facet:

```lean
C.qs_ray_boundaryOutcome_otherFacet
```

with

```lean
∃ next : ToricFacet,
  next ≠ .qs ∧
  MvRankThreeOnFacet next C.ray.outsideExponent.
```

Therefore `next` is `.pr`, `.sp`, or `.rq`.

Do not duplicate the `.pr` staircase proof twice.

## 14.1 Existing permutation infrastructure

Owner:

```text
HC4/Newton/TerminalCoordinatePermutation.lean
```

Verified theorems:

```lean
hessian_rename_perm
hessianDeterminant_rename_perm
isPolynomialMongeAmpere_rename_perm
mvGradientMap_rename_perm
mvGradientMap_rename_perm_injective_iff
```

Also search/reuse:

```text
HC4/Valuation/PermutedPolynomialHessianFourBlock.lean
HC4/Valuation/PermutedFamilyHessianFourBlock.lean
```

## 14.2 Recommended implementation

Write one facet transport theorem.

1. `fin_cases next`.
2. `.qs` is eliminated by `next ≠ .qs`.
3. `.pr` calls the completed `.pr` theorem directly.
4. `.sp` and `.rq` use explicit `Equiv.Perm (Fin 4)` values sending the
   selected omitted coordinate into the `.pr` role.
5. Rename only the source-honest data needed to invoke the `.pr` closure.
6. Transport Hessian determinant/rank geometry by existing covariance theorems.

If transporting deeply dependent `P/S/R` records directly is painful, do not
clone their proofs. Instead put the `.pr` closure behind a smaller
facet-generic theorem formulated in terms of the renamed polynomial/ray data.

Keep all permutations explicit and prove their coordinate values with
`by decide` where possible.

---

# 15. Upstream A19 splice

The lower `.qs` compression already exists.

Owner:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowQsReducedLowerFrontier.lean
```

Verified theorem:

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.
  qs_rankThree_startCodimensionTwo_or_otherFacet_or_quadraticSquare
```

It retains exactly:

```text
1. lower ray starts at a codimension-two endpoint;
2. lower ray starts rank-three on .qs and reaches an actual different-facet
   rank-three endpoint;
3. represented source contains the literal coordinate-zero quadratic square.
```

Do not erase the sibling constructors. They have dedicated mature consumers.

After the all-other-facet theorem exists, use reverse-import search / generated
module index to locate the narrowest theorem still exposing this three-way
frontier.

Likely route names include:

```text
...ZeroStrictLowQsReducedLowerFrontier
...ZeroStrictLowCrossFacetBoundaryTransition
...ZeroStrictLowRankThreeBoundaryReduction
...ZeroStrictLowTerminalResidualReduction
...RankOneReesZeroStrictLowTerminal
...HC4ReachableTerminalReduction
...ReachableHC4Reduction
...HC4Reduction
```

Do **not** edit all of these mechanically. Add the strongest new local theorem
as high as possible, rebuild, and let Lean show the next unmatched constructor.

The same-carrier codimension-two branch is already geometry-resolved. The
quadratic-square branch already has dedicated quadratic/low-degree machinery.
The new work should only consume the actual other-facet constructor.

---

# 16. Target local theorem: presented terminal impossible

The proof should culminate in a theorem with the semantic shape:

```lean
theorem presentedTerminal_impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0) :
    False
```

Use the repository's preferred namespace/name if an owner already exists.

Do not add another recursive argument here. The finite termination trace was
already constructed, and

```lean
AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.
  impossible_of_presentedTerminal_impossible
```

is ready to consume this theorem structurally.

---

# 17. Public unrestricted HC4 theorem — expected boilerplate

Once `presentedTerminal_impossible` is green, the public theorem should be only
an application of the existing reduction.

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

Use the existing public namespace/naming convention if there is already a
placeholder or theorem front for the unrestricted statement.

Do not delay the main theorem for cosmetic aliases.

---

# 18. Recommended commit order from the fresh chat

Keep the remaining work small and compile/root after each semantic seam.

## U1 — right endpoint-only unit mirror

```text
right unit NoStrictInteriorSupport -> False
```

using `swap 2 3` and the existing two-function theorem.

## U2 — unit first-interior source adapter

```text
¬ NoStrictInteriorSupport
-> honest highest surviving interior affine fibre at V=1
```

Reuse generic pair-Rees layer/support infrastructure.

## U3 — unit interior finite-staircase contradiction

Consume one-fibre and multi-fibre possibilities by the existing state-free
finite-staircase terminal library. Prefer adapting mature scalar theorems over
copying `V>1` dependent records.

Output:

```text
left unit noStrictInterior
right unit noStrictInterior / transported mirror
left/right unit impossible
```

## U4 — unit quotient parent closure

```text
Q : QsOtherFacetPrQuotientCarrierData C P 1 1 -> False
```

for nontrivial `S`.

## S1 — singleton monomial adapter

```text
singleton support -> literal monomial
all-positive case -> MonomialHessian contradiction
zero-coordinate case -> existing singleton/vertical consumer
```

## P1 — complete `.pr`

```text
any .pr highest slice -> actual presented rank-two chart
```

Root this in `HC4.lean`.

## F1 — `.sp/.rq` coordinate transport

```text
any actual different-facet endpoint -> transported .pr closure
```

No cloned staircase mathematics.

## A1 — splice actual other-facet branch into A19 terminal frontier

Preserve codimension-two and quadratic-square sibling consumers.

## T1 — hypothesis-free `presentedTerminal_impossible`

Use existing rank-two/rank-three geometry and global macro/terminal consumers.
No new recursion.

## H1 — public HC4 theorem

Apply `gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible`.

## C1 — final certification

Full root build + all audits.

---

# 19. How to decide whether a new lemma is justified

Before adding any new theorem, ask:

```text
Is this source provenance already stored?
Is this merely a coordinate rename?
Is the algebra already state-free under HC4/Polynomial or HC4/RationalRigidity?
Is there already an actual rank-two/rank-three geometry consumer?
Is this only repairing a dependent-type interface rather than proving math?
```

Search first in:

```text
docs/generated/DECLARATION_INDEX.md
docs/generated/LEAN_MODULE_INDEX.md
docs/generated/LOCAL_IMPORT_EDGES.md
```

and by theorem/file keywords.

The remaining proof should become **thinner**, not introduce a new architectural
subsystem.

---

# 20. Historical routes that must remain closed

## 20.1 Generic stationary determinant comparison — do not revive

The explicit obstruction is formalized in:

```text
HC4/Polynomial/StationaryDeterminantComparisonObstruction.lean
```

Source singularity plus the available Euler rows does not force the canonical
parameter/depth profile determinant to vanish.

The extensive stationary modules remain useful for exact coefficients and
Euler bookkeeping, but they are not the preferred final unit route.

## 20.2 First-variation degree <= 1 shortcut — false

The counterexample/audit is in:

```text
docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md
```

Do not infer endpoint-only support from one affine two-root first variation.

## 20.3 Generic JC2 — unnecessary and forbidden on this route

The strict-low source/contact branch has stronger structure. The live
codimension-two branch is already geometry-resolved without JC2.

## 20.4 Repair-only rank changes — not a proof

Whenever rank promotion is used, retain the actual Hessian/Schur geometry that
licenses it.

---

# 21. Existing papers/handoffs to consult, in order

For the fresh chat, use this document as the status/TODO authority and consult
older documents only for details.

## 21.1 Unit and singleton paper mathematics

```text
docs/HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md
```

Relevant sections:

```text
5.4 full two-function Hessian
5.5 singleton/developable escape
5.6 V=1
```

Be aware that some of this paper work has since been superseded by stronger
Lean infrastructure, especially the generalized positive-`V` two-function
contradiction and the unit endpoint normalization.

## 21.2 Pair-Rees endpoint-coupling warnings

```text
docs/HANDOFF_2026-09-15_HC4_PAIR_REES_FINAL_CLOSURE.md
```

Use it for:

```text
honest contact/pair Rees interfaces;
why two first variations alone are insufficient;
finite-staircase notation and provenance.
```

Its old statement that finite-staircase coupling was the main `V>1` gap is
historical: that branch has since been closed.

## 21.3 Previous final assembly

```text
docs/HANDOFF_2026-09-16_HC4_FINAL_ASSEMBLY.md
```

Use it for:

```text
right V>1 mirror details;
actual-rank-two chart lifting;
public terminal-resolver architecture.
```

Its status table is superseded by this file.

---

# 22. Certification gate before claiming unrestricted HC4

Require all of the following on the final head:

```text
1. `HC4.lean` full root build green.
2. Final public unrestricted theorem explicitly rooted.
3. Unit and singleton closure owners explicitly rooted through the final
   assembly graph.
4. Theorem axiom audit green.
5. Negative control rejected.
6. Escape-hatch audit green:
   no sorry
   no admit
   no native_decide proof escape
   no unsafe proof bridge.
7. Public theorem has no:
   terminal-resolver argument
   JC2 hypothesis
   balance assumption
   source/global homogeneity assumption
   repair-only contradiction.
```

Also manually inspect `#print axioms` or the workflow output for the exact new
public theorem before changing repository documentation to say HC4 is proved.

---

# 23. What “very close” means at this checkpoint

The proof is no longer waiting on broad global mathematics.

The hard completed infrastructure includes:

```text
unrestricted front door;
well-founded rank-one termination trace;
source-honest codimension-two closure;
source-honest planar extraction;
line-supported primitive highest-slice rigidity;
full left finite-staircase closure;
full right finite-staircase mirror;
actual presented rank-two chart lifting;
positive-V two-function Hessian contradiction;
unit endpoint orientation/contact/staircase machinery;
unit pair Rees and first strict-interior selector;
unit endpoint-only left contradiction;
coordinate-permutation Hessian covariance;
rank-two -> actual rank-three geometry;
public reduction to one terminal resolver.
```

The remaining likely substantive local mathematics is therefore only:

```text
unit strict-interior staircase elimination
+
highest-slice singleton adapter.
```

The right endpoint unit branch is a mirror/rename. The `.sp/.rq` work should be
coordinate transport. The public HC4 theorem is already reduced to the terminal
resolver.

That is the correct sense in which the project is now in its last mile.

---

# 24. Fresh-chat execution prompt

Use the following prompt verbatim or nearly verbatim in a fresh chat:

```text
Continue the unrestricted HC4 final closure from
`docs/HANDOFF_2026-09-16_HC4_LAST_MILE_PUBLIC_CLOSURE.md` on PR #34.

Re-audit the live PR head and CI first. The certified baseline in the handoff is
`cf53735baedb4555df9d8a1c6c63cef7cc17fdec` with Lean CI run `35139954849`
green through build, axiom audit, negative control, and escape-hatch audit.

Treat the completed left/right V>1 finite-staircase branches, codimension-two
geometry, global rank-one termination trace, and public HC4 reduction as closed.
Do not reopen them.

Immediate critical path:

1. close the right endpoint-only V=1 unit branch by transverse coordinate swap
   and the existing positive-V two-function Hessian theorem;
2. eliminate surviving strict-interior V=1 staircase support, reusing the
   existing unit pair-Rees selector and the mature state-free finite-staircase
   one-/multi-fibre terminal algebra before adding any new determinant lemma;
3. collapse the entire nontrivial unit quotient;
4. consume the singleton/trivial highest slice, preferring the direct monomial
   Hessian obstruction and existing singleton/vertical consumers;
5. produce the complete `.pr` actual-rank-two closure and root it;
6. transport `.sp/.rq` into `.pr` by explicit coordinate permutations, without
   cloning staircase mathematics;
7. splice the all-other-facet closure into the existing A19 terminal frontier,
   preserving the already-resolved codimension-two and quadratic-square sibling
   branches;
8. prove the hypothesis-free `presentedTerminal_impossible` using the existing
   geometry-bearing consumers and no new recursion;
9. feed it into
   `gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible`
   to obtain the public unrestricted HC4 theorem;
10. run the full root/axiom/negative-control/escape-hatch certification gate.

Preserve exact status labels throughout: LEAN VERIFIED, SOURCE-LANDED / NOT LEAN
VERIFIED, PAPER CANDIDATE, DIAGNOSTIC ONLY, OPEN.

Do not identify auxiliary Rees clocks with the zero blocker, do not use naked
`withRepairOnly`, do not collapse the strict-low branch to generic JC2, do not
revive the false first-variation degree shortcut, and do not revive the false
generic stationary determinant implication.

Search existing infrastructure before adding anything. The goal is to finish
HC4, not create another proof architecture.
```

---

# 25. Immediate first commands/checks in the fresh chat

Before coding:

```text
1. fetch PR #34 metadata/head;
2. inspect commits after cf53735b... if any;
3. inspect HC4.lean tail;
4. inspect current unit endpoint closure/right mirror status;
5. search `Unit`, `FiniteStaircase`, `oneFiber_impossible`, `CrossRoof`,
   `singleton`, and `ActualRankTwo` declarations in the generated index;
6. only then edit.
```

After every semantic commit:

```text
root it or import it from an already-rooted parent;
run full build;
fix compiler errors in place;
do not redesign on a type-normalization failure.
```

The recent unit failures were all small Lean normalization issues (`omega`,
`↑1 * ...`, pair-degree unfolding, eta-expanded coordinate projections). They
were not mathematical counterexamples. Continue to distinguish compiler seams
from actual proof gaps.

---

# 26. Final target

The repository should end with a rooted, audited theorem semantically equivalent
to:

```lean
theorem gradient_injective_of_hessianDeterminant_one
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F)
```

with no external resolver and no additional mathematical hypothesis.

Only once that exact public endpoint passes the complete certification gate
should the project status be changed from “final closure in progress” to
“unrestricted HC4 Lean proof complete”.
