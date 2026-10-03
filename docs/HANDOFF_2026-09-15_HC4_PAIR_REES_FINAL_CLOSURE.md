# HC4 pair-Rees final closure handoff — 15 September 2026

> **Purpose.** This is the current implementation-grade handoff for the final
> unrestricted HC4 sprint on PR #34. It is written so that a fresh context
> window can resume without reconstructing the last several days of algebra,
> Lean plumbing, failed approaches, and source-provenance decisions.
>
> **This document supersedes the status/TODO sections of**
> `docs/HANDOFF_2026-09-15_HC4_FINAL_LEAN_CLOSURE.md`.
> The older 15 September handoff remains useful for the stationary machinery
> and historical audit trail, but its proposed generic stationary
> source/profile determinant bridge is **not** the current route.
>
> **Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`
>
> **PR:** `#34 — A18.4.42 collapse final termination frontier`
>
> **Branch:** `final-assembly/a18-4-42-termination-frontier`
>
> **Current green source head:**
> `e121f5c206443ff6345b00c2bf2a8b581ae1c831`
> (`Make pair-Rees V positivity explicit`)
>
> **Lean CI:** workflow run **#2318**, conclusion **success**.
>
> At this checkpoint the newly rooted direct pair-Rees highest-end
> first-variation chain is accepted by the Lean kernel together with the full
> root build and existing audit jobs.

---

# 0. Start here in a fresh context

The shortest accurate summary is:

```text
Global HC4 entry / normalisation / rank-one termination       LEAN VERIFIED
A19.55 same-carrier codimension-two -> rank-two geometry      LEAN VERIFIED
lower .qs outside codimension-two elimination                 LEAN VERIFIED
rank-three other-facet planar carrier / highest slice         LEAN VERIFIED
left (1,V), V>1 staircase classification                      LEAN VERIFIED
locked-end honest contact-Rees first variation                LEAN VERIFIED
highest-end honest pair-Rees first variation                  LEAN VERIFIED

finite-staircase coupling -> NoStrictInteriorSupport           OPEN
NoStrictInteriorSupport -> exact two-function carrier         LEAN VERIFIED
exact two-function carrier -> False                            LEAN VERIFIED

right (V,1), V>1 symmetry wrapper                             OPEN
V=1 source-facing closure                                     OPEN
.pr wrapper                                                    OPEN
.sp/.rq cyclic relabelling                                    OPEN
other-facet/A19/global splice                                 OPEN
public unrestricted HC4 theorem without resolver              OPEN
```

The immediate task is **not** another Rees family, another stationary profile,
or another global descent. The immediate mathematical task is:

> Combine the already-verified **lowest-surviving-interior** equation from the
> contact-oriented Rees with the already-verified
> **highest-surviving-interior** equation from the pair-degree reverse Rees,
> together with the finite staircase relation, to prove
>
> ```lean
> F.NoStrictInteriorSupport.
> ```

Once that proposition is proved, the left `V>1` branch is already closed by
existing Lean code.

A good fresh-session prompt is included verbatim in section 23.

---

# 1. Status vocabulary — use it literally

Use only these labels when reporting progress:

- **LEAN VERIFIED** — the declaration is in the rooted source graph and a
  successful Lean build is known for the relevant head.
- **SOURCE-LANDED / NOT LEAN VERIFIED** — code is committed but an exact-head
  successful build is not yet known.
- **PAPER CANDIDATE** — a paper argument or symbolic calculation exists, but
  it is not yet a Lean theorem.
- **DIAGNOSTIC ONLY** — useful computational/symbolic evidence that must not be
  promoted into the proof without a theorem.
- **OPEN** — a genuine missing mathematical or formal bridge remains.

Do **not** call unrestricted HC4 proved until the final public
`det Hess = 1 -> Function.Injective gradient` theorem compiles without a
caller-supplied terminal resolver, JC2 assumption, balance assumption,
homogeneity assumption, or repair-only contradiction.

---

# 2. Non-negotiable architectural rules

Carry these rules into every continuation.

1. **Do not identify auxiliary Rees clocks with the zero blocker.**
   The contact Rees, pair-degree reverse Rees, stationary ramification, and
   ordinary reverse-Rees parameters are auxiliary filtrations unless an
   explicit theorem identifies them with something else.

2. **Do not use naked `withRepairOnly` progress as a contradiction.**
   Rank-two progress must carry actual Hessian/Schur geometry.

3. **Do not infer singularity of a superface from a smaller singular ray.**
   Every singular carrier/slice used in the proof has its own honest
   determinant-defect or Rees-covariance argument.

4. **Do not collapse the A19 strict-low branch to generic JC2.**
   The live branch retains much stronger source/contact/ray provenance.

5. **Do not use the old four-monomial cross-ratio equation as a contradiction
   by itself.**

6. **Do not conflate two different codimension-two branches.**
   The A19.55 same-carrier exposed codimension-two branch is different from the
   later lower `.qs` outside-endpoint codimension-two branch.

7. **Do not add a second global/rank-one recursion.**
   The existing raw-defect termination trace is the global termination
   mechanism.

8. **Do not reintroduce the false first-variation degree shortcut.**
   The statement

   ```text
   first variation + staircase arithmetic -> degree <= 1
   ```

   is false. See
   `docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`, especially

   ```text
   V=2, ell=4, n=3, k=2, j=2,
   phi(T)=(5+4T)^2.
   ```

9. **Do not revive the generic stationary source/profile determinant
   implication.** Section 5 explains why it is false and what replaced it.

10. **Search existing infrastructure before adding a package.** The current
    tree already has canonical owners for the contact Rees, pair Rees, affine
    layer, moment Hessians, dual-jet bridge, two-function carrier, reverse
    Rees, first-kernel break, and global rank-one trace.

---

# 3. Executive proof architecture from HC4 down to the live gap

The public reduction already exists in

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4Reduction.lean
```

with

```lean
gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
```

which proves unrestricted determinant-one gradient injectivity from the sole
remaining resolver

```lean
forall {state},
  AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
    canonicalAdaptiveAlignedSmithRepairRanking state 0 -> False.
```

Thus the proposition-level front door is already unrestricted. The remaining
work is to prove that terminal resolver internally.

The mature global/local architecture is:

```text
arbitrary det-Hess-one source + exact gradient collision
        |
        v
canonical collision normalisation
        |
        v
positive Rees presentation
        |
        v
existing raw-defect rank-one termination trace
        |
        v
zero-clock strict-low terminal frontier
        |
        +-------------------------------+
        |                               |
        v                               v
A19.55 exposed                  rank-three first-nonfacet /
codimension two                 lower .qs boundary
        |                               |
        | LEAN VERIFIED                 | LEAN VERIFIED
        v                               v
explicit rank-two geometry      actual other-facet rank-three endpoint
                                        |
                                        v
                               .pr/.sp/.rq local closure
                                        |
                                        v
                                 terminal impossible
                                        |
                                        v
                              unrestricted HC4 theorem
```

The codimension-two side is no longer the mathematical blocker. The live
blocker is the rank-three other-facet local closure, specifically the `.pr`
left non-unit interior staircase.

---

# 4. A19.55 codimension-two status: already locally closed

Do not restart the old codimension-two programme.

File:

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoFinalGeometry.lean
```

**LEAN VERIFIED** theorem:

```lean
AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.
  exposedCodimensionTwo_resolvedRankTwoGeometry
```

It returns one of four concrete geometry-bearing outcomes:

```text
1. nonzero 2x2 Hessian minor on the honest maximal top face;
2. nonzero 2x2 Hessian minor on an exact coordinate-max opening child;
3. rank-two geometry at the first kernel-row break of that opening child;
4. rank-two geometry at the first ordinary-degree reverse-Rees break from a
   rank-one top face back to the represented source.
```

The inductive output is

```lean
ExposedCodimensionTwoResolvedRankTwoGeometry
```

and intentionally has **no unresolved/default constructor**.

This is source-honest, contains no generic-JC2 fallback, and does not identify
its auxiliary Rees parameter with the zero blocker.

The separate later lower `.qs` outside-endpoint codimension-two case is also
already eliminated by

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoElimination
```

and compressed by

```lean
C.qs_ray_boundaryOutcome_otherFacet
```

in

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetReduction.lean.
```

So a fresh session should **not** spend time rebuilding either codimension-two
argument.

---

# 5. Critical correction: the old stationary determinant route is superseded

The earlier 15 September handoff proposed the chain

```text
source sheared determinantCore = 0
    -> stationaryProfileHessianDetFamily = 0
    -> stationaryIntegralProfileHessianDet = 0
    -> False.
```

That generic comparison is not valid.

## 5.1 Lean-verified obstruction

File:

```text
HC4/Polynomial/StationaryDeterminantComparisonObstruction.lean
```

contains an explicit finite-vector example satisfying the two Euler-row
relations with singular source Hessian and nonzero active minor, while the
canonical profile determinant is nonzero.

The concrete diagnostic is based on

```text
Q = tau^6 y^2 z^3 w^8,
V=2, ell=4, n=3, r=6.
```

At the matrix level the module verifies source determinant zero but profile
core determinant `-36`.

This means:

```text
source Hessian singular + the two Euler rows
    DOES NOT imply
canonical parameter/depth profile determinant singular.
```

The reason is structural: the source Hessian still contains derivatives in an
inner/profile direction omitted by the naive parameter/depth determinant.

## 5.2 What remains useful from the stationary work

The stationary modules are still valuable audited infrastructure and may be
useful for coefficient identities, but they are **not the current critical
path**.

In particular keep:

```text
stationary exact-order lemmas;
stationary carrier support/profile bookkeeping;
weighted Euler identities;
falling Hessian rows;
StationaryDeterminantComparisonObstruction as a prohibition test.
```

Do **not** attempt to prove the old generic theorem

```lean
D.stationaryProfileHessianDetFamily_eq_zero
```

from only source singularity and the two Euler rows.

## 5.3 Replacement

The replacement is source-honest and endpoint-sensitive:

```text
locked endpoint
   -> contact-oriented singular Rees
   -> first surviving interior fibre from the locked side
   -> locked-end affine two-root equation

highest primitive endpoint
   -> pair-degree reverse singular Rees
   -> first surviving interior fibre from the highest side
   -> highest-end affine two-root equation
```

Both halves now compile.

---

# 6. Current left `(1,V)`, `V>1` notation

For the local live branch fix

```lean
C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs
P : QsOtherFacetPlanarCarrierPackage C .pr
S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P
R : QsOtherFacetContactQuadraticReesPackage C
F : QsOtherFacetPrLeftVContactFrontierData C P S R
```

and

```lean
hthree    : MvRankThreeOnFacet .qs C.ray.facetExponent
houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent.
```

Mental notation:

```text
V   := F.V,                 with 1 < V
n   := F.highest.n,         with 2 <= n
ell := F.locked.ell,        with 0 < ell and n < ell+1
k   := pair degree
j   := first-transverse index minus one.
```

Every actual carrier support exponent lies on the quotient staircase and
satisfies the wall relation

```text
(n-1) * j = ell * (n-k).
```

The endpoints are exactly

```text
highest: k=n, j=0
locked : k=1, j=ell.
```

A strict interior point has

```text
1 < k < n,
0 < j < ell.
```

The Lean owner is

```text
...PrVGreaterOneStaircaseClassification.lean
```

with

```lean
F.support_staircase_classification hthree houtThree
```

and the underlying affine equalities in

```lean
F.support_staircase_equations hthree houtThree.
```

---

# 7. The exact downstream obligation: `NoStrictInteriorSupport`

File:

```text
...PrVGreaterOneNoInteriorSupport.lean
```

defines

```lean
F.NoStrictInteriorSupport : Prop :=
  forall {e}, e in P.carrier.support ->
    rankThreeQuotientCoordinate 1 F.V e |>.pair = 1 ||
    rankThreeQuotientCoordinate 1 F.V e |>.pair = F.highest.n
```

(in Lean the final connective is the logical `Or`, not boolean `||`).

Once `hno : F.NoStrictInteriorSupport` exists, the rest of the left branch is
already formal.

**LEAN VERIFIED:**

```lean
F.support_eq_locked_highest_of_noStrictInterior hno
```

proves literal source support equality

```text
P.carrier.support =
  {facetExponent, outsideExponent, highest.e0, highest.e1}.
```

Then

```text
...PrVGreaterOneTwoFunctionReconstruction.lean
```

contains

```lean
F.twoFunctionCarrierData_of_noStrictInterior hno
```

and finally

```lean
F.impossible_of_noStrictInterior hno : False.
```

So the local target should be a theorem of the form

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.noStrictInterior
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.NoStrictInteriorSupport := by
  ...
```

and then the parent-facing contradiction becomes simply

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.impossible
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : ...)
    (houtThree : ...) : False := by
  exact F.impossible_of_noStrictInterior
    (F.noStrictInterior hthree houtThree)
```

There is no reason to expose the Rees packages above this theorem boundary.

---

# 8. LEAN VERIFIED locked-end route

The locked endpoint already had an honest first-variation pipeline before the
new pair-Rees work.

## 8.1 Honest contact-oriented family

Use the existing

```lean
Dcontact : QsOtherFacetPrLeftVPlanarContactReesData F
```

constructed by the existing `F.planarContactRees` theorem.

The family is source-derived and Hessian-singular; its first positive actual
layer is the first surviving strict-interior layer from the locked/contact
side.

## 8.2 Exact affine/moment realization

Canonical files:

```text
...PlanarInteriorFirstLayer.lean
...PlanarInteriorAffineCoordinates.lean
...PlanarInteriorAffineLayer.lean
...PlanarInteriorAffineRealisation.lean
...PlanarInteriorMomentRealisation.lean
```

They retain the actual source coefficients and realize the selected layer as a
rank-three affine line with direction

```text
(1,-1,-1,-V).
```

## 8.3 Locked-end Euler equation

File:

```text
...PlanarInteriorFirstVariation.lean
```

**LEAN VERIFIED:**

```lean
Dcontact.exists_firstInteriorAffineLayer_affineTwoRootEulerOperator_eq_zero
  hthree houtThree hnot
```

where `hnot : not F.NoStrictInteriorSupport`.

It produces

```lean
A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dcontact
```

whose honest coefficient profile `A.coefficientProfile` satisfies

```lean
affineTwoRootEulerOperator
  (a * (ell+1))
  (b * ell)
  (A.k - 1)
  A.coefficientProfile = 0,
```

with literal nonzero locked source coefficients

```text
a = coeff facetExponent P.carrier,
b = coeff outsideExponent P.carrier.
```

The two characteristic roots are the adjacent pair

```text
A.k-1, A.k.
```

## 8.4 Translated two-mode normal form

File:

```text
...PlanarInteriorTwoModeNormalForm.lean
```

**LEAN VERIFIED:**

```lean
Dcontact.exists_firstInteriorAffineLayer_translated_eq_twoMode
  hthree houtThree hnot
```

After translation by the locked affine root

```text
alpha = -(a(ell+1))/(b ell),
```

the selected profile is exactly

```text
p X^(k-1) + q X^k
```

with

```text
p != 0 or q != 0.
```

Important: this does **not** by itself prove the original source fibre contains
only two monomials, and it does **not** imply the profile has degree at most
one. It is a translated adjacent-mode statement.

---

# 9. LEAN VERIFIED highest-end pair-Rees route

This is the major new progress since the older 15 September handoff.

## 9.1 Pair-degree reverse Rees

File:

```text
...PrVGreaterOnePairRees.lean
```

Natural pair weight:

```lean
qsPrPairNatWeight : Fin 4 -> Nat := ![1,1,0,0].
```

The family is the bounded reverse-weighted Rees of the **actual carrier** by
pair degree, oriented so the primitive highest pair is parameter order zero.

Package:

```lean
QsOtherFacetPrPairReesData C P S n
```

stores:

```text
n >= 2;
S.pairLevel = n;
reverse-weight bound;
family;
zero/special fibre = S.slice;
hessian determinant = 0;
positive actual parameter layer.
```

Constructors:

```lean
F.pairRees hthree houtThree
```

for left orientation, and a corresponding right-oriented constructor already
exists.

Exact parameter coefficient:

```lean
Dpair.parameterLayer_coeff q e
```

and exact support theorem in

```text
...PairReesFirstInterior.lean:
```

```lean
Dpair.parameterLayer_support q :
  (familyParameterLayer Dpair.family q).support =
    P.carrier.support.filter fun e =>
      n - (e 0 + e 1) = q.
```

**Compiler pitfall:** do not write

```lean
qsPrPairNatWeight e
```

for an exponent `e`. `qsPrPairNatWeight` is the coordinate weight vector
`Fin 4 -> Nat`, not a function on `Finsupp` exponents. Use the verified
subtraction predicate above or `Finsupp.weight qsPrPairNatWeight e`.

## 9.2 First positive pair layer is strict interior

File:

```text
...PairReesFirstInterior.lean
```

**LEAN VERIFIED:**

```lean
Dpair.firstPositiveLayer_pair_strictInterior_left
  F hthree houtThree hnot
```

for `hnot : not F.NoStrictInteriorSupport`.

Thus every exponent in the first positive actual pair-Rees layer has

```text
1 < e0+e1 < n.
```

Because the reverse Rees parameter is exactly `n-(e0+e1)`, this layer is the
**highest surviving interior pair-degree fibre**.

## 9.3 Source-honest affine layer package

File:

```text
...PairReesFirstInteriorAffineLayer.lean
```

Structure:

```lean
QsOtherFacetPrPairFirstInteriorAffineLayerData F Dpair
```

stores exact integers

```text
k, j,
1<k<n,
0<j<ell,
```

and for every selected source exponent `e`

```text
e0+e1 = k,
e0+e2 = j+1,
V*e0+e3 = V*(k+j),
```

plus literal equality between selected-layer coefficients and source carrier
coefficients.

The constructor is

```lean
QsOtherFacetPrPairFirstInteriorAffineLayerData.
  exists_of_not_noStrictInterior
```

and is **LEAN VERIFIED** at the current green head.

## 9.4 Exact highest zero-layer moment identification

File:

```text
...PairReesHighestMomentRealisation.lean
```

**LEAN VERIFIED:**

```lean
Dpair.zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_left F
```

The zero parameter layer is literally `S.slice`, whose exact support is the
primitive highest binomial. No copied polynomial or extra singularity
assumption is introduced.

The specialised Euler-scaled Hessian is identified with

```lean
highestBinomialMomentHessian V n c d,
```

where

```text
c = coeff highest.e0 S.slice,
d = coeff highest.e1 S.slice,
```

and both are nonzero by actual support provenance.

## 9.5 Exact first positive moment identification

File:

```text
...PairReesFirstInteriorMomentRealisation.lean
```

The module builds a canonical source exponent over every supported profile
index, proves coordinate-zero injectivity, constructs

```lean
A.affineLineData
```

and proves

```lean
A.affineLineData_polynomial_eq_layer.
```

Its final **LEAN VERIFIED** theorem is

```lean
A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
```

identifying the first positive pair-Rees layer with

```lean
parallelStaircaseMomentHessian V A.k A.j A.coefficientProfile.
```

## 9.6 Highest-end first variation

State-free algebra owner:

```text
HC4/Polynomial/HighestBinomialParallelFirstVariation.lean
```

Generic Rees bridge owner:

```text
HC4/Valuation/PlanarHighestFirstVariationBridge.lean
```

The determinant calculation says that, around the primitive highest binomial
`c+dT`, the first variation against a lower staircase fibre factors as

```text
V(V+1) * [c n + d(n-1) T] * T^2 *
  affineTwoRootEulerOperator(c n, d(n-1), j, phi).
```

Crucially `k` cancels from this boundary equation, dual to the way `j`
cancels from the locked-end equation.

Current assembly-facing owner:

```text
...PairReesFirstVariation.lean
```

**LEAN VERIFIED** theorem:

```lean
Dpair.exists_firstPositiveLayer_highestEulerEquation_left
  F hthree houtThree hnot
```

returns an actual

```lean
A : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dpair
```

with

```text
1 < A.k < n,
0 < A.j < ell,
```

and

```lean
affineTwoRootEulerOperator
  (c*n)
  (d*(n-1))
  A.j
  A.coefficientProfile = 0.
```

There is also an equivalent helper theorem in

```text
...PairReesHighestFirstVariation.lean
```

named

```lean
F.exists_pairReesFirstInterior_dualEuler.
```

**Do not build two future proof stacks on these equivalent interfaces.** Use
`...PairReesFirstVariation.lean` as the assembly-facing owner because it also
packages the strict inequalities explicitly. The other theorem may remain as
an internal/helper equivalence.

---

# 10. What the two endpoint equations do — and do not — prove

Under

```lean
hnot : not F.NoStrictInteriorSupport,
```

we now have two honest extremal interior fibres:

```text
A_low  = first surviving interior fibre from the locked/contact side;
A_high = highest surviving interior fibre from the primitive-highest side.
```

They satisfy dual adjacent-root equations:

```text
LOW:
  L_low(phi_low) = 0
  with roots k_low-1, k_low.

HIGH:
  L_high(phi_high) = 0
  with roots j_high, j_high+1.
```

This is a major narrowing, but it is not yet a contradiction.

Why not:

1. the two equations can apply to **different** interior fibres when more than
   one staircase fibre survives;
2. an affine two-root Euler equation has genuine nonzero higher-degree
   solutions before translation;
3. even after translation the adjacent two-mode normal form is not, by itself,
   a source-support contradiction;
4. bare singular staircase families have developable examples.

Therefore the remaining theorem must use **coupling between staircase fibres**
(or an equivalent full Hessian/contact argument), not another isolated
first-variation statement.

---

# 11. Finite staircase arithmetic — the key simplification

The support wall equation is

```text
(n-1) j = ell (n-k).
```

Let

```text
g  = gcd(n-1, ell),
N0 = (n-1)/g,
L0 = ell/g.
```

Since `gcd(N0,L0)=1`, every integral staircase fibre lies at

```text
k_t = 1 + t*N0,
j_t = ell - t*L0,
```

for an integer

```text
0 <= t <= g.
```

Equivalently, indexing from the highest end gives

```text
k = n - s*N0,
j = s*L0.
```

Endpoints:

```text
t=0 -> (k,j)=(1,ell)      locked;
t=g -> (k,j)=(n,0)        highest.
```

Thus there are at most `g-1` possible strict-interior fibres. This is a
**finite one-parameter staircase**, not an arbitrary 2D set of fibres.

Status of this explicit gcd parameterisation:

- the wall equation and endpoint bounds are **LEAN VERIFIED**;
- the explicit gcd enumeration above is a straightforward mathematical
  consequence but is not currently the canonical Lean interface;
- formalise it only if it materially simplifies the coupling proof.

A new session should first try to use the existing `(k,j)` wall equation
without introducing gcd machinery. Add the gcd index only if an induction over
all possible fibres becomes cleaner with it.

---

# 12. The one genuinely OPEN local theorem: finite-staircase coupling

The goal is to prove

```lean
F.NoStrictInteriorSupport
```

by contradiction from `hnot`.

The proof now has enough boundary data. What is missing is a theorem coupling
one occupied interior fibre to the next occupied fibre or to the opposite
endpoint.

There are two honest ways to do this. Route A is preferred.

---

# 13. Preferred Route A — endpoint-sensitive determinant recurrence

## A1. Package the highest-end translated two-mode form

This should be a small adapter, not new mathematics.

The generic affine-two-root rigidity infrastructure already turns an equation

```text
affineTwoRootEulerOperator A B j phi = 0
```

with nonzero affine coefficients into adjacent modes after translation to the
root of `A+B*T`.

Mirror

```text
...PlanarInteriorTwoModeNormalForm.lean
```

for the pair-Rees `A_high` returned by

```lean
Dpair.exists_firstPositiveLayer_highestEulerEquation_left.
```

Expected conclusion, schematically:

```text
translate beta A_high.coefficientProfile
  = p X^(A_high.j) + q X^(A_high.j+1),
```

with `p != 0 or q != 0`, where

```text
beta = -(c*n)/(d*(n-1)).
```

This is mostly interface symmetry and should be a small commit.

Do not mistake it for the final contradiction.

## A2. Give the finite staircase a single canonical fibre interface

Avoid creating another carrier package. Reuse the existing data:

```text
support_staircase_classification;
quotient.pair_fiber;
contact-layer affine packages;
pair-Rees affine package.
```

What the next algebra wants is a way to refer to an occupied fibre by its
`(k,j)` pair and its honest coefficient profile.

A minimal helper theorem is preferable to a new structure, for example:

```lean
same pair degree -> same quotient fibre -> same j.
```

This is already effectively proved inside
`firstPositiveLayer_coordinates_relative`; expose/reuse the smallest generic
version if needed.

## A3. Extract the **next** determinant coefficient, not another first variation

The first positive determinant coefficient at an endpoint gives the affine
Euler equation and has now been exhausted.

The next useful coefficient should couple:

```text
endpoint x next occupied fibre
```

with either

```text
quadratic self-interaction of the outermost interior fibre
```

or

```text
linear interaction with the next occupied staircase fibre.
```

This is the algebraic bridge that the isolated first-variation equations do
not contain.

The recommended strategy is state-free first:

1. define a finite symbolic staircase family of moment Hessians indexed by
   occupied fibres;
2. assume the endpoint binomial and the first one/two interior profile layers;
3. compute the second relevant parameter coefficient of the 4x4 Hessian
   determinant;
4. factor it using the already-known boundary Euler equation;
5. identify the remaining factor as a recurrence from the current extremal
   profile to the next one.

Only after the factorisation is correct should it be adapted to the live A19
packages.

Do not start with a giant dependent-state `ring` proof.

## A4. Use both orientations of the recurrence

The contact Rees naturally strips from the locked end; the pair Rees strips
from the primitive-highest end.

The desired shape is:

```text
lowest occupied interior fibre
  -> recurrence constrains/removes next fibre
  -> ...

highest occupied interior fibre
  -> dual recurrence constrains/removes previous fibre
  -> ...
```

Because the staircase is finite, the two recurrences must meet.

The cleanest possible endpoint theorem would be something like:

```lean
no_nonempty_finite_staircase_of_locked_and_highest_recurrences
```

stated purely for scalar/polynomial profiles, followed by a thin A19 adapter.

If a developable exceptional recurrence survives, isolate it explicitly
rather than hiding it under `ring`.

## A5. Exclude the developable exceptional recurrence using retained contact

Bare Hessian singularity admits developable staircase families. The live A19
branch has additional contact/source data, so any exceptional recurrence must
be tested against:

```text
locked source pair with nonzero coefficients;
primitive highest source pair with nonzero coefficients;
contact-order monotonicity / source bound;
strict pair-degree interior source provenance.
```

The 12 September paper handoff gives the fallback conceptual exclusion:
constant-kernel versus developable form, with the unique top term forcing the
wrong linear factor in the developable branch.

Do not formalise the full external classification unless the specialized
recurrence actually leaves that branch.

## A6. Final local theorem

Once the recurrence theorem is in place, package only:

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.noStrictInterior
    (F : ...)
    (hthree : ...)
    (houtThree : ...) : F.NoStrictInteriorSupport := by
  by_contra hnot
  rcases F.planarContactRees hthree houtThree with <Dcontact>
  rcases F.pairRees hthree houtThree with <Dpair>
  have hlow :=
    Dcontact.exists_firstInteriorAffineLayer_affineTwoRootEulerOperator_eq_zero
      hthree houtThree hnot
  have hhigh :=
    Dpair.exists_firstPositiveLayer_highestEulerEquation_left
      F hthree houtThree hnot
  exact finiteStaircaseContradiction ... hlow hhigh ...
```

Then immediately close with

```lean
F.impossible_of_noStrictInterior
  (F.noStrictInterior hthree houtThree).
```

---

# 14. Useful DIAGNOSTIC evidence for Route A

These are **not Lean theorems** and must remain labelled diagnostic.

## 14.1 Smallest genuine interior case

For the example

```text
n=3, ell=4
```

there is one genuine middle staircase fibre. Writing its profile coefficients
schematically as

```text
p0 + p1 U + p2 U^2
```

and expanding the full source Hessian, the top-boundary coefficient equations
were observed to force successively

```text
D * p2^2 = 0,
D^2 * p1 = 0,
D^2 * p0 = 0,
```

where `D` is the nonzero primitive-highest endpoint coefficient.

Thus the entire interior fibre vanishes in that smallest case.

This strongly suggests the correct general proof is an endpoint-sensitive
triangular recurrence, not a generic profile determinant identity.

## 14.2 Bivariate staircase viewpoint

A symbolic reparameterisation of the whole staircase suggests that the source
Hessian determinant factors schematically as

```text
-V(V+1) U^2 * A(Psi) * B(Psi)
```

for a bivariate staircase polynomial `Psi`.

The locked-end and highest-end affine Euler equations appear as the two
boundary linearisations of the same nonlinear factor `B`.

This is a useful guide for deriving the second-layer recurrence, but the exact
factorisation has not been installed as a Lean theorem and should not be cited
as one.

---

# 15. Route B fallback — specialized no-singleton/developable paper closure

Use this only if the finite recurrence becomes genuinely awkward.

The 12 September paper handoff proves the no-singleton carrier has form

```text
F = x(Q(Y)+b H^ell) + z(P(Y)+a H^ell Y),
Y = y w^V,
H = z w^V,
```

with Hessian determinant

```text
V*ell*(V+1)*w^(V*ell+2V-2)*z^(ell-2) * A * B.
```

For the nondevelopable/two-function branch this gives a characteristic-zero
contradiction.

The singleton/developable escape then uses the retained contact/top-degree
information to rule out a constant kernel or force an impossible linear
factor.

However, formalising the full classification is larger than the endpoint
recurrence route. Prefer a tailored special-case recurrence if possible.

Existing Lean already contains the **post-`NoStrictInteriorSupport`**
two-function contradiction, so do not confuse this paper fallback with
`F.impossible_of_noStrictInterior`, which is already green.

---

# 16. Left `V>1` completion after the open theorem

Once

```lean
F.noStrictInterior hthree houtThree
```

compiles, the left branch should be closed permanently in one thin module.

Recommended theorem:

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.impossible
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) : False := by
  exact F.impossible_of_noStrictInterior
    (F.noStrictInterior hthree houtThree)
```

Do not leak `Dcontact`, `Dpair`, stationary profiles, or moment matrices into
the parent interface.

---

# 17. Right `(V,1)`, `V>1`: symmetry only

The normalized carrier infrastructure already has

```lean
QsOtherFacetPrRightVContactFrontierData
```

and a right-oriented pair-Rees constructor.

Do not duplicate the entire left proof.

Preferred source coordinate permutation:

```text
2 <-> 3,
```

fixing coordinates `0,1`. It sends the right primitive direction

```text
(1,-1,-V,-1)
```

to the left direction

```text
(1,-1,-1,-V).
```

Transport only the data needed to instantiate the left impossibility theorem:

```text
planar carrier and Hessian singularity;
locked source endpoint coefficients and nonvanishing;
highest endpoint coefficients and nonvanishing;
quotient direction;
contact/source weight bound;
V>1.
```

Desired public theorem:

```lean
theorem QsOtherFacetPrRightVContactFrontierData.impossible
    (F : ...)
    (hthree : ...)
    (houtThree : ...) : False := by
  -- coordinate-swap adapter
  -- invoke left theorem
```

If transporting the dependent frontier record is unpleasant, add a small
state-free source permutation theorem and reconstruct the minimal left-facing
record. Do not copy the recurrence algebra.

Status: **OPEN**, expected mostly plumbing once left is closed.

---

# 18. Unit branch `V=1`

Keep this separate from the non-unit proof.

## 18.1 Mixed orientation

Already **LEAN VERIFIED** state-free contradiction:

```text
HC4/Polynomial/TwoFunctionMixedOrientationRigidity.lean
```

```lean
HC4.Polynomial.mixedOrientation_endpoint_coefficients_impossible
```

with hypotheses

```text
B != 0,
C != 0,
2*A*D = B*C,
A*D = 2*B*C.
```

Missing work is source-facing coefficient extraction from the actual unit
carrier Hessian determinant.

Implementation plan:

```text
1. obtain literal endpoint coefficients A,B,C,D from existing source packages;
2. keep the required endpoint nonvanishing from provenance;
3. extract the two extremal determinant coefficients;
4. normalize to
     2AD = BC
     AD = 2BC;
5. invoke mixedOrientation_endpoint_coefficients_impossible.
```

## 18.2 Same orientation

Use the existing two-function determinant factorisation or a tiny `V=1`
specialisation of it. Do not build another carrier classification.

Status of the source-facing unit wrappers: **OPEN**.

---

# 19. Close `.pr`, then `.sp` / `.rq`

After left non-unit, right non-unit, and unit branches are impossible, package
one `.pr` theorem at the highest source-honest level possible.

The normalized split already has the semantic form

```text
(1,1)
or
exists V>1, (1,V) or (V,1).
```

Desired `.pr` wrapper:

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_impossible ... : False
```

using the existing

```lean
S.pr_normalizedCarrier_frontier
S.pr_leftV_contactFrontier
S.pr_rightV_contactFrontier.
```

Handle any singleton-highest-slice constructor through its existing source
branch; do not assume nontriviality unless the constructor gives it.

For `.sp` and `.rq`, reuse cyclic relabelling rather than cloning the planar
proof. Existing active permutations include

```lean
qsPrSuperfaceSchurPermutation
qsSpSuperfaceSchurPermutation
qsRqSuperfaceSchurPermutation.
```

Preferred architecture:

```text
rank-three endpoint on .sp/.rq
    -> cyclic source/toric relabel
    -> .pr source package
    -> .pr_impossible.
```

Status: **OPEN**.

---

# 20. Upward splice after other-facet contradiction

Once all different-facet rank-three endpoints are impossible, inspect and
splice upward in this order:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetReduction
AdaptiveAlignedSmithCanonicalZeroStrictLowQsReducedLowerFrontier
AdaptiveAlignedSmithCanonicalZeroStrictLowCrossFacetBoundaryTransition
AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeBoundaryReduction
AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalResidualReduction
AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction
AdaptiveAlignedSmithCanonicalReachableHC4Reduction
AdaptiveAlignedSmithCanonicalHC4Reduction
HC4.lean
```

The exact reverse importer may have moved, so after the local theorem compiles,
search current imports rather than editing all of these blindly.

At each step eliminate only the constructor actually contradicted. Do not
silently erase:

```text
start-codimension-two;
quadratic-square;
confined-support;
geometry-backed successor;
```

without invoking their dedicated existing consumers.

The A19.55 codimension-two constructor should now route through

```lean
exposedCodimensionTwo_resolvedRankTwoGeometry
```

rather than through generic JC2.

---

# 21. Public theorem target

Current unrestricted reducer:

```lean
gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
```

still takes the presented-terminal impossibility resolver as an argument.

The final public closure should internally supply that resolver and expose a
theorem of the semantic form

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

Use the repository's final preferred theorem name, but do not leave a resolver
argument in the public HC4 result.

---

# 22. File ownership map — avoid duplicate infrastructure

## Global entry / termination

```text
AdaptiveAlignedSmithCanonicalHC4Reduction.lean
AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean
AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean
AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean
```

## A19.55 codimension-two

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoFinalGeometry.lean
FirstKernelBreakRankTwo.lean
FourOrdinaryReverseRees.lean
...TopKernelLinearPowerFirstBreak.lean
```

## Other-facet planar source

```text
...OtherFacetPlanarCarrier.lean
...OtherFacetPlanarHighestPairSlice.lean
...PrVGreaterOneContactFrontier.lean
...PrVGreaterOneStaircaseClassification.lean
```

## Locked-end interior

```text
...PlanarContactRees.lean
...PlanarInteriorAffineLayer.lean
...PlanarInteriorMomentRealisation.lean
...PlanarInteriorFirstVariation.lean
...PlanarInteriorTwoModeNormalForm.lean
PlanarContactFirstVariationBridge.lean
```

## Highest-end interior

```text
...PairRees.lean
...PairReesFirstInterior.lean
...PairReesFirstInteriorAffineLayer.lean
...PairReesHighestMomentRealisation.lean
...PairReesFirstInteriorMomentRealisation.lean
...PairReesFirstVariation.lean
HighestBinomialParallelFirstVariation.lean
PlanarHighestFirstVariationBridge.lean
```

## Post-interior contradiction

```text
...PrVGreaterOneNoInteriorSupport.lean
...PrVGreaterOneFourTermCarrier.lean
...PrVGreaterOneTwoFunctionReconstruction.lean
HC4/Polynomial/TwoFunctionCarrierHessianRigidity.lean
HC4/Polynomial/TwoFunctionCarrierMonomialNormalForm.lean
```

## Historical/prohibition stationary route

```text
...PlanarContactStationary*.lean
HC4/Polynomial/StationaryDeterminantComparisonObstruction.lean
```

Do not add competing owners for any of these concepts.

---

# 23. Exact new-context prompt

A new context can start with this:

```text
Continue the unrestricted HC4 final closure from
`docs/HANDOFF_2026-09-15_HC4_PAIR_REES_FINAL_CLOSURE.md`
on PR #34, branch `final-assembly/a18-4-42-termination-frontier`.

The authoritative green checkpoint is
`e121f5c206443ff6345b00c2bf2a8b581ae1c831`; Lean CI #2318 succeeded.
Re-audit the current PR head first in case inventory/docs commits moved it.

Do not revive the generic stationary source/profile determinant implication:
`StationaryDeterminantComparisonObstruction.lean` proves that route false.
Do not collapse the strict-low branch to generic JC2, do not identify
auxiliary Rees clocks with the zero blocker, and do not add another global
recursion.

The live left (1,V), V>1 branch now has BOTH source-honest endpoint equations
LEAN VERIFIED:

1. contact/locked side:
   `Dcontact.exists_firstInteriorAffineLayer_affineTwoRootEulerOperator_eq_zero`
   plus the translated two-mode normal form;

2. pair/highest side:
   `Dpair.exists_firstPositiveLayer_highestEulerEquation_left`
   with exact highest-binomial and first-interior moment realizations.

The single mathematical obligation is now the finite-staircase coupling that
forces

    F.NoStrictInteriorSupport.

Once that is proved, `F.impossible_of_noStrictInterior` is already Lean
verified and closes the left V>1 branch immediately.

Preferred next work:
- add the small highest-end translated two-mode adapter;
- derive the next endpoint-sensitive determinant coefficient / staircase
  recurrence state-free;
- use the finite wall relation `(n-1)j = ell(n-k)` and both endpoint
  recurrences to eliminate every interior fibre;
- package `F.noStrictInterior` and then `F.impossible`;
- only then do right (V,1) by coordinate-swap symmetry, V=1 source wrappers,
  cyclic .sp/.rq relabelling, and the existing A19/global splice.

Throughout, distinguish LEAN VERIFIED, SOURCE-LANDED, PAPER CANDIDATE,
DIAGNOSTIC ONLY, and OPEN claims.
```

---

# 24. Recent Lean plumbing lessons — avoid repeating them

The pair-Rees route is now green, but several trivial elaboration errors cost
CI cycles. Preserve these fixes.

## 24.1 Special-fibre level rewrite

When the target already contains `(n : Z)` and the stored theorem is

```text
S.pairLevel = n,
```

the special-fibre proof needs the rewrite in the direction matching the
initial-form theorem. Do not blindly `rw [hlevel]`; inspect the target first.

## 24.2 Use packaged bounds

For `n>=2`, use

```lean
F.highest.n_two_le
```

rather than unfolding the whole highest record and asking `omega` to discover
it.

## 24.3 Exact pair-Rees layer support

Canonical theorem:

```lean
Dpair.parameterLayer_support q
```

with predicate

```text
n - (e0+e1) = q.
```

Do not apply `qsPrPairNatWeight` directly to a Finsupp exponent.

## 24.4 Structure projections and arithmetic tactics

If `F.V_gt_one : 1 < F.V` is already stored, derive

```lean
have hVpos : 0 < F.V := lt_trans Nat.zero_lt_one F.V_gt_one
```

instead of asking an isolated inline `omega` to inspect the structure.

## 24.5 Avoid giant dependent-state automation

Normalize to local scalar/polynomial variables before `ring`, `nlinarith`, or
large `simp`. Keep source-state extraction in tiny helpers and the algebra in
state-free lemmas.

---

# 25. Suggested commit sequence from the current green head

Keep each mathematical seam independently compilable.

## Commit A — highest-end translated normal form

Mirror the locked-side two-mode translation for the pair-Rees highest-end
profile.

Acceptance:

```text
actual pair-Rees profile + dual Euler equation
  -> translated support in {j,j+1}, nonzero.
```

## Commit B — generic finite-staircase / adjacent-fibre interface

Expose only the minimal arithmetic/fibre identity required by the recurrence.
Do not add a second carrier package.

Possible contents:

```text
wall relation helper;
same-pair-degree -> same j;
optional gcd staircase enumeration if genuinely useful.
```

## Commit C — state-free second determinant coefficient

Compute/factor the next endpoint-sensitive determinant coefficient for a
binomial endpoint plus the first one/two staircase profiles.

Acceptance: a clear recurrence theorem, no A19 state objects.

## Commit D — source-honest recurrence adapter

Feed the actual contact/pair Rees layers into Commit C.

Acceptance: under `not NoStrictInteriorSupport`, the extremal interior fibre
forces a precise next-fibre/developable alternative.

## Commit E — finite staircase contradiction

Iterate/dualize the recurrence across the finite staircase and kill any
remaining developable exception with the retained contact data.

Output:

```lean
F.noStrictInterior hthree houtThree : F.NoStrictInteriorSupport.
```

## Commit F — left `V>1` contradiction

One-line consumer:

```lean
F.impossible_of_noStrictInterior (F.noStrictInterior ...).
```

## Commit G — right `V>1` symmetry

Coordinate swap only. No duplicate recurrence stack.

## Commit H — `V=1`

Source-facing endpoint coefficient extraction and existing mixed/same
orientation algebra.

## Commit I — `.pr` closure

Consume unit/left/right normalized-carrier alternatives.

## Commit J — cyclic `.sp`/`.rq`

One relabelling layer into `.pr`.

## Commit K — A19/terminal splice

Use existing codimension-two rank-two geometry consumers and eliminate the
other-facet constructor.

## Commit L — public unrestricted HC4 theorem

Supply the terminal resolver internally, compile `HC4.lean`, then run all
proof/axiom audits.

Only after Commit L is green should status docs or the PR description say
unrestricted HC4 is Lean verified.

---

# 26. Final acceptance checklist

Local left branch:

```text
[x] staircase classification
[x] locked endpoint/source provenance
[x] primitive highest endpoint/source provenance
[x] contact-oriented singular family
[x] locked-end affine first variation
[x] locked-end translated two-mode normal form
[x] pair-degree reverse singular family
[x] first positive pair layer strict interior
[x] pair-layer affine source package
[x] highest zero-layer moment realization
[x] first positive pair-layer moment realization
[x] highest-end affine first variation
[ ] finite staircase coupling / recurrence
[ ] F.NoStrictInteriorSupport
[x] support equality after NoStrictInteriorSupport
[x] exact two-function reconstruction after NoStrictInteriorSupport
[x] contradiction after NoStrictInteriorSupport
[ ] parent-facing left V>1 impossible theorem
```

Other rank-three cases:

```text
[ ] right (V,1), V>1 by symmetry
[ ] V=1 mixed orientation source coefficient extraction
[ ] V=1 same orientation wrapper
[ ] .pr normalized carrier impossible
[ ] .sp cyclic relabel to .pr
[ ] .rq cyclic relabel to .pr
```

A19/global:

```text
[x] A19.55 codimension-two -> explicit rank-two geometry
[x] later lower .qs outside codimension-two elimination
[x] lower boundary compression to actual other-facet rank-three endpoint
[ ] consume rank-three other-facet impossibility
[ ] route every sibling local constructor through existing consumer
[ ] prove presented-terminal impossibility without external hypothesis
[ ] feed it to unrestricted HC4 reduction
[ ] expose public determinant-one gradient injectivity theorem
[ ] full root build
[ ] axiom audit
[ ] no sorry/admit/native_decide/unsafe escape-hatch audit
```

---

# 27. Claim level at this checkpoint

The correct claim is:

> The unrestricted HC4 project has a green Lean implementation of the global
> entry/termination architecture, the A19.55 codimension-two geometry branch,
> the rank-three planar/source/staircase infrastructure, and **both honest
> endpoint first-variation equations** for the remaining left non-unit `.pr`
> staircase. The downstream two-function contradiction is also already Lean
> verified once strict-interior support is eliminated. The principal remaining
> local mathematical gap is the finite-staircase coupling theorem proving
> `NoStrictInteriorSupport`; after that remain symmetry/unit/facet wrappers and
> the final existing-architecture splice.

That is genuinely very close, but it is not yet unrestricted HC4.

The important strategic point is that we are no longer searching for the
right global mechanism. We have reached a small, explicit, finite local
algebra problem between two already-verified boundary equations. Close that
problem first; everything else should be assembly and symmetry rather than a
new theory.
