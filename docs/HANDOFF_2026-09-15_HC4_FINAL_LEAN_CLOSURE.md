# HC4 final Lean closure handoff — 15 September 2026

> **Purpose.** This is the implementation-grade handoff for the final unrestricted
> HC4 sprint on PR #34. It supersedes the 12 September TODO lists for deciding
> what to implement next. Older paper documents remain mathematical references,
> but several stages they call `PAPER CANDIDATE` have since been formalised or
> replaced by a shorter stationary Schur/profile route.
>
> **Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`
>
> **Branch:** `final-assembly/a18-4-42-termination-frontier`
>
> **Green substantive checkpoint:** `e330a1ef806c95df03fc3ecf8240da0dd711bcc8`
> (`Identify stationary Hessian determinant with staircase residual`), followed
> by generated-inventory bot head `63ad436ba8525c3a3677e6d585ecaab75c5cfa97`.
> The user reports the current exact checkout is green locally. The bot-head
> GitHub run is `action_required` with no jobs and is not evidence of a Lean
> failure.

---

## 0. Status language and non-negotiable rules

Use these labels literally.

- **LEAN VERIFIED** means the declaration is present in the current source and
  has compiled on the current local green checkout.
- **SOURCE-LANDED / NOT LEAN VERIFIED** means source has been committed but no
  successful exact-head Lean build is known yet.
- **PAPER CANDIDATE** means a complete paper argument exists but it is not the
  current Lean theorem.
- **OPEN** means a genuine missing mathematical/formal interface remains.

Do **not** claim unrestricted HC4 until the public determinant-one gradient
injectivity theorem itself compiles without a caller-supplied resolver,
terminal-impossibility hypothesis, JC2 hypothesis, balance hypothesis,
homogeneity hypothesis, or hidden repair-only contradiction.

The following architectural rules remain binding:

1. Do not identify an auxiliary Rees/ramification clock with the zero blocker
   unless an explicit theorem proves the equality.
2. Do not treat naked `withRepairOnly` progress as a contradiction.
3. Do not infer singularity of a larger carrier/superface from singularity of
   a smaller face or ray.
4. Do not collapse the actual A19 strict-low source/contact/ray branch to
   generic JC2 prematurely.
5. Do not use the old four-monomial cross-ratio equation as a contradiction by
   itself.
6. Do not conflate the old A19.55 same-carrier/top-face codimension-two branch
   with the later A19.91 lower `.qs` outside-endpoint codimension-two branch.
7. Do not add a second global/rank-one recursion. The existing raw-defect
   recursion is the termination mechanism.
8. Do not attach rank-two progress before producing actual rank-two Hessian or
   Schur geometry.
9. Do not reintroduce the false shortcut

   ```text
   first variation + staircase arithmetic -> degree <= 1.
   ```

   `docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md` gives the exact
   counterexample

   ```text
   V=2, ell=4, n=3, k=2, j=2,
   phi(T)=(5+4T)^2.
   ```

   The stronger full stationary/profile Hessian residual is essential.

---

# 1. Executive summary: what is actually left

The proof is no longer missing a broad HC4 mechanism. The global entry,
normalisation, zero-defect/restart architecture, rank-one termination, terminal
source retention, first-contact machinery, lower `.qs` codimension-two
elimination, planar-carrier construction, highest-pair source provenance,
stationary ramification, source-first Schur cancellation, profile Hessian
algebra, and final profile contradiction are already in the repository.

The live local chain is now:

```text
actual singular left (1,V), V>1 stationary ramified source
        |
        | LEAN VERIFIED
        v
source-first Euler-scaled 2+2 Schur block
        |
        | LEAN VERIFIED
        v
pair-weighted Euler shear, nonzero active pivot
        |
        | LEAN VERIFIED
        v
source-first active-pivot cancellation
        |
        | LEAN VERIFIED
        v
stationaryPairWeightedEulerShear.determinantCore = 0
        |
        | OPEN: corrected Schur/profile determinant identification
        v
stationaryProfileHessianDetFamily = 0
        |
        | OPEN: exact quadratic parameter-layer extraction
        v
F.stationaryIntegralProfileHessianDet = 0
        |
        | LEAN VERIFIED consumer
        v
False
```

After that left `V>1` contradiction there are three assembly jobs:

```text
right (V,1), V>1  -- one symmetry/coordinate-swap wrapper
unit V=1          -- source-facing endpoint equations / same-orientation wrapper
other facets      -- reuse cyclic symmetry instead of rebuilding the proof
```

Then the contradiction is spliced upward through the already-existing
strict-low boundary/terminal path to the unrestricted public HC4 theorem.

**The next theorem to implement remains**

```lean
theorem QsOtherFacetPrLeftVPlanarContactReesData.stationaryIntegralProfileHessianDet_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.stationaryIntegralProfileHessianDet = 0 := by
  ...
```

but it should be implemented in two internal stages rather than as one giant
proof:

1. source/sheared determinant -> `stationaryProfileHessianDetFamily = 0`;
2. stationary family determinant -> canonical integral profile determinant.

Once those compile, the left `V>1` endpoint becomes a one-line contradiction.

---

# 2. What the old 12 September plan got superseded by

The following documents remain useful references but are **not** the current
TODO list:

- `docs/HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md`
- `docs/FORMALISATION_PLAN_2026-09-12.md`
- `docs/CURRENT_STATE.md`
- `docs/LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

The 12 September plan proposed, among other things, implementing
`FirstKernelBreakRankTwo.lean`, `FourOrdinaryReverseRees.lean`, and a large
paper rank-three carrier classification. In the current tree:

- `HC4/Valuation/FirstKernelBreakRankTwo.lean` exists and contains the exact
  first-kernel-break determinant linearisation and explicit nonzero principal
  `2 x 2` minor conclusion.
- `HC4/Valuation/FourOrdinaryReverseRees.lean` exists and contains the honest
  reverse-Rees family, exact layers, evaluation at one, source inflation, and
  exact Hessian defect clock `4 * (D - 2)`.
- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoElimination`
  proves the later A19.91 lower `.qs` outside endpoint cannot be codimension
  two.
- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetReduction`
  compresses that lower boundary to an actual rank-three outside endpoint on a
  different facet.
- the rank-three `.pr`, `V>1` branch has moved to a source-honest stationary
  Schur/profile construction that is shorter than formalising the complete
  paper no-singleton/developable classification.

Therefore:

> **Do not restart the old codimension-two programme and do not formalise the
> de Bondt--van den Essen classification merely because the 12 September docs
> call those things future work.**

The old paper route is now a fallback for a concrete failure of the stationary
adapter, not the primary implementation route.

---

# 3. The current lower-boundary location in the Lean DAG

The existing lower `.qs` compression is already precise.

`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetReduction.lean`
proves

```lean
C.qs_ray_boundaryOutcome_otherFacet
```

and removes the far codimension-two endpoint under a rank-three `.qs` start.

`AdaptiveAlignedSmithCanonicalZeroStrictLowQsReducedLowerFrontier.lean` then
proves

```lean
T.qs_rankThree_startCodimensionTwo_or_otherFacet_or_quadraticSquare
```

with three honest outcomes:

```text
1. lower ray starts codimension two;
2. lower ray starts rank three on .qs and its actual outside endpoint is
   rank three on a different facet;
3. literal coordinate-zero quadratic square.
```

The current stationary work is closing the **second** constructor. Do not
silently assume this also closes constructor 1 or the quadratic-square branch;
those have their own existing consumers and must be checked at the final
assembly splice.

`AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeBoundaryReduction.lean`
is an earlier, more general rank-three boundary-transition interface. Preserve
its provenance discipline: the lower first-contact carrier stays attached to
that lower carrier and is not transported back to the maximal top face.

---

# 4. Current left `V>1` notation dictionary

For the remainder of this handoff fix

```lean
C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs
P : QsOtherFacetPlanarCarrierPackage C .pr
S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P
R : QsOtherFacetContactQuadraticReesPackage C
F : QsOtherFacetPrLeftVContactFrontierData C P S R
D : QsOtherFacetPrLeftVPlanarContactReesData F
```

and

```lean
hthree    : MvRankThreeOnFacet .qs C.ray.facetExponent
houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent
```

Use the following symbols mentally:

```text
n   := F.highest.n
ell := F.locked.ell
V   := F.V
r   := F.stationaryWeight
Dt  := F.stationaryTotalDegree
m(e):= n - (e 0 + e 1)
q(e):= Dt - r * m(e)
```

The actual Lean definitions are:

```lean
F.stationaryWeight =
  (F.V + 1) * (F.locked.ell + 1 - F.highest.n)

F.stationaryTotalDegree =
  F.stationaryWeight * (F.highest.n - 1)
```

Do **not** simplify `stationaryWeight` to `V+1`: there is an additional
positive contact-gap factor

```text
ell + 1 - n.
```

Existing theorems give

```lean
F.stationaryWeight_pos hthree houtThree
F.two_le_stationaryWeight hthree houtThree
F.highest.n_two_le
F.highest_n_lt_locked_height hthree houtThree
```

For an actual carrier monomial the ramified parameter order is exactly

```text
q(e) = Dt - r*m(e) = r*((e0+e1)-1).
```

The relevant existing declarations are

```lean
D.stationary_scaledOrder_eq_of_carrier_mem
D.stationary_order_eq_weight_mul_pair_pred
D.stationary_order_add_weight_eq_weight_mul_pair
D.coeff_stationaryRamifiedFamily_of_carrier_mem
D.stationaryRamifiedFamily_parameterLayer_coeff
D.stationaryRamifiedFamily_parameterLayer_support
```

This exact-order information is the key to making the final determinant
extraction mechanical.

---

# 5. LEAN VERIFIED stationary stack

## 5.1 Source-honest stationary profile

File:

```text
...PlanarContactStationaryProfile.lean
```

The nested profile is

```lean
F.stationaryCarrierProfile : Polynomial (Polynomial K)
```

where the outer index is

```text
m = n - (e0+e1)
```

and the inner index is `e0`. Thus this is not a recreated abstract profile: it
is a literal finite regrouping of coefficients of `P.carrier`.

Use:

```lean
F.coeff_stationaryCarrierProfile
F.natDegree_stationaryCarrierProfile_le hthree houtThree
```

and endpoint facts from `...StationaryProfileEndpoints.lean`:

```lean
F.coeff_coeff_stationaryCarrierProfile_of_mem
F.stationaryCarrierProfile_coeff_zero_ne_zero hthree houtThree
F.stationaryCarrierProfile_coeff_top_ne_zero hthree houtThree
```

The exact degree theorem is later exposed in `...StationaryRigidity.lean`:

```lean
F.stationaryCarrierProfile_natDegree_eq hthree houtThree
```

with value `n-1`.

## 5.2 Honest stationary ramification

File:

```text
...PlanarContactStationaryRamification.lean
```

Definition:

```lean
D.stationaryRamifiedFamily :=
  parameterRamificationFamily (F.highest.n - 1) D.family
```

Important theorems:

```lean
D.stationaryRamifiedFamily_hessianDeterminant_eq_zero
D.stationary_scaledOrder_eq_of_carrier_mem
D.coeff_stationaryRamifiedFamily_of_carrier_mem
D.stationaryRamifiedFamily_parameterLayer_coeff
D.stationaryRamifiedFamily_parameterLayer_support
```

The last theorem was added specifically for the final determinant extraction.
It says exact parameter layers have no hidden support: they are literally the
carrier support filtered by `q(e)=q`.

## 5.3 Weighted Euler equation

File:

```text
...PlanarContactStationaryWeightedEuler.lean
```

The exact whole-family identity is

```text
E_tau Q + r Q = r E_0 Q + r E_1 Q.
```

Lean theorem:

```lean
D.stationaryRamifiedFamily_weightedEuler hthree houtThree
```

This equation is the origin of the important diagonal correction discussed
below.

## 5.4 Two affine carrier Euler equations and Hessian rows

Files:

```text
...PlanarContactStationaryCarrierEuler.lean
...PlanarContactStationaryCarrierEulerHessian.lean
```

On actual support the two affine equations are, schematically,

```text
((n-1)+ell)e0 + ell e1 + (n-1)e2 = (n-1) + ell*n
V(e0+e1+e2) = V + e3.
```

Use the whole-family first-order identities in `StationaryCarrierEuler` and the
second-order/falling rows

```lean
D.stationaryRamifiedFamily_wallEulerRow hthree houtThree i
D.stationaryRamifiedFamily_curveEulerRow hthree houtThree i
```

when converting source Hessian directions. These falling rows are safer than
trying to turn affine support equations into naive linear relations between
Hessian entries by hand.

## 5.5 Parameter/depth profile Hessian family

File:

```text
...PlanarContactStationaryProfileHessianFamily.lean
```

Definitions:

```lean
D.stationaryDepthEuler Q
D.stationaryDepthSecondEuler Q
D.stationaryProfileHessian00Family
D.stationaryProfileHessian01Family
D.stationaryProfileHessian11Family
D.stationaryProfileHessianDetFamily
```

with the intended meanings

```text
M        = n - E0 - E1
H00      = E_tau(E_tau-1) Q
H01      = E_tau M Q
H11      = M(M-1) Q
profileDet = H00*H11 - H01^2.
```

## 5.6 Exact source coefficients of those three entries

File:

```text
...PlanarContactStationaryProfileHessianCoefficients.lean
```

For actual carrier exponent `e`, depth `m=n-(e0+e1)`, and stationary order
`q=Dt-rm`, the exact factors are

```text
H00[e] = q(q-1) * Q[e]
H01[e] = q*m    * Q[e]
H11[e] = m(m-1)* Q[e].
```

Use the existing theorem names:

```lean
D.stationaryProfileHessian00Family_coeff_of_carrier_mem
D.stationaryProfileHessian01Family_coeff_of_carrier_mem
D.stationaryProfileHessian11Family_coeff
```

Do not rewrite these factors from scratch inside the determinant extraction.

## 5.7 Profile Euler reductions

File:

```text
...PlanarContactStationaryProfileHessianEulerReduction.lean
```

Important declarations include

```lean
D.stationaryRamifiedFamily_parameterDepthWeightedEuler
D.stationaryProfileHessian_depthRow
D.stationaryProfileHessian_parameterRow
D.stationaryProfileHessianDetFamily_eq_euler_reduction
```

and the existing depth-reduction theorem in the same module.

The source equation is

```text
E_tau Q + r M Q = Dt Q.
```

The falling Hessian rows are

```text
H00 + r H01 = (Dt-1) E_tau Q
H01 + r H11 = (Dt-r) M Q.
```

These are likely the cleanest algebraic normal form for the final comparison
because they already contain the falling diagonal corrections.

## 5.8 Source-coordinate representations of parameter and depth

File:

```text
...PlanarContactStationaryCoordinateEuler.lean
```

Theorems:

```lean
D.stationaryRamifiedFamily_parameterActiveEuler hthree houtThree
D.stationaryRamifiedFamily_depthActiveEuler hthree houtThree
```

Mathematically:

```text
V E_tau Q = r (E3 - V E2) Q,
ell V M Q = (n-1) (E3 - V E1) Q.
```

These are denominator-free. They are exactly the bridge from the abstract
parameter/depth Hessian to the actual active `(2,3)` source block.

## 5.9 Falling parameter correction

File:

```text
...PlanarContactStationaryParameterEulerHessian.lean
```

Use

```lean
familyParameterEuler_familyParameterEuler
D.stationaryRamifiedFamily_fallingParameterRow hthree houtThree
```

The latter is the formal statement that differentiating the weighted Euler
identity introduces the extra first-Euler term required by a falling Hessian.

## 5.10 Euler-scaled source Schur block

File:

```text
...PlanarContactStationaryEulerSchur.lean
```

The active `.pr` pair is source coordinates `(2,3)`. Under
`qsPrSuperfaceSchurPermutation`, the four-block order is

```text
(2,3 | 0,1).
```

Definitions:

```lean
D.stationaryEulerHessianFourBlock
D.stationaryPairWeightedEulerShear
```

where the second complement is sheared to

```text
r E1 + r E0 = r(E0+E1).
```

Verified zero-Schur facts:

```lean
D.stationaryEulerHessianFourBlock_schurDetCore_eq_zero
D.stationaryPairWeightedEulerShear_schurDetCore_eq_zero
D.stationaryPairWeightedEulerShear_activeDet
```

## 5.11 Source-first pivot cancellation

File:

```text
...PlanarContactStationarySchurProfileBridge.lean
```

This is an especially important verified base. It proves

```lean
D.stationaryRamifiedFamily_sourceActiveDet_ne_zero
D.stationaryEulerHessianFourBlock_activeDet_ne_zero
D.stationaryPairWeightedEulerShear_activeDet_ne_zero
D.cancel_stationaryPairWeightedEulerShear_activeDet
D.stationaryPairWeightedEulerShear_determinantCore_eq_zero
```

and then defines/zeros

```lean
D.specialisedStationarySchurDet
D.specialisedStationarySchurDet_eq_zero
D.specialisedStationaryDeterminantCore
D.specialisedStationaryDeterminantCore_eq_zero
```

**Preserve this order of operations.** The genuine source active pivot is
cancelled *before* rank-three line specialisation. A specialisation can kill a
nonzero factor, so do not move pivot cancellation after specialisation.

## 5.12 Canonical integral stationary profile Hessian

File:

```text
...PlanarContactStationaryIntegralProfileHessian.lean
```

Definitions:

```lean
F.stationaryIntegralProfileSecondEuler
F.stationaryIntegralProfileHessian00
F.stationaryIntegralProfileHessian01
F.stationaryIntegralProfileHessian11
F.stationaryIntegralProfileHessianDet
```

Coefficient formulas are already exactly what the final extraction needs:

```text
H00[m] = (Dt-rm)(Dt-rm-1) h[m]
H01[m] = m(Dt-rm) h[m]
H11[m] = m(m-1) h[m].
```

The terminal consumer is already proved:

```lean
F.impossible_of_stationaryIntegralProfileHessianDet
  hthree houtThree
  (hdet : F.stationaryIntegralProfileHessianDet = 0) : False
```

Once `hdet` exists there is no need to run through four-term-carrier or
singleton/developable classification in this branch.

## 5.13 Integral determinant = staircase residual

File added at substantive head `e330a1e...`:

```text
...PlanarContactStationaryResidualBridge.lean
```

Theorems:

```lean
F.stationaryIntegralProfileHessianDet_eq_binaryStaircaseProfileResidual
F.stationaryIntegralProfileHessianDet_eq_zero_iff_residual_eq_zero
```

This is a useful sanity bridge and a second downstream consumer. It does not
prove the geometric vanishing.

`...StationaryRigidity.lean` already proves

```lean
F.noStrictInteriorSupport_of_stationaryResidual
```

from residual zero. That route is now weaker than the direct contradiction
available from `impossible_of_stationaryIntegralProfileHessianDet`; use it only
if it happens to make a later assembly interface easier.

---

# 6. The crucial warning: raw complementary entries are NOT the profile Hessian

Do not attempt a theorem saying the three raw/sheared complementary entries
are literally

```text
H00, H01, H11.
```

That statement is false because the Euler-scaled Hessian uses falling diagonal
operators.

Let

```text
S = r(E0+E1).
```

Weighted Euler gives

```text
S Q = E_tau Q + r Q.
```

For the bilinear Euler-Hessian form `B`, differentiating this identity gives
the corrected diagonal relation

```text
B(S,S) = H_tau_tau + (r+1) E_tau Q,
```

where

```text
H_tau_tau = E_tau(E_tau-1)Q.
```

Equivalently, on a monomial of parameter order `q`, the raw pair shear sees

```text
r^2 k(k-1) = q(q+r),
```

whereas the canonical falling parameter Hessian sees

```text
q(q-1).
```

The difference is exactly the first-Euler correction. This is why
`stationaryRamifiedFamily_fallingParameterRow`, the carrier Hessian rows, and
the profile Euler reductions were added.

A correct final proof must preserve these corrections until the determinant is
formed. Do not “simplify” them away.

---

# 7. Recommended implementation: Route A

Route A is the shortest source-honest path. It avoids formalising the complete
paper classification and avoids a giant direct expansion of the specialised
4x4 determinant.

## A1. Prove the source-level stationary profile determinant vanishes

### Target

Add a theorem close to the source determinant machinery, preferably in
`...StationarySchurProfileBridge.lean` if the import direction remains acyclic,
or in a new thin module such as

```text
...PlanarContactStationaryDeterminantComparison.lean
```

that imports

```text
StationarySchurProfileBridge
StationaryProfileHessianEulerReduction
StationaryCoordinateEuler
StationaryCarrierEulerHessian
```

Target signature:

```lean
theorem QsOtherFacetPrLeftVPlanarContactReesData.stationaryProfileHessianDetFamily_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryProfileHessianDetFamily = 0 := by
  ...
```

### Preferred proof shape

Do not begin by expanding all 17 terms of `GeneralFourBlock.determinantCore`.
First derive corrected linear relations among the sheared complement directions
and the `(E_tau,M)` directions.

The available first-order source identities are

```text
V E_tau = r(E3 - V E2)
ell V M = (n-1)(E3 - V E1)
```

on `Q`.

At Hessian level use the corresponding falling rows, not informal
differentiation. The exact ingredients are:

```lean
D.stationaryRamifiedFamily_wallEulerRow hthree houtThree i
D.stationaryRamifiedFamily_curveEulerRow hthree houtThree i
D.stationaryRamifiedFamily_fallingParameterRow hthree houtThree
D.stationaryProfileHessian_parameterRow hthree houtThree
D.stationaryProfileHessian_depthRow hthree houtThree
```

There are two good ways to finish A1.

### A1a. Explicit scalar-multiple determinant theorem

Prove an equality of the form

```lean
Cscalar * D.stationaryProfileHessianDetFamily =
  Csource * D.stationaryPairWeightedEulerShear.determinantCore
```

where `Cscalar` and `Csource` are explicit ground-field/source monomial factors
coming from the denominator-free coordinate transform. Then use

```lean
D.stationaryPairWeightedEulerShear_determinantCore_eq_zero hthree houtThree
```

and cancel the nonzero scalar.

Do not guess the scalar. Derive it mechanically from the two coordinate-Euler
identities. Expected factors can involve

```text
V, ell, n-1, r
```

and source coordinate monomials already introduced by Euler scaling.

For scalar nonvanishing use existing positivity:

```lean
F.V_gt_one
F.highest.n_two_le
F.stationaryWeight_pos hthree houtThree
F.highest_n_lt_locked_height hthree houtThree
```

and verify the exact positivity theorem for `ell` before relying on it.

### A1b. Row-reduction proof without naming the scalar

This may elaborate more smoothly. Rewrite
`D.stationaryProfileHessianDetFamily` with

```lean
D.stationaryProfileHessianDetFamily_eq_euler_reduction hthree houtThree
```

or the depth-reduction theorem, rewrite `E_tau` and `M` using the two
source-coordinate identities, then use the wall/curve Hessian rows and
`ring`/`linear_combination` to identify the result with a multiple of the
already-zero source determinant core.

This keeps the falling corrections inside already-verified identities and may
avoid constructing a new transformed `GeneralFourBlock` object.

### Acceptance condition for A1

The only assumptions should be the existing `D`, `hthree`, and `houtThree`.
There must be no new degree, coprimality, balance, or nonvanishing hypothesis.
The proof should end with an actual source-family polynomial identity, not a
pointwise heuristic.

---

## A2. Prove the stationary convolution-order lemma

The generic binary extraction already has exactly the pattern we need in

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDeterminantExtraction.lean
```

Do not invent a new extraction architecture. Copy its proof shape and replace
its binary profile order with the stationary order.

The needed arithmetic lemma is essentially:

```lean
theorem stationary_profileOrder_add
    {i j : Nat}
    (hi : F.stationaryCarrierProfile.coeff i != 0)
    (hj : F.stationaryCarrierProfile.coeff j != 0) :
    (Dt - r*i) + (Dt - r*j) =
      2*Dt - r*(i+j) := by
  ...
```

### How to prove the bounds

From

```lean
F.natDegree_stationaryCarrierProfile_le hthree houtThree
```

and `Polynomial.le_natDegree_of_ne_zero hi`, obtain

```text
i <= n-1,
j <= n-1.
```

Since

```text
Dt = r*(n-1),
```

get

```text
r*i <= Dt,
r*j <= Dt.
```

Then

```lean
rw [Nat.mul_add]
omega
```

should discharge the natural-subtraction addition exactly, just as
`binary_profileOrder_add` does.

Put this arithmetic in a named theorem; the convolution proof will need it
for both `H00*H11` and `H01*H01`.

---

## A3. Extract the exact quadratic stationary determinant layer

### Recommended new theorem

Define no new mathematical profile. Work with the existing
`D.stationaryProfileHessianDetFamily` and `F.stationaryIntegralProfileHessianDet`.

Prove an exact coefficient/layer theorem analogous to
`binaryProfileHessianDetFamily_longitudinal_coeff`.

One useful target shape is:

```lean
theorem stationaryProfileHessianDetFamily_parameterLayer_specialisation
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : ...)
    (houtThree : ...)
    (s : Nat) :
    rankThreeLineSpecialisation
      (familyParameterLayer
        D.stationaryProfileHessianDetFamily
        (2 * F.stationaryTotalDegree - F.stationaryWeight * s)) =
      F.stationaryIntegralProfileHessianDet.coeff s := by
  ...
```

If direct line specialisation of the entire source layer is awkward, split it
into the same two stages as the generic binary theorem:

1. move source parameter outermost with `parameterFirstEquiv`;
2. take outer parameter coefficient;
3. apply `Polynomial.map rankThreeLineSpecialisation`;
4. identify the remaining inner one-variable polynomial with the stationary
   profile determinant coefficient.

### Mechanical convolution proof

For the `H00*H11` half:

```lean
rw [Polynomial.coeff_mul]
apply Finset.sum_congr rfl
intro ij hij
```

For every antidiagonal pair `(i,j)`:

- if `stationaryCarrierProfile.coeff i = 0`, the H00 coefficient at `i` is
  zero by the existing canonical coefficient theorem;
- if `stationaryCarrierProfile.coeff j = 0`, the H11 coefficient at `j` is
  zero;
- otherwise use `stationary_profileOrder_add hi hj` to combine
  `X^(Dt-r*i) * X^(Dt-r*j)` into
  `X^(2Dt-r*(i+j))`.

Repeat for `H01*H01`.

Do not rely on an informal claim that the stationary family is globally one
monomial in the parameter. Use the exact source coefficient theorem and
`stationaryRamifiedFamily_parameterLayer_support` so off-carrier terms are
explicitly zero.

### Inner line specialisation

The existing line/family bridge is

```text
...StationaryFamilyBridge.lean
```

with

```lean
A.rankThreeLineSpecialisation_layer_eq_coefficientProfile
D.specialisedParameterFirstFamily_coeff_eq_coefficientProfile
D.specialisedParameterFirstFamily_coeff_eq_stationaryCarrierProfile
```

These theorems are stated for the honest unramified contact layer package.
Ramification changes only the outer parameter order, not the source layer.
If the exact theorem needed for a stationary ramified layer is absent, add a
small adapter:

```lean
stationaryRamifiedFamily_parameterLayer_specialisation_eq_stationaryCarrierProfile_coeff
```

whose proof should:

1. use `stationaryRamifiedFamily_parameterLayer_support` to identify the
   source layer;
2. use the corresponding unramified affine layer package/order from the
   contact interpolation;
3. finish with the existing
   `rankThreeLineSpecialisation_layer_eq_coefficientProfile` and
   `coefficientProfile_eq_stationaryCarrierProfile_coeff`.

Do not reconstruct the affine line from scratch.

---

## A4. Deduce the canonical determinant is zero

Once A1 and A3 exist, this theorem should be short.

For every `s`, the exact determinant-family layer is zero because

```lean
D.stationaryProfileHessianDetFamily_eq_zero hthree houtThree
```

so A3 gives

```text
F.stationaryIntegralProfileHessianDet.coeff s = 0.
```

Then

```lean
apply Polynomial.ext
intro s
rw [Polynomial.coeff_zero]
exact ...
```

This should produce the public adapter:

```lean
theorem QsOtherFacetPrLeftVPlanarContactReesData.stationaryIntegralProfileHessianDet_eq_zero
    ... : F.stationaryIntegralProfileHessianDet = 0 := by
  ...
```

At this point **do not stop to formalise more geometry**.

---

## A5. Close the left `V>1` branch immediately

Add a tiny theorem:

```lean
theorem QsOtherFacetPrLeftVPlanarContactReesData.impossible
    {C ...} {P ...} {S ...} {R ...}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) : False := by
  exact F.impossible_of_stationaryIntegralProfileHessianDet
    hthree houtThree
    (D.stationaryIntegralProfileHessianDet_eq_zero hthree houtThree)
```

Then remove `D` from the parent-facing interface:

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.impossible
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) : False := by
  rcases F.planarContactRees hthree houtThree with ⟨D⟩
  exact D.impossible hthree houtThree
```

`F.planarContactRees hthree houtThree` is already the verified constructor for
`QsOtherFacetPrLeftVPlanarContactReesData F`.

This is the clean theorem boundary that the parent normalized-carrier split
should consume.

---

# 8. Route B fallback: specialised determinant core directly

Use this only if A1's row-reduction proof becomes genuinely harder to
elaborate than expected.

Already verified:

```lean
D.specialisedStationaryDeterminantCore_eq_zero hthree houtThree
```

The fallback is to prove a literal identity in

```text
Polynomial (Polynomial K)
```

between `D.specialisedStationaryDeterminantCore` and a nonzero scalar/source
monomial multiple of `F.stationaryIntegralProfileHessianDet`.

The danger is that `determinantCore` still contains the active block and all
active/complement couplings. A naive direct `ring` expansion will be enormous
and will obscure the diagonal falling-Euler corrections. If this route is
used:

1. map the **four-block entries** through parameter-first + line
   specialisation first;
2. prove corrected formulas for the three complementary entries and six
   couplings using the existing Euler rows;
3. only then unfold `GeneralFourBlock.determinantCore` and call `ring`.

Do not try to identify just the raw x/y/z fields with H00/H01/H11.

Route A should normally be shorter because it works before this unnecessary
4x4 expansion.

---

# 9. Why the old four-term/developable route is now fallback only

The old paper closure remains valid mathematical guidance:

```text
F = x(Q(Y)+bH^ell) + z(P(Y)+aH^ell Y),
Y = y w^V,
H = z w^V
```

with Hessian determinant factorisation

```text
V*ell*(V+1)*w^(V*ell+2V-2)*z^(ell-2) * A * B.
```

The paper argument then forces the two-function branch to contradict
characteristic zero and handles singleton/developable escape from retained
contact data. Likewise
`docs/LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md` gives a complete paper
classification of a singular line-supported slice.

However, in the current Lean tree:

- `NoStrictInteriorSupport` already has a downstream four-term reconstruction;
- the stationary determinant route has a **stronger direct consumer**:
  determinant zero -> `False`;
- formalising the complete developable classification would introduce far
  more machinery than extracting the already-built stationary determinant.

Therefore formalise the old paper route only if a specific obstruction proves
that the stationary family determinant cannot be connected to the integral
profile determinant.

The paper documents remain excellent independent checks on any coefficient
identity derived in A1--A3.

---

# 10. Right orientation `(V,1)`, `V>1`

The normalized carrier split is already exhaustive:

```lean
S.pr_normalizedCarrier_frontier hthree houtThree hnontrivial
```

returns either

```text
(1,1)
```

or, for some `V>1`,

```text
(1,V) OR (V,1).
```

The right structure exists:

```lean
QsOtherFacetPrRightVContactFrontierData
```

and the right geometric chain already contains

```lean
F.quotient_affine_interpolation
F.support_staircase_equations
```

in the right-oriented modules.

The stationary implementation is currently left-named. **Do not duplicate the
whole stationary stack.**

## Preferred implementation

Search first for an existing source-variable permutation/relabeling API. If it
exists, define one thin adapter exchanging source coordinates `2` and `3`.
The permutation fixes `0,1` and sends

```text
(1,-1,-V,-1) -> (1,-1,-1,-V).
```

Transport only the data needed to instantiate the left theorem:

- planar carrier and Hessian singularity;
- locked source endpoints and coefficient nonvanishing;
- highest-pair endpoints and coefficient nonvanishing;
- quotient direction;
- contact Rees/source bound;
- `V>1`.

Then invoke the left `V>1` impossibility theorem.

## If dependent package transport is painful

Do not copy the generic profile/Hessian algebra. Instead make a right-facing
wrapper whose proof uses the same coordinate permutation internally and whose
public signature is

```lean
theorem QsOtherFacetPrRightVContactFrontierData.impossible
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : ...)
    (houtThree : ...) : False := by
  ...
```

At most duplicate the short source-coordinate formulas with indices `2` and
`3` swapped. Never duplicate `stationaryProfileHessianFamily`, determinant
extraction, or profile rigidity.

Acceptance condition: right `V>1` dies by symmetry, not by a second independent
proof stack.

---

# 11. Unit branch `V=1`

Keep this separate from `V>1`.

The paper reference remains section 6.6 of
`docs/FORMALISATION_PLAN_2026-09-12.md` / the 12 September handoff.

There are two unit-orientation behaviours.

## 11.1 Mixed orientation

The state-free final scalar contradiction is already LEAN VERIFIED in

```text
HC4/Polynomial/TwoFunctionMixedOrientationRigidity.lean
```

as

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

So the missing work is source-facing coefficient extraction, not algebra.

### Implementation recipe

1. Find the existing unit normalized-carrier endpoint/source coefficient
   package before adding new structures.
2. Name the four literal endpoint coefficients `A B C D` from the actual
   carrier and obtain nonvanishing from provenance.
3. Use `P.hessian_zero` (or the corresponding actual carrier singularity
   theorem) and extract the two **extremal Hessian determinant coefficients**
   identified by the paper calculation.
4. Normalize those two coefficients with `simp`, `ring`, and exact exponent
   inequalities; derive

   ```text
   2*A*D = B*C
   A*D = 2*B*C.
   ```

5. Finish with

   ```lean
   exact HC4.Polynomial.mixedOrientation_endpoint_coefficients_impossible
     A B C D hB hC h1 h2
   ```

Do not prove a more general classification theorem unless the source-facing
coefficient extraction demonstrably needs it.

## 11.2 Same orientation

The paper says this is killed by the same full two-function determinant
factorisation as the non-unit case. Search existing `TwoFunction...`,
`FourTermCarrier`, and carrier-normal-form modules first. If a source-facing
same-orientation theorem is already present, consume it directly.

If not, prefer a tiny unit specialization of the existing two-function
factorisation over formalising the whole paper classification.

---

# 12. Closing `.pr` itself

After left `V>1`, right `V>1`, and unit `V=1` are all impossible, package one
`.pr` theorem at the highest source-honest level possible.

The natural input is the already-existing planar carrier/highest-slice/contact
frontier chain, not an abstract quotient polynomial.

A desirable theorem shape is

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_impossible
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) : False := by
  rcases S.pr_normalizedCarrier_frontier
      hthree houtThree hnontrivial with hunit | hV
  · -- V=1 theorem
    ...
  · rcases hV with ⟨V, hVgt, hleft | hright⟩
    · rcases S.pr_leftV_contactFrontier R hVgt hleft
          hthree houtThree hnontrivial with ⟨F⟩
      exact F.impossible hthree houtThree
    · rcases S.pr_rightV_contactFrontier R hVgt hright
          hthree houtThree hnontrivial with ⟨F⟩
      exact F.impossible hthree houtThree
```

Use the exact existing argument order of `pr_leftV_contactFrontier` and
`pr_rightV_contactFrontier`; the sketch above is semantic, not guaranteed to
match elaborated implicit-argument order verbatim.

Then connect the nontrivial-highest-slice theorem to the existing
highest-pair-slice constructor. If the highest slice can be singleton, consume
the already-built singleton/source branch rather than assuming
`hnontrivial`.

---

# 13. Cyclic `.sp` / `.rq` closure

The lower `.qs` boundary only tells us the next rank-three facet is different
from `.qs`. Thus the final other-facet theorem must handle `.pr`, `.sp`, and
`.rq`.

The repository already has cyclic active permutations

```lean
qsPrSuperfaceSchurPermutation
qsSpSuperfaceSchurPermutation
qsRqSuperfaceSchurPermutation
```

and generic binary contact machinery was deliberately written cyclically.
Before copying any planar proof, search for existing facet-relabeling or
coordinate-permutation lemmas in the first-nonfacet/other-facet stack.

Preferred architecture:

```text
generic other-facet rank-three source package
        |
        +-- relabel .sp -> .pr
        +-- relabel .rq -> .pr
        |
        v
single .pr impossibility theorem
```

If a fully generic `otherFacet` relabeling already exists, use it. If not, add
a small state-free toric/source permutation adapter once. Do not clone the
stationary profile files three times.

---

# 14. Upward splice after local other-facet contradiction

Once every actual different-facet rank-three endpoint is impossible, revisit
these modules in order:

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

The exact parent may have changed since older handoffs, so inspect imports and
reverse importers after the local theorem compiles rather than editing all
parents speculatively.

At every level, eliminate only the constructor you have genuinely contradicted.
Do not silently erase:

- a start-codimension-two constructor;
- a quadratic-square constructor;
- a confined-support constructor;
- a geometry-backed successor constructor.

Those should already have dedicated consumers elsewhere in the mature A19
stack. The final splice should mostly be `rcases` + existing theorem calls.

The target architecture is

```text
unrestricted counterexample / collision entry
       -> existing canonical normalisation
       -> existing rank-one raw-defect termination trace
       -> zero-clock strict-low terminal
       -> existing exhaustive local frontier
       -> every local constructor eliminated or converted to already-certified
          geometry/progress
       -> contradiction
       -> public determinant-one gradient injectivity.
```

Do not add another global recursion or another public assumption to make the
splice typecheck.

---

# 15. Paper theorem map: what to consult if a Lean seam fails

## 15.1 `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`

Use this as an independent mathematical check on a line-supported slice. It
proves on paper that a nonconstant singular line profile in direction

```text
(1,-1,-alpha,-beta)
```

has degree at most one, using the Euler-scaled Hessian, the rational first
integral `Phi(Z)`, and rational-map degree multiplicativity.

Do **not** formalise this entire theorem first. The stationary Hessian route
already encodes stronger whole-carrier source/contact information.

## 15.2 `HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md`

Use it for:

- defect-neutral planar-refinement provenance;
- highest-slice singularity rationale;
- two-function carrier Hessian factorisation;
- singleton/developable fallback;
- `V=1` extremal coefficient equations.

Several of its implementation tasks have since landed, so use it for
mathematics, not status.

## 15.3 `A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`

Use it as a prohibition document. It demonstrates exactly why a degree-one
shortcut from first variation is invalid. Any proof that appears to recover
that implication without using stronger Hessian/profile data is suspect.

## 15.4 Generic binary R18 modules

For Lean proof shape, these are more useful than the paper docs:

```text
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianRecognition
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDeterminantExtraction
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianCancellation
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurProfileBridge
```

The stationary proof should look like a source-honest specialization of this
mature R18 pipeline, not a fresh proof architecture.

---

# 16. Suggested commit sequence

Keep each commit small enough that a failure identifies one seam.

## Commit A — corrected source/profile determinant comparison

Add only the lemmas needed to prove

```lean
D.stationaryProfileHessianDetFamily_eq_zero hthree houtThree
```

from the verified source-first sheared determinant zero.

Acceptance:

```text
lake build <new module>
```

is green; no new assumptions.

## Commit B — stationary order-add + ramified-layer specialisation

Add:

```text
stationary_profileOrder_add
stationaryRamifiedFamily_parameterLayer_specialisation_...
```

or the exact minimal equivalents required by determinant extraction.

Do not include the determinant convolution yet if this commit becomes large.

## Commit C — stationary determinant coefficient extraction

Add the stationary analogue of
`binaryProfileHessianDetFamily_longitudinal_coeff` / layer extraction.

Acceptance: for every outer index `s`, zero family layer implies zero
`stationaryIntegralProfileHessianDet.coeff s`.

## Commit D — canonical determinant zero and left contradiction

Add

```lean
D.stationaryIntegralProfileHessianDet_eq_zero
D.impossible
F.impossible
```

for the left `V>1` chain.

At this point the left branch should be finished permanently.

## Commit E — right `V>1` symmetry wrapper

Transport `(V,1)` to the proved left case. No duplicate stationary algebra.

## Commit F — `V=1` source-facing closure

Add only the missing unit source adapters and invoke the existing mixed scalar
contradiction / same-orientation factorisation.

## Commit G — `.pr` normalized-carrier contradiction

Eliminate unit/left/right alternatives in one theorem.

## Commit H — cyclic other-facet contradiction

Transport `.sp/.rq` to `.pr` or consume existing generic relabeling.

## Commit I — strict-low local dispatcher splice

Remove the actual other-facet constructor from the current lower boundary / A19
terminal frontier. Check every sibling constructor explicitly.

## Commit J — unrestricted assembly

Connect the now-closed local frontier to the existing reachable-terminal HC4
reduction and expose the final public theorem. Then run the full root build and
proof/axiom audits before changing status documentation.

Only after Commit J is green should `CURRENT_STATE.md`, the formalisation
ledger, PR description, or paper claim be rewritten to say unrestricted HC4 is
Lean verified.

---

# 17. Likely Lean failure modes and the intended fixes

## 17.1 Natural subtraction fails to normalize

Do not fight `norm_num`/`simp` on expressions like

```text
(D-r*i) + (D-r*j) = 2D-r(i+j).
```

First prove

```text
r*i <= D
r*j <= D
```

from profile support, then `rw [Nat.mul_add]` and `omega`.

The previous `q+1+1` normalization failure in
`StationaryProfileHessianCoefficients` was a warning against brittle cast
normalization. Prefer deriving identities from already-proved Euler equations.

## 17.2 `Nat` casts into `Polynomial K`

Use the same pattern already used throughout the stationary files:

```lean
have hnC : (n : Polynomial K) = Polynomial.C (n : K) :=
  (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
rw [hnC]
```

Then use `map_add`, `map_sub`, `map_mul`, `map_one`, followed by `ring`.

## 17.3 `parameterFirstEquiv` representation noise

Do not expand the equivalence manually. Existing transport lemmas in
`PermutedPolynomialHessianFourBlock.lean` already identify active determinant,
Schur entries, determinant core, and Schur determinant under the equivalence.
Use those or map only after the source identity is proved.

## 17.4 Specialisation loses nonzero information

Never cancel a pivot after line specialisation. Source-first cancellation is
already implemented for exactly this reason.

## 17.5 Dependent package elaboration explodes

Keep state extraction in tiny private lemmas, then call state-free algebraic
lemmas. This pattern already made the A19.91 elimination tractable.

For right-orientation transport, if reconstructing a giant dependent record in
one term causes timeouts, create small coordinate/provenance helper theorems
first and build the record at the end.

## 17.6 Heartbeats

Do not put a giant `ring` against a full restart-state record. Normalize to
local scalar/polynomial variables first. Use `set_option maxHeartbeats` only
around a genuinely finite algebraic declaration, not as a substitute for
factoring the proof.

## 17.7 Generated inventory bot moves the head

Before every GitHub `update_file`, fetch the current blob SHA. A bot-only
inventory commit does not invalidate the mathematics, but stale blob SHAs will
make writes fail.

---

# 18. What not to build anymore

Unless a concrete type/lemma failure proves otherwise, do not add:

- another planar carrier package;
- another stationary profile definition;
- another parameter ramification family;
- another active-pivot cancellation theorem family;
- another generic binary Hessian determinant extraction framework;
- another line-supported ODE infrastructure;
- a generic JC2 fallback for this strict-low branch;
- a de Bondt--van den Essen formalisation;
- another rank-one termination measure;
- another ordinary reverse-Rees API;
- another `GeneralFourBlock` or Schur-complement representation.

All of those concepts already have canonical owners in the current tree.

---

# 19. Final completion checklist

The project may call unrestricted HC4 **LEAN VERIFIED** only after all of the
following are true:

- [ ] `D.stationaryProfileHessianDetFamily_eq_zero` compiles.
- [ ] exact stationary determinant-layer extraction compiles.
- [ ] `D.stationaryIntegralProfileHessianDet_eq_zero` compiles.
- [ ] left `(1,V)`, `V>1` contradiction compiles.
- [ ] right `(V,1)`, `V>1` is transported to the same contradiction.
- [ ] unit `V=1` same/mixed orientations are source-facing and closed.
- [ ] `.pr` normalized carrier has no surviving rank-three constructor.
- [ ] `.sp` and `.rq` are eliminated by verified cyclic symmetry/relabeling.
- [ ] the parent other-facet/lower-boundary theorem consumes that contradiction.
- [ ] every sibling A19 terminal constructor is either impossible or reaches an
      already-verified geometry/progress consumer.
- [ ] the reachable-terminal reduction has no caller-supplied local resolver.
- [ ] the public determinant-one gradient-injectivity theorem compiles.
- [ ] `lake build` from the root is green on the exact head.
- [ ] generated proof inventory is current.
- [ ] proof-escape audit (`sorry`, `admit`, `axiom`, `unsafe`) is clean.
- [ ] `#print axioms` / project axiom audit for the public theorem is clean.
- [ ] no JC2, balance, global homogeneity, caller degree cap, or repair-only
      hypothesis appears in the public theorem.

---

# 20. The shortest path from here

The practical order is now:

```text
1. prove stationaryProfileHessianDetFamily = 0
2. copy/adapt the mature binary determinant-layer extraction
3. prove stationaryIntegralProfileHessianDet = 0
4. invoke impossible_of_stationaryIntegralProfileHessianDet
5. wrap left V>1
6. symmetry-wrap right V>1
7. close V=1 with the existing endpoint scalar contradiction / factorisation
8. close .pr
9. relabel .sp/.rq
10. splice the actual other-facet contradiction upward
11. compile the unrestricted public theorem
12. run root + axiom/proof audits
```

The only step in that list that should still require genuinely delicate new
algebra is step 1, and even there the necessary Euler/falling-row identities
are already formalised. Step 2 should be mostly a specialization of the
existing R18 binary convolution proof. Steps 3--10 should increasingly become
plumbing and case elimination.

That is the current finish line.