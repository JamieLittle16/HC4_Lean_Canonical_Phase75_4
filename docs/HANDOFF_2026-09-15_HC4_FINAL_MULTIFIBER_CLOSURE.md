# HC4 final multi-fibre closure handoff — 15 September 2026

> **Purpose.** This is the authoritative implementation-grade handoff for the
> unrestricted HC4 final sprint on PR #34. It is intended to be sufficient for
> a fresh context window to resume the proof without reconstructing the last
> several days of Lean work, counterexamples, source-provenance decisions, and
> determinant calculations.
>
> **This document supersedes the status/TODO sections of**
> `docs/HANDOFF_2026-09-15_HC4_PAIR_REES_FINAL_CLOSURE.md`.
> The pair-Rees handoff remains valuable for the detailed history of the two
> endpoint Rees constructions, but its principal open task — generic
> finite-staircase coupling — has now been substantially closed and replaced by
> a much sharper multi-fibre exposed-edge problem.

## Repository checkpoint

- Repository: `JamieLittle16/HC4_Lean_Canonical_Phase75_4`
- PR: `#34 — A18.4.42 collapse final termination frontier`
- Branch: `final-assembly/a18-4-42-termination-frontier`
- Current proof/inventory head at handoff creation:
  `8ea4cd66ec07f00dd2b6597dd3e551afe1cf0b66`
- Current compilation status: **LEAN VERIFIED** at this checkpoint by the
  current clean/root build reported during the handoff session.
- Connector note: the GitHub Actions run attached to this exact generated-docs
  head is `action_required` before jobs start, so re-audit CI on resume rather
  than interpreting that UI state as a Lean failure. The immediately preceding
  substantive proof stack has been compiling cleanly.

A documentation-only commit containing this handoff may move the PR head after
`8ea4cd...`; re-audit the live head before editing code.

---

# 0. Start here in a fresh context

The shortest accurate status is:

```text
Global HC4 entry / normalisation / rank-one termination       LEAN VERIFIED
A19.55 same-carrier codimension-two -> rank-two geometry      LEAN VERIFIED
lower .qs outside codimension-two elimination                 LEAN VERIFIED
rank-three other-facet planar carrier / highest slice         LEAN VERIFIED
left (1,V), V>1 staircase classification                      LEAN VERIFIED
locked/contact-end first interior Rees equation                LEAN VERIFIED
highest/pair-Rees first interior equation                      LEAN VERIFIED
finite-staircase extremal ordering                             LEAN VERIFIED
complete one-fibre elimination                                 LEAN VERIFIED
genuine multi-fibre strict extremal separation                 LEAN VERIFIED
cross-roof staircase arithmetic                                LEAN VERIFIED
state-free cross-roof terminal -> high residual = 1            LEAN VERIFIED

multi-fibre source-honest exposed-roof adapter                 OPEN
mirror/dual cross-roof terminal -> low residual = 1            OPEN
multi-fibre contradiction -> NoStrictInteriorSupport           OPEN
NoStrictInteriorSupport -> exact two-function carrier          LEAN VERIFIED
exact two-function carrier -> False                            LEAN VERIFIED

right (V,1), V>1 symmetry wrapper                              OPEN
V=1 source-facing closure                                      OPEN
.pr wrapper                                                     OPEN
.sp/.rq cyclic relabelling                                     OPEN
other-facet/A19/global splice                                  OPEN
public unrestricted HC4 theorem without resolver               OPEN
```

The key strategic change is:

> **Do not resume by deriving another endpoint recurrence.**
>
> The one-fibre branch is completely dead. Under surviving strict-interior
> support the two honest Rees extrema are now provably distinct. The current
> left-branch problem is therefore a genuine finite multi-fibre Newton polygon.
> The new state-free cross-roof terminal theorem already resolves the hard
> exceptional affine-line algebra. What remains is to construct the correct
> source-honest exposed roof transition, obtain the same unit-residual conclusion
> from the opposite orientation, and collapse the staircase arithmetically.

Once `F.NoStrictInteriorSupport` is available, the left `(1,V), V>1` branch is
already contradicted by existing compiled code.

---

# 1. Status vocabulary — use these labels literally

Use only:

- **LEAN VERIFIED** — formalised, rooted, and known to compile at the stated
  checkpoint;
- **SOURCE-LANDED / NOT LEAN VERIFIED** — committed but no successful build is
  yet known for that exact head;
- **PAPER CANDIDATE** — a complete or nearly complete mathematical argument
  exists but has not been installed in Lean;
- **DIAGNOSTIC ONLY** — symbolic/computational evidence, not a proof theorem;
- **OPEN** — a genuine mathematical or formal bridge remains.

Do not say unrestricted HC4 is proved until the public determinant-one theorem
compiles with no caller-supplied terminal resolver, no JC2 hypothesis, no
balance assumption, no homogeneity assumption, and no repair-only
contradiction.

---

# 2. Non-negotiable architectural rules

Carry these into every continuation.

1. **Do not identify auxiliary Rees clocks with the zero blocker.**
   Contact Rees, pair-degree reverse Rees, stationary clocks, and ordinary
   reverse-Rees parameters are separate filtrations unless an explicit theorem
   identifies them.

2. **Do not use naked `withRepairOnly` progress as a contradiction.**
   Rank-two progress must carry actual Hessian/Schur geometry.

3. **Do not infer singularity of a superface from a smaller singular face.**
   Every singular carrier/line/face used in the final proof needs its own honest
   initial-form, determinant, or Rees-covariance theorem.

4. **Do not collapse A19 strict-low to generic JC2.**
   The actual branch retains much stronger source/contact/ray provenance and
   the codimension-two side is already locally closed without JC2.

5. **Do not revive the old four-monomial cross-ratio equation as a
   contradiction by itself.**

6. **Do not conflate the two codimension-two branches.**
   A19.55 same-carrier exposed codimension two and the later lower `.qs`
   outside-endpoint codimension two are different objects with different
   consumers.

7. **Do not add a second global/rank-one recursion.**
   The existing raw-defect termination trace is the global mechanism.

8. **Do not reintroduce the false first-variation degree shortcut.**
   The example

   ```text
   V=2, ell=4, n=3, k=2, j=2,
   phi=(5+4T)^2
   ```

   defeats the statement “first variation + staircase arithmetic implies
   degree <= 1”. See
   `docs/A1_FIRST_INTERIOR_ADAPTER_AUDIT_2026-09-13.md`.

9. **Do not revive the generic stationary source/profile determinant
   implication.** It was explicitly falsified and replaced by the honest
   pair-Rees/finite-staircase route.

10. **Do not treat equality of the two endpoint affine roots as a
    contradiction.** Root equality is a useful coupling fact; the actual
    one-fibre contradiction required second/intermediate determinant
    coefficients.

11. **Search existing infrastructure before adding a package.** The repository
    now contains canonical owners for finite staircase extrema, affine layers,
    exact three-layer pencils, polynomial reflection, separated parameter jets,
    endpoint cross variations, affine-line terminals, and the final
    two-function contradiction.

---

# 3. End-to-end architecture

The public reduction already reduces unrestricted HC4 to presented-terminal
impossibility. The mature path is:

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
        +----------------------------------+
        |                                  |
        v                                  v
A19.55 same-carrier               rank-three first-nonfacet /
codimension two                   lower .qs boundary
        |                                  |
        | LEAN VERIFIED                    | LEAN VERIFIED
        v                                  v
explicit rank-two geometry        actual other-facet rank-three endpoint
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

The same-carrier codimension-two side is not the current mathematical blocker.
The live blocker is the other-facet rank-three local closure, currently reduced
inside `.pr` to the left non-unit finite staircase, and inside that branch to a
genuine multi-fibre exposed-edge problem.

---

# 4. Authoritative left `(1,V)`, `V>1` setup

The live data are:

```lean
C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs
P : QsOtherFacetPlanarCarrierPackage C .pr
S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P
R : QsOtherFacetContactQuadraticReesPackage C
F : QsOtherFacetPrLeftVContactFrontierData C P S R
hthree    : MvRankThreeOnFacet .qs C.ray.facetExponent
houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent
```

Notation:

```text
V   := F.V,                 1 < V
n   := F.highest.n,         2 <= n
ell := F.locked.ell,        0 < ell
```

The retained endpoint/contact separation gives

```text
n < ell + 1
```

and hence

```text
n <= ell.
```

For any strict-interior staircase fibre write

```text
k = normalized pair degree,
j = first transverse height minus one.
```

The exact wall equation is

```text
(n - 1) * j = ell * (n - k).
```

For support points on a fibre `(k,j)`, the affine coordinate formulas are
schematically

```text
e0 = t
e1 = k - t
e2 = j + 1 - t
e3 = V * (k + j - t).
```

Thus the two coordinate roofs occur at:

```text
y=0 roof: t = k
  exponent = (k, 0, j+1-k, V*j)
  residual q = j+1-k;

z=0 roof: t = j+1
  exponent = (j+1, k-j-1, 0, V*(k-1))
  residual v = k-j-1.
```

Only one of these residuals is positive away from the central diagonal
`j+1=k`; the central point has both `y=z=0`.

The exact goal remains:

```lean
def F.NoStrictInteriorSupport : Prop :=
  ∀ {e}, e ∈ P.carrier.support →
    rankThreeQuotientCoordinate 1 F.V e |>.pair = 1 ∨
    rankThreeQuotientCoordinate 1 F.V e |>.pair = F.highest.n
```

Already **LEAN VERIFIED** downstream:

```lean
F.support_eq_locked_highest_of_noStrictInterior hno
F.twoFunctionCarrierData_of_noStrictInterior hno
F.impossible_of_noStrictInterior hno : False
```

Therefore the entire left non-unit branch now hinges only on proving
`NoStrictInteriorSupport`.

---

# 5. What has been completed since the pair-Rees handoff

The previous handoff stopped with two endpoint first-variation equations and
called the remaining work “finite-staircase coupling”. That description is now
outdated.

## 5.1 Finite staircase extremal ordering — LEAN VERIFIED

Key modules:

```text
...PrVGreaterOneFiniteStaircaseInterface.lean
...PrVGreaterOneFiniteStaircaseExtremalFibers.lean
...PrVGreaterOneFiniteStaircaseDualExtrema.lean
```

The contact-oriented Rees selects the **least** surviving strict-interior pair
degree; the pair-degree reverse Rees selects the **greatest** surviving
strict-interior pair degree.

For already-built affine packages

```text
Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo
Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dpair
```

one has, for every strict-interior support point `e`,

```text
Alo.k <= pair(e) <= Ahi.k.
```

## 5.2 Coincident extrema / one-fibre coupling — LEAN VERIFIED

Key modules:

```text
...FiniteStaircaseOneFiber.lean
...FiniteStaircaseEndpointEuler.lean
HC4/Polynomial/AffineEulerTwoRootDegree.lean
HC4/Polynomial/AffineEulerTwoRootDistinctRoots.lean
...FiniteStaircaseOneFiberDegree.lean
...FiniteStaircaseOneFiberRoot.lean
```

If

```text
Alo.k = Ahi.k,
```

then every strict-interior support monomial lies in one normalized quotient
fibre. More strongly:

- the selected contact and pair-Rees parameter layers are literally equal;
- the selected univariate coefficient profiles are literally equal;
- that common nonzero profile satisfies both endpoint affine two-root Euler
  equations;
- the two endpoint affine roots are forced to coincide;
- the common profile degree can lie only on three adjacent staircase
  diagonals.

The three diagonal alternatives are:

```text
j + 2 = k,
j + 1 = k,
j     = k.
```

## 5.3 Lower and upper one-fibre diagonals — LEAN VERIFIED

Key modules include:

```text
...OneFiberLowerImpossible.lean
...OneFiberUpperImpossible.lean
```

These eliminate the two pure outer diagonals using the honest endpoint
variation machinery.

## 5.4 Middle one-fibre diagonal — LEAN VERIFIED

This is the major recent simplification.

Relevant state-free infrastructure:

```text
HC4/Polynomial/FiniteStaircaseMiddleDoubleRootVariation.lean
HC4/Polynomial/FiniteStaircaseThreeLayerEvaluation.lean
HC4/Polynomial/FiniteStaircaseEndpointDoubleRootEvaluation.lean
HC4/Polynomial/FiniteStaircaseEndpointCrossVariation.lean
HC4/Polynomial/FiniteStaircaseEndpointCrossScaled.lean
HC4/Valuation/SeparatedParameterDualJet.lean
```

Relevant source-facing infrastructure:

```text
...OneFiberThreeLayerPencil.lean
...OneFiberThreeLayerReflection.lean
...OneFiberMiddleTop.lean
...OneFiberMiddleLowerImpossible.lean
...OneFiberCentralLowerMode.lean
...OneFiberMiddleImpossible.lean
```

The final middle proof no longer needs a cubic jet or any general developable
classification.

On `j+1=k`, let

```text
q_hi = n-k,
q_lo = k-1,
N    = n-1.
```

The wall equation and `n <= ell` force

```text
q_hi < q_lo,
```

so

```text
q_lo < N = q_lo + q_hi < 2*q_lo.
```

Reflecting the exact pair-Rees three-layer pencil gives

```text
H_locked + tau^q_lo H_int + tau^N H_highest.
```

At the separated order `N`, the determinant coefficient cannot contain a
quadratic interior contribution because `N < 2*q_lo`. It is therefore exactly
the first variation from the locked endpoint to the primitive-highest
endpoint. Evaluating at twice the already-verified common affine root reduces
this to the explicit state-free endpoint cross determinant

```text
4 * V * (V+1) * ell^3 * n * (ell+1)^3 * (n-1)^2
```

up to nonzero endpoint scaling. Every factor is nonzero in the live branch,
contradicting singularity.

Canonical theorem:

```lean
D.oneFiber_middle_impossible ... : False
```

## 5.5 Complete one-fibre contradiction — LEAN VERIFIED

Canonical module:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberImpossible.lean
```

Canonical theorem:

```lean
D.oneFiber_impossible
  F Alo Ahi hthree houtThree hnot hext : False
```

This theorem packages the lower, middle, and upper diagonal eliminations.

**Do not reopen the one-fibre algebra.**

---

# 6. Genuine multi-fibre entry — LEAN VERIFIED

Canonical module:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseMultiFiberExtrema.lean
```

The completed one-fibre theorem upgrades weak extremal ordering to strict
separation:

```lean
D.extremalPair_lt
  F Alo Ahi hthree houtThree hnot : Alo.k < Ahi.k
```

and correspondingly:

```lean
D.extremal_pairReesOrder_lt ... :
  n - Ahi.k < n - Alo.k

D.extremal_reflectedOrder_lt ... :
  Alo.k - 1 < Ahi.k - 1
```

So under

```lean
hnot : ¬ F.NoStrictInteriorSupport
```

we are now **provably in a genuine multi-fibre branch**. There is no remaining
case split back to one fibre.

This is the canonical starting theorem for the next implementation session.

---

# 7. New cross-roof arithmetic — LEAN VERIFIED

State-free owner:

```text
HC4/Polynomial/FiniteStaircaseCrossRoofArithmetic.lean
```

Consider two distinct staircase fibres

```text
(kLo,jLo), (kHi,jHi),
kLo < kHi,
(n-1)jLo = ell(n-kLo),
(n-1)jHi = ell(n-kHi),
n <= ell.
```

The staircase is steeper than slope `-1`:

```lean
staircase_heightDrop_gt_pairGain:
  kHi-kLo < jLo-jHi.
```

Suppose the lower selected endpoint lies on the `y=0` roof and the higher
endpoint lies on the `z=0` roof. Define positive residuals

```text
q = jLo + 1 - kLo,
v = kHi - jHi - 1.
```

Then:

```lean
crossRoof_residual_sum:
  q + v = (kHi-kLo) + (jLo-jHi).
```

Additional verified exceptional-direction translations include:

```lean
crossRoof_fixed_x_iff
crossRoof_fixed_w_iff
crossRoof_fixed_w_iff_ordinaryDegree
no_crossRoof_fixed_x_and_fixed_w
no_crossRoof_fixed_w_terminal_degree_relation
```

These are exactly the arithmetic needed to eliminate the exceptional factors
in the general rank-three affine-line terminal stack.

A particularly useful future final step is immediate from the first two
relations:

```text
q = 1 and v = 1
  -> q+v = 2
  -> pairGain + heightDrop = 2
```

but `pairGain >= 1` and `heightDrop > pairGain`, hence
`heightDrop >= 2`, so the right side is at least `3`. Contradiction.

That final arithmetic is essentially `omega` once both unit residuals are in
hand.

---

# 8. New state-free cross-roof terminal theorem — LEAN VERIFIED

Owner:

```text
HC4/RationalRigidity/FiniteStaircaseCrossRoofTerminal.lean
```

Canonical theorem:

```lean
HC4.RationalRigidity.finiteStaircase_crossRoof_highResidual_eq_one
```

Input:

- two distinct live staircase fibres `(kLo,jLo)` and `(kHi,jHi)`;
- lower `y=0` residual `q>0`;
- higher `z=0` residual `v>0`;
- an honest coefficient polynomial `phi` with
  `phi.natDegree = v` and nonzero constant coefficient;
- a
  `HasRankThreePolynomialTerminalCertificate`
  for the exposed cross-roof affine line, indexed from the lower `y=0`
  endpoint by its `y` coordinate.

The primitive line direction is encoded as

```text
(1,
 (jHi+1-kLo)/v,
 -q/v,
 V*(kHi-1-jLo)/v).
```

Conclusion:

```text
v = 1.
```

Why the theorem is strong:

- if the generic highest-direction factor is nonzero, terminal rigidity forces
  degree one immediately;
- if one direction component vanishes, the existing single-direction
  refinement is invoked;
- fixed-`x` and fixed-`w` exceptional directions are converted to exact
  staircase arithmetic and eliminated;
- the homogeneous fixed-`w` case is killed by the existing next-coefficient
  relation `A+B=D` plus
  `no_crossRoof_fixed_w_terminal_degree_relation`.

This means the difficult **state-free algebra for a cross-roof edge is done**.
The future A19 work should be a thin source/exposed-face adapter rather than a
new rational-rigidity proof.

---

# 9. The exact OPEN local seam: expose and adapt the multi-fibre roof transition

This is now the principal mathematical/formal gap.

Under `hnot`, choose the genuine extremal interior fibres

```text
kLo := Alo.k,
kHi := Ahi.k,
kLo < kHi.
```

Their wall heights are given by the affine packages / wall theorem:

```text
(n-1) jLo = ell (n-kLo),
(n-1) jHi = ell (n-kHi).
```

The goal is **not** simply to assert that these two extrema themselves are on
opposite roofs. That is not automatic. Depending on where the occupied fibres
sit relative to the central diagonal `j+1=k`, several geometric patterns are
possible.

The correct Newton-polygon task is:

> Inside the actual source-honest planar carrier, choose an exposed edge or
> transition along the finite staircase hull that connects a `y=0` roof point
> to a `z=0` roof point, or eliminate all alternatives (same-roof edges and a
> possible central transition) using existing singular-initial/line rigidity.

This distinction is important. **Do not write a theorem assuming a cross-roof
edge merely from `Alo.k < Ahi.k`.**

## 9.1 Existing geometry to reuse

Fixed pair-degree fibres are already honest affine lines parallel to the
locked ray:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarLineSupport.lean
```

Key theorem:

```lean
P.support_difference_parallel_ray ...
```

and the corresponding highest-slice theorem.

Thus each occupied pair fibre is one finite segment in the known direction;
its natural coordinate endpoints lie on the two coordinate roofs described in
Section 4.

The highest pair slice is already primitive:

```text
...OtherFacetPlanarPrimitiveSlice.lean
```

with the state-free rank-three line rigidity theorem

```lean
HC4.RationalRigidity.affine_line_natDegree_eq_one_of_direction_factor_ne_zero
```

and exact support `{0,1}` for the nonexceptional locked-ray direction.

Finite-support exposure / initial-form infrastructure already exists. Search
before adding anything, especially:

```text
HC4/Polynomial/UniqueMaximalInitialMonomial.lean
HC4/Polynomial/MaximalHessianInitial.lean
HC4/Newton/FiniteSupportExposedFaceRefinement.lean
HC4/Newton/FiniteSupportExposedVertex.lean
HC4/Newton/FiniteSupportRayPlanarRefinement.lean
```

## 9.2 Unique positive exposed vertices are impossible

This is an important reusable observation from the already-compiled
one-fibre middle-lower proof.

If an exposed maximal initial of the singular carrier consists of one monomial
whose four exponent coordinates are positive, then

```text
initial singularity
+ literal monomial initial
+ hessianDeterminant_monomial_ne_zero
```

is a contradiction.

The generic helper

```lean
initialForm_eq_monomial_of_unique_max
```

already exists.

Therefore an interior positive support monomial cannot be a unique exposed
vertex. This should help eliminate some same-roof hull configurations without
new determinant algebra.

Be careful: the central point with `y=z=0` is degenerate as a monomial, so this
argument alone does **not** eliminate a central roof-intersection vertex.

## 9.3 Cases the adapter must honestly handle

A fresh implementation should expect a finite hull-path case split of the
following shape:

```text
(A) an exposed edge has endpoints on opposite roofs
    -> cross-roof terminal route;

(B) an exposed edge stays on y=0 roof
    -> use the existing rank-three affine-line / homogeneous exceptional
       machinery, or show the edge forces a forbidden exposed vertex;

(C) an exposed edge stays on z=0 roof
    -> symmetric treatment;

(D) the hull transition passes through a central point y=z=0
    -> isolate this explicitly; do not silently identify it with the old
       one-fibre central case, because other fibres may still be present.
```

The strong expectation is that (B)/(C)/(D) are small once written in the right
source-honest exposed-face language. The difficult terminal exceptional
algebra for (A) is already compiled.

Status: **OPEN**.

---

# 10. First cross-roof source adapter: high residual

Once an honest exposed cross-roof edge is selected, write its endpoints as

```text
L = (kLo, 0, q, V*jLo),
H = (jHi+1, v, 0, V*(kHi-1)),
```

where

```text
q = jLo+1-kLo > 0,
v = kHi-jHi-1 > 0.
```

Index the line from `L` by the `y` coordinate. After putting that omitted
coordinate first, the rank-three affine-line data have base

```text
(kLo, q, V*jLo)
```

and direction

```text
(1,
 (jHi+1-kLo)/v,
 -q/v,
 V*(kHi-1-jLo)/v).
```

The adapter must prove:

1. the selected exposed face is an honest source face / initial form of
   `P.carrier`;
2. its Hessian determinant is zero by initial-form singularity of
   `P.hessian_zero`;
3. its support lies on the displayed affine line;
4. its coefficient polynomial has degree exactly `v` with nonzero constant
   endpoint coefficient;
5. therefore it yields
   `HasRankThreePolynomialTerminalCertificate` with the parameters expected by
   `finiteStaircase_crossRoof_highResidual_eq_one`.

Then invoke the compiled theorem to obtain

```text
v = 1.
```

Likely owners to reuse while building the certificate:

```text
HC4/Polynomial/RankThreeAffineLineRealisation.lean
HC4/RationalRigidity/RankThreeAffineLineTerminal.lean
HC4/RationalRigidity/RankThreeSingleDirectionRefinement.lean
HC4/Polynomial/MaximalHessianInitial.lean
```

Do not reconstruct the autonomous ODE or terminal relation manually.

Status: **OPEN**, expected mostly adapter/exposure work once the edge is in
hand.

---

# 11. Mirror cross-roof orientation: low residual

After the high-side theorem gives `v=1`, the cleanest closure is to obtain the
symmetric conclusion

```text
q = 1.
```

There are two acceptable implementations.

## 11.1 Preferred: transport/permutation reuse

Try first to reuse the existing terminal theorem through an honest coordinate
permutation / reversal of the exposed line.

Index the same geometric line from the `z=0` endpoint `H` by the `z`
coordinate. The opposite orientation has degree `q`; schematically the base
transverse exponents are

```text
(jHi+1, v, V*(kHi-1))
```

and direction is the normalized reverse edge

```text
(1,
 (kLo-(jHi+1))/q,
 -v/q,
 V*(jLo-(kHi-1))/q).
```

Search the existing line-specialisation permutation/parameter-swap stack
before writing a duplicate theorem, especially modules named

```text
RankThreeLineSpecialisation*Swap.lean
PermutedPolynomialHessianFourBlock.lean
PermutedFamilyHessianFourBlock.lean
```

If a clean permutation turns this into the hypotheses of the existing
cross-roof theorem, use it.

## 11.2 Fallback: state-free mirror theorem

If transporting the arithmetic names is more awkward than the proof, add a
state-free companion

```lean
finiteStaircase_crossRoof_lowResidual_eq_one
```

by mirroring `FiniteStaircaseCrossRoofTerminal.lean`.

Keep it state-free. Do **not** duplicate any A19 package or Rees construction.
The proof should reuse the same mature rank-three terminal relations and the
same cross-roof arithmetic.

Conclusion:

```text
q = 1.
```

Status: **OPEN**.

---

# 12. Final multi-fibre contradiction after both unit residuals

Once

```text
q = 1,
v = 1,
```

the contradiction is purely arithmetic.

From

```lean
crossRoof_residual_sum
```

obtain

```text
2 = (kHi-kLo) + (jLo-jHi).
```

From distinct pair degrees:

```text
1 <= kHi-kLo.
```

From

```lean
staircase_heightDrop_gt_pairGain
```

obtain

```text
kHi-kLo < jLo-jHi,
```

so

```text
2 <= jLo-jHi.
```

Hence the right side is at least `3`, contradiction.

This should be a tiny state-free or adapter-level `omega` proof once the two
terminal conclusions are available.

Desired source-facing theorem, schematically:

```lean
theorem QsOtherFacetPrPairReesData.multiFiber_impossible
    (F : ...)
    (Dpair : ...)
    (Alo : ...)
    (Ahi : ...)
    (hthree : ...)
    (houtThree : ...)
    (hnot : ¬ F.NoStrictInteriorSupport) : False := by
  have hlt := Dpair.extremalPair_lt F Alo Ahi hthree houtThree hnot
  -- construct exposed roof transition
  -- high residual = 1
  -- low residual = 1
  -- crossRoof_residual_sum + staircase_heightDrop_gt_pairGain
```

Status: **OPEN**.

---

# 13. Package `NoStrictInteriorSupport` and close left `V>1`

Once the multi-fibre contradiction compiles, the left branch becomes very
small.

Recommended theorem:

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.noStrictInterior
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    F.NoStrictInteriorSupport := by
  by_contra hnot
  rcases F.planarContactRees hthree houtThree with ⟨Dlo⟩
  rcases F.pairRees hthree houtThree with ⟨Dpair⟩
  rcases Dlo.exists_firstInteriorAffineLayer_... hthree houtThree hnot with
    ⟨Alo, ...⟩
  rcases Dpair.exists_firstPositiveLayer_highestEulerEquation_left
      F hthree houtThree hnot with ⟨Ahi, ...⟩
  exact Dpair.multiFiber_impossible
    F Alo Ahi hthree houtThree hnot
```

Then the parent-facing theorem is literally:

```lean
theorem QsOtherFacetPrLeftVContactFrontierData.impossible
    (F : ...)
    (hthree : ...)
    (houtThree : ...) : False := by
  exact F.impossible_of_noStrictInterior
    (F.noStrictInterior hthree houtThree)
```

Do not leak Rees families, moment matrices, or hull certificates into the
public parent interface.

Status: **OPEN**, but all downstream mathematics after `NoStrictInteriorSupport`
is already **LEAN VERIFIED**.

---

# 14. Right `(V,1)`, `V>1` after left closure

This remains a symmetry task, not a second staircase proof.

The normalized infrastructure already contains

```lean
QsOtherFacetPrRightVContactFrontierData.
```

Preferred source permutation:

```text
2 <-> 3
```

fixing coordinates `0,1`. It sends

```text
(1,-1,-V,-1)
```

to

```text
(1,-1,-1,-V).
```

Transport only enough source data to instantiate the left impossibility
result:

```text
planar carrier and Hessian singularity;
locked source endpoint coefficients/nonvanishing;
primitive highest endpoint coefficients/nonvanishing;
quotient direction;
contact/source bound;
V>1.
```

If transporting the dependent right frontier record is unpleasant, add a
small source permutation theorem and reconstruct the minimal left-facing
record. **Do not copy the finite-staircase proof.**

Desired theorem:

```lean
theorem QsOtherFacetPrRightVContactFrontierData.impossible ... : False
```

Status: **OPEN**, expected mostly plumbing after left closure.

---

# 15. Unit branch `V=1`

Keep this separate from the non-unit proof.

## Mixed orientation

State-free contradiction already **LEAN VERIFIED**:

```text
HC4/Polynomial/TwoFunctionMixedOrientationRigidity.lean
```

with theorem

```lean
HC4.Polynomial.mixedOrientation_endpoint_coefficients_impossible
```

consuming endpoint relations of the shape

```text
2*A*D = B*C,
A*D   = 2*B*C,
```

with the required nonzero coefficients.

The remaining work is source-facing extraction of those two determinant
coefficients from the actual `V=1` carrier.

## Same orientation

Use the existing two-function determinant factorisation or a tiny `V=1`
specialisation. Do not build another carrier classification.

Status: **OPEN**.

The detailed paper algebra remains in
`docs/HANDOFF_2026-09-12_HC4_PAPER_CLOSURE.md`.

---

# 16. Close `.pr`, then `.sp` / `.rq`

After left non-unit, right non-unit, and unit alternatives are contradicted,
package a single `.pr` theorem at the highest source-honest level possible.

Use the existing normalized-carrier/frontier constructors rather than creating
new cases.

Desired shape:

```lean
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_impossible ... : False
```

For `.sp` and `.rq`, prefer cyclic relabelling into `.pr` rather than cloning
any planar/staircase proof.

Existing permutation infrastructure includes the active superface Schur
permutations and the general permuted Hessian modules.

Status: **OPEN**.

---

# 17. Upward A19/global splice

Once every different-facet rank-three endpoint is impossible, splice upward
through the current import graph rather than editing old phase files blindly.
The expected route remains approximately:

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

After the local theorem compiles, search reverse imports first; generated
module indexes are available and should prevent stale-path editing.

Important sibling constructors must route through their existing dedicated
consumers. Do not silently erase:

```text
start-codimension-two;
quadratic-square;
confined-support;
geometry-bearing rank-two successor.
```

The A19.55 codimension-two constructor must continue through

```lean
exposedCodimensionTwo_resolvedRankTwoGeometry
```

rather than generic JC2.

Status: **OPEN**, expected mostly assembly once the other-facet theorem exists.

---

# 18. Public theorem target

The unrestricted reducer already proves gradient injectivity from a
presented-terminal impossibility resolver. The final public theorem should
supply that resolver internally.

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

Use the repository's final preferred theorem name.

Acceptance requires:

```text
full root build green;
#print axioms audit clean;
negative control still rejected;
no sorry/admit/native_decide/unsafe proof escape;
no hidden JC2/resolver argument in the public theorem.
```

Status: **OPEN**.

---

# 19. Recent Lean modules that matter — do not duplicate them

## Finite staircase ordering / one fibre

```text
...FiniteStaircaseInterface.lean
...FiniteStaircaseExtremalFibers.lean
...FiniteStaircaseDualExtrema.lean
...FiniteStaircaseOneFiber.lean
...FiniteStaircaseEndpointEuler.lean
...FiniteStaircaseOneFiberDegree.lean
...FiniteStaircaseOneFiberRoot.lean
...FiniteStaircaseOneFiberLowerImpossible.lean
...FiniteStaircaseOneFiberUpperImpossible.lean
...FiniteStaircaseOneFiberMiddleImpossible.lean
...FiniteStaircaseOneFiberImpossible.lean
...FiniteStaircaseMultiFiberExtrema.lean
```

## State-free one-fibre determinant machinery

```text
HC4/Polynomial/AffineEulerTwoRootDegree.lean
HC4/Polynomial/AffineEulerTwoRootDistinctRoots.lean
HC4/Polynomial/FiniteStaircaseMiddleDoubleRootVariation.lean
HC4/Polynomial/FiniteStaircaseThreeLayerEvaluation.lean
HC4/Polynomial/FiniteStaircaseThreeLayerSecondVariation.lean
HC4/Polynomial/FiniteStaircaseEndpointDoubleRootEvaluation.lean
HC4/Polynomial/FiniteStaircaseEndpointCrossVariation.lean
HC4/Polynomial/FiniteStaircaseEndpointCrossScaled.lean
HC4/Valuation/ParameterGapSecondJet.lean
HC4/Valuation/SeparatedParameterDualJet.lean
```

## New multi-fibre cross-roof owners

```text
HC4/Polynomial/FiniteStaircaseCrossRoofArithmetic.lean
HC4/RationalRigidity/FiniteStaircaseCrossRoofTerminal.lean
```

The second currently has no A19 source-facing importer. That is intentional:
**the next real commit is the adapter.**

## Planar geometry / line support owners

```text
...OtherFacetPlanarCarrier.lean
...OtherFacetPlanarLineSupport.lean
...OtherFacetPlanarHighestPairSlice.lean
...OtherFacetPlanarPrimitiveSlice.lean
HC4/Polynomial/RankThreeAffineLineRealisation.lean
HC4/RationalRigidity/RankThreeAffineLineTerminal.lean
HC4/RationalRigidity/LineSupportedHessianRigidity.lean
```

## Post-interior contradiction owners

```text
...PrVGreaterOneNoInteriorSupport.lean
...PrVGreaterOneFourTermCarrier.lean
...PrVGreaterOneTwoFunctionReconstruction.lean
HC4/Polynomial/TwoFunctionCarrierHessianRigidity.lean
HC4/Polynomial/TwoFunctionCarrierMonomialNormalForm.lean
```

---

# 20. Useful mathematical picture of the remaining carrier

The entire left staircase lies in a two-dimensional affine lattice. One useful
paper parameterisation is:

```text
d = gcd(n-1, ell)
a = (n-1)/d
b = ell/d
```

with wall fibres

```text
k_r = n-a*r,
j_r = b*r.
```

A support exponent on fibre `r` with longitudinal coordinate `t` is

```text
e(r,t) =
  (t,
   n-a*r-t,
   b*r+1-t,
   V*(n+(b-a)*r-t)).
```

Equivalently the carrier support lies in the affine plane generated by

```text
u = (0,-a,b,V*(b-a))
v = (1,-1,-1,-V).
```

This is useful for intuition, but the current Lean proof does **not** require
formalising the gcd parameterisation unless the exposed-hull adapter becomes
simpler with it.

Another exact support relation is

```text
e3 = V * (e0+e1+e2-1).
```

At paper level this yields a simple row identity for the Euler-scaled Hessian:
subtracting `V` times rows `0,1,2` from row `3` leaves only a diagonal term.
This is a useful conceptual explanation of the old bivariate factorisation,
but it is not currently needed for the preferred cross-roof adapter route.
Treat it as **PAPER CANDIDATE** unless installed explicitly.

---

# 21. Abandoned / fallback routes

## Generic stationary determinant comparison — prohibited

The old claim that source Hessian singularity generically implies the
stationary profile Hessian determinant vanishes is false. Keep the obstruction
file and counterexample as a prohibition, not as a TODO.

## First-variation degree <= 1 shortcut — prohibited

False, as recorded above.

## Full Gordan–Noether/developable classification — fallback only

The repository still does not need a full external homogeneous singular
Hessian classification if the specialized cross-roof terminal route closes the
multi-fibre branch. Do not formalise a large theorem merely because the old
paper proof mentioned it.

## Bivariate `Psi(S,T)` Hessian factorisation — diagnostic/paper fallback

The symbolic representation of the whole staircase is useful for intuition
and suggests a clean factorisation, but the current source-honest route has
moved beyond it. Use only if the exposed-edge adapter unexpectedly fails.

---

# 22. Recommended commit sequence from this checkpoint

Keep every seam independently compilable.

## Commit A — exposed roof-transition geometry

Suggested owner:

```text
...PrVGreaterOneFiniteStaircaseMultiFiberRoofTransition.lean
```

Goal:

- start from `D.extremalPair_lt`;
- choose the relevant exposed hull edge/transition;
- prove either a genuine cross-roof edge or one of a small set of same-roof /
  central alternatives;
- eliminate the easy alternatives using existing singular-initial / line
  rigidity where possible.

Acceptance: return literal source support endpoints and their wall coordinates;
do not yet invoke the terminal theorem.

## Commit B — cross-roof affine-line terminal adapter

Suggested owner:

```text
...PrVGreaterOneFiniteStaircaseCrossRoofTerminalAdapter.lean
```

Build the honest exposed line data/certificate and call

```lean
finiteStaircase_crossRoof_highResidual_eq_one
```

to get `v=1`.

## Commit C — mirrored low residual

First attempt a line reversal/coordinate permutation reusing Commit B and the
existing state-free theorem. If awkward, add a **state-free** companion theorem
for `q=1`, then a thin adapter.

## Commit D — multi-fibre contradiction

Use

```text
crossRoof_residual_sum
staircase_heightDrop_gt_pairGain
```

and the two unit residuals. Expected final arithmetic: `omega`.

Output:

```lean
D.multiFiber_impossible ... : False
```

## Commit E — `F.noStrictInterior`

Consume the existing contact and pair-Rees constructors, selected affine
packages, one-fibre/multi-fibre elimination, and expose only

```lean
F.NoStrictInteriorSupport.
```

## Commit F — left `V>1` impossible

One-line consumer of

```lean
F.impossible_of_noStrictInterior.
```

## Commit G — right `V>1` symmetry

Coordinate transport only.

## Commit H — `V=1`

Source-facing coefficient extraction + existing state-free mixed/same
orientation contradiction.

## Commit I — `.pr` wrapper

Consume normalized unit/left/right alternatives.

## Commit J — `.sp/.rq` cyclic relabelling

No cloned staircase proof.

## Commit K — A19 / terminal splice

Consume other-facet impossibility and existing sibling constructors.

## Commit L — public unrestricted HC4 theorem + audits

Only after this commit is green should repository status say HC4 is Lean
verified.

---

# 23. Acceptance checklist

## Left `(1,V)`, `V>1`

```text
[x] staircase classification
[x] locked endpoint/source provenance
[x] primitive highest endpoint/source provenance
[x] contact-oriented singular Rees
[x] pair-degree reverse singular Rees
[x] lowest/highest strict-interior affine packages
[x] endpoint Euler equations
[x] finite staircase extremal ordering
[x] coincident selected layers/profiles coupling
[x] endpoint affine roots coincide in one-fibre branch
[x] three one-fibre diagonal classification
[x] lower one-fibre diagonal impossible
[x] upper one-fibre diagonal impossible
[x] middle one-fibre diagonal impossible
[x] complete one-fibre contradiction
[x] genuine multi-fibre extremal separation
[x] cross-roof arithmetic
[x] state-free cross-roof high-residual terminal theorem
[ ] source-honest exposed roof-transition adapter
[ ] mirrored low-residual theorem/adapter
[ ] complete multi-fibre contradiction
[ ] F.NoStrictInteriorSupport
[x] support equality after NoStrictInteriorSupport
[x] exact four-term/two-function reconstruction
[x] contradiction after NoStrictInteriorSupport
[ ] parent-facing left V>1 impossible theorem
```

## Remaining other-facet cases

```text
[ ] right (V,1), V>1 by symmetry
[ ] V=1 mixed orientation source coefficient extraction
[ ] V=1 same orientation wrapper
[ ] .pr normalized-carrier impossibility
[ ] .sp cyclic relabel to .pr
[ ] .rq cyclic relabel to .pr
```

## A19/global

```text
[x] A19.55 codimension-two -> explicit rank-two geometry
[x] lower .qs outside codimension-two elimination
[x] lower boundary compression to actual other-facet rank-three endpoint
[ ] consume rank-three other-facet impossibility
[ ] route sibling terminal constructors through existing consumers
[ ] prove presented-terminal impossibility without external resolver
[ ] feed it to unrestricted HC4 reducer
[ ] expose public determinant-one gradient injectivity theorem
[ ] full root build at final head
[ ] axiom audit
[ ] proof escape-hatch audit
```

---

# 24. Fresh-context prompt

Use this almost verbatim in a new session:

```text
Continue the unrestricted HC4 final closure from
`docs/HANDOFF_2026-09-15_HC4_FINAL_MULTIFIBER_CLOSURE.md`
on PR #34, branch `final-assembly/a18-4-42-termination-frontier`.

Re-audit the current PR head first and distinguish LEAN VERIFIED,
SOURCE-LANDED / NOT LEAN VERIFIED, PAPER CANDIDATE, DIAGNOSTIC ONLY, and OPEN.
The proof checkpoint underlying the handoff is
`8ea4cd66ec07f00dd2b6597dd3e551afe1cf0b66`, reported fully green.

Do not revive the generic stationary source/profile determinant implication,
do not use the false first-variation degree<=1 shortcut, do not collapse the
strict-low branch to generic JC2, do not identify auxiliary Rees clocks with
the zero blocker, and do not add another global recursion.

The left (1,V), V>1 branch has advanced substantially:

- both endpoint Rees first-variation equations are Lean verified;
- finite-staircase extremal ordering is Lean verified;
- the entire coincident-extrema / one-fibre branch is Lean verified impossible
  (`oneFiber_impossible`);
- hence surviving strict interior is genuinely multi-fibre
  (`extremalPair_lt`);
- `FiniteStaircaseCrossRoofArithmetic.lean` proves the exact roof arithmetic;
- `FiniteStaircaseCrossRoofTerminal.lean` proves state-free that an honest
  exposed cross-roof terminal forces the high-side residual `v=1`.

The immediate task is NOT another determinant recurrence. It is to build the
source-honest exposed-roof transition for the genuine multi-fibre Newton
polygon, adapting the selected exposed cross-roof face to the existing
rank-three terminal certificate. Handle same-roof and central-transition
alternatives honestly rather than assuming a cross-roof edge.

After obtaining high residual v=1, get the mirrored low residual q=1 by line
reversal/coordinate transport if possible, otherwise by a small state-free
mirror theorem. Then `crossRoof_residual_sum` plus
`staircase_heightDrop_gt_pairGain` gives an immediate arithmetic
contradiction. Package this as `multiFiber_impossible`, then prove
`F.NoStrictInteriorSupport` and invoke the already-verified
`F.impossible_of_noStrictInterior`.

Only after the left V>1 branch is closed should you do right (V,1) by symmetry,
V=1 source wrappers, .pr closure, cyclic .sp/.rq relabelling, and the existing
A19/global splice.

Search existing infrastructure before adding any package, especially
PlanarLineSupport, PlanarPrimitiveSlice, RankThreeAffineLineRealisation,
RankThreeAffineLineTerminal, MaximalHessianInitial,
UniqueMaximalInitialMonomial, and the finite-support exposed-face modules.
```

---

# 25. Correct claim at this checkpoint

The correct statement is:

> The unrestricted HC4 project now has a compiled Lean implementation of the
> global entry/termination architecture, the A19.55 codimension-two geometry
> branch, the source-honest rank-three planar/staircase infrastructure, both
> honest endpoint Rees equations, the full one-fibre finite-staircase
> elimination, strict multi-fibre extremal separation, and the hard
> state-free cross-roof terminal algebra. The principal remaining local
> mathematical seam is the source-honest exposed-roof transition for the
> genuine multi-fibre staircase and its mirrored residual. Once that is
> closed, `NoStrictInteriorSupport -> False` is already Lean verified; what
> remains afterward is symmetry/unit/facet wrapping and the existing global
> splice.

This is substantially closer than the previous pair-Rees checkpoint, but it is
not yet a claim that unrestricted HC4 has been proved.
