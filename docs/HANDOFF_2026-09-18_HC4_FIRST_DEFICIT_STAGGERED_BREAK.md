# HC4 unrestricted closure — first-deficit staggered-break handoff

**Date:** 18 September 2026  
**Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`  
**PR:** #34 — `A18.4.42 collapse final termination frontier`  
**Branch:** `final-assembly/a18-4-42-termination-frontier`  
**Substantive source checkpoint for this handoff:** `f735921c6f994f1854e155056d55332de62ee165`  
**Exact-head Lean CI:** run `35339770347` (run #3013; status must be checked before promoting SOURCE-LANDED items below to LEAN VERIFIED)

This handoff supersedes `HANDOFF_2026-09-17_HC4_FINAL_GLOBAL_ASSEMBLY.md` as the
live continuation point.  The older handoff remains useful provenance, but its
claim that the remaining task is primarily a global-successor splice is no
longer the best closing route.

The current branch has returned to the provenance-rich strict-low source and
has formalised a substantially sharper local chain.  The live endpoint is now:

```text
left non-unit .pr finite staircase
        |
        v
central source monomial with deficits (0,0)
        |
        v
source-honest total-deficit reverse Rees family
        |
        v
first positive total-deficit layer
        |
        v
binary Hessian singularity
        |
        v
binary Hesse linear-power rigidity
        |
        v
adjacent-deficit exclusion
        |
        v
pure-axis binary first layer
        |
        v
one honest source monomial on one roof
        |
        v
honest rank-three active roof block at order q
        |
        v
least later source monomial opening the missing deficit coordinate
        |
        v
FIRST DEFICIT OPPOSITE OPENING   <-- LIVE ENDPOINT
```

The immediate next theorem should package this chronology into the already
written generic staggered first-kernel-break theorem.

---

## 1. Status vocabulary

Use these labels literally.

- **LEAN VERIFIED** — accepted by a stated successful exact-head Lean build.
- **SOURCE-LANDED / NOT LEAN VERIFIED** — committed source whose relevant
  exact-head full build has not yet been certified.
- **PAPER CANDIDATE** — paper mathematics is available but not formalised.
- **DIAGNOSTIC ONLY** — useful symbolic/counterexample evidence, not a theorem.
- **OPEN** — a genuine mathematical/formal/assembly obligation remains.

Do not call a theorem green merely because its source exists.

At the time this handoff source was written, run `35339770347` was the
certification run for `f735921c...`.  Check that run first.  If its full
`Build HC4`, axiom audit, negative control, and escape-hatch audit all pass,
then the source-landed modules listed in Sections 4–7 may be promoted to
**LEAN VERIFIED** together.

---

## 2. Public target and already-existing final reducer

The public target remains:

```lean
F : MvPolynomial (Fin 4) K
hdet : HC4.Polynomial.hessianDeterminant F = 1
⊢ Function.Injective (mvGradientMap F)
```

with the ambient assumptions already used by the A19 front door:

```lean
[K : Type u] [Field K] [CharZero K] [IsAlgClosed K]
```

The preferred final reduction is already present:

```lean
gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
```

in

```text
HC4/Valuation/AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean
```

It reduces unrestricted determinant-one gradient injectivity to impossibility
of the **actually reachable** complexity-zero presented terminal while
retaining the canonical

```lean
state.repair = rankOneRepairState 0
```

provenance.

Do not regress to the stronger older reducer asking for impossibility of every
arbitrary presented terminal unless necessary.

---

## 3. Important correction to the 17 September global-progress handoff

The following infrastructure is real and useful:

```text
zero strict-low rank-one reached state
        ->
zero-defect rank-two geometry
        ->
global macro progress
        ->
rank-three repair-labelled continuation
```

including the source-facing Rees descent work.

However, this is **not by itself a contradiction**.

The repository's own soundness guard proves why: changing only the repair tag
does not change the polynomial family, section, raw defect, or collision.
In particular `rankThreeRepairState 0` is the bottom of the repair bookkeeping
ladder, and declaring it impossible from the label alone would be unsound.

Therefore:

- keep the global-progress infrastructure;
- do **not** use `withRepairOnly` as the final contradiction;
- do **not** claim that generic zero-defect rank-three geometry proves HC4;
- prefer the provenance-rich local strict-low chain below.

---

## 4. State-free algebra introduced in the present sprint

### 4.1 Joint codimension-two departure

File:

```text
HC4/Polynomial/CodimensionTwoNonhomogeneousJointDeparture.lean
```

Key exact coefficient:

```text
[X^2] det(C M(p,0,0,r) + X A M(a,m,n,b))
  =
A^2 C^2 m n p r (m+n-1)(p+r-1).
```

The helper theorem rules out a genuinely joint departure in the corresponding
two-term singular pencil under the expected positive/nonzero hypotheses.

The first version landed at:

```text
e6a83762106eee3bfa1909de72643e235fc08274
```

and passed the full CI/audit suite at that checkpoint.

### 4.2 Separated codimension-two departures

File:

```text
HC4/Polynomial/CodimensionTwoNonhomogeneousSeparatedDeparture.lean
```

Key coefficient:

```text
[X^2] det(
  C M(p,0,0,r)
  + X (A M(a,0,m,b) + B M(c,n,0,d))
)
=
- A B C^2 m n p r (m-1)(n-1)(p+r-1).
```

The initial version landed at:

```text
07031af9c152112f34860f8acc8ada66e6934410
```

and passed the full CI/audit suite at that checkpoint.

These state-free formulas are useful diagnostics and reusable algebra, but the
live proof no longer needs to pretend that a two- or three-term
**subpolynomial** of the source is singular.  The source-honest total-deficit
family below is stronger.

### 4.3 Rank-two kernel second variation

File:

```text
HC4/Polynomial/RankTwoKernelSecondVariation.lean
```

The central exact identity is:

```text
second variation of det at rank-two (0,3) base
  =
2 * det(active (0,3) block) * det(first-layer (1,2) block).
```

The arbitrary second-order correction layer disappears identically.

The initial matrix theorem at

```text
f00d7b3ae64a2df9f6227600de52133a48da9516
```

passed the full CI/audit suite.

The file has since gained a polynomial-family gap bridge so a complete source
family may be retained rather than truncated.

---

## 5. Source-honest central total-deficit family

File:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitRees.lean
```

Let `P.carrier` be the actual source-honest planar carrier in the left
`(1,V)`, `V>1` branch.  It already lies on a positive integral source
weight `W).

The new weight lowers exactly the two deficit coordinates by one:

```text
W' = (W0, W1-1, W2-1, W3).
```

Because every carrier monomial lies on the same original `W)-level, the
bounded reverse-Rees order becomes exactly:

```text
order(e) = e1 + e2.
```

The file defines:

```lean
centralDeficitWeight
centralDeficitLevel
centralDeficitFamily
```

and proves, in particular:

```lean
centralDeficit_order_eq
centralDeficitFamily_layer_mem_iff
centralDeficitFamily_hessian_zero
centralDeficitFamily_layer_zero_eq
centralDeficitFamily_hasPositiveActualLayer
```

Thus:

- parameter layer zero is the actual central monomial;
- every positive layer is selected from actual source support by total deficit;
- the complete family remains Hessian-singular;
- the construction introduces no blocker clock and no repair transition.

This is the source-honest replacement for trying to declare an arbitrarily
chosen sparse subpencil singular.

---

## 6. First positive total-deficit layer

### 6.1 Binary Hessian singularity

File:

```text
...PrVGreaterOneCentralFirstLayerHessian.lean
```

Definitions/theorems include:

```lean
firstDeficitOrder
firstDeficitLayer
firstDeficitBinaryFace
firstDeficitOrder_pos
firstDeficitLayer_ne_zero
firstDeficitLayer_support
firstDeficitLayer_deficit_injective
firstDeficitBinaryFace_ne_zero
firstDeficitBinaryFace_isHomogeneous
binaryParameterHessian
centralBinaryCore
centralBinaryCore_activeDet_ne_zero
firstDeficitBinaryFace_hessian_zero
```

The logic is:

1. move the Rees parameter outside the source variables;
2. specialise source coordinates
   `(x0,x1,x2,x3) -> (1,U,V,1)`;
3. retain the whole source family;
4. use the rank-two second-variation gap theorem;
5. conclude the honest first positive binary deficit face has zero binary
   Hessian determinant.

This is **not** the old false stationary source/profile determinant
comparison.

### 6.2 Binary Hesse rigidity + staircase arithmetic

File:

```text
...PrVGreaterOneCentralFirstLayerLinearPower.lean
```

Key theorems:

```lean
firstDeficitOrder_two_le
firstDeficitBinaryFace_eq_linearPower
firstDeficitLinearPower_not_both_nonzero
firstDeficitBinaryFace_pureAxis
```

The binary Hesse theorem yields:

```text
firstDeficitBinaryFace = a * L^D.
```

If both coefficients of `L` are nonzero, its support contains adjacent binary
deficit exponents.  The source projection is coefficient-faithful and the
finite-staircase chord theorem forbids adjacent deficit pairs.  Hence `L`
uses only one binary variable.

This is where the existing source-facing theorem

```lean
QsOtherFacetPrLeftVContactFrontierData.no_adjacent_deficits
```

is essential.

### 6.3 Axis support and singleton source layer

Files:

```text
...PrVGreaterOneFirstDeficitAxis.lean
...PrVGreaterOneFirstDeficitSingleton.lean
```

Key endpoint:

```lean
firstDeficitLayer_singleton_axis
```

The honest first source layer is exactly one monomial, with one of:

```text
(e1,e2) = (D,0)
or
(e1,e2) = (0,D),
```

where

```text
D = firstDeficitOrder >= 2.
```

The theorem

```lean
firstDeficitLayer_eq_monomial_axis
```

keeps its actual nonzero source coefficient.

---

## 7. The first layer opens rank two to rank three

Files:

```text
HC4/Polynomial/RankTwoToRankThreeRoofLinearCoefficient.lean

HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitRankThree.lean

HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitRankThreeRoof.lean
```

The active source roofs are the coordinate triples:

```text
(0,1,3)
and
(0,2,3).
```

The singleton first deficit monomial has exponent at least two in its active
deficit coordinate.  Together with the nonzero central `(0,3)` minor, the
first coefficient of the relevant three-by-three Hessian determinant is
nonzero.

The provenance-rich package is:

```lean
FirstDeficitRankThreeRoofGeometry
```

and the compact endpoint is:

```lean
firstDeficit_activeRankThree
```

which yields:

```lean
G.firstDeficitLeftActiveHessian.det ≠ 0
∨
G.firstDeficitRightActiveHessian.det ≠ 0.
```

More sharply, each orientation has a theorem that the determinant's coefficient
at `firstDeficitOrder` is nonzero, while all earlier positive coefficients
vanish.

So the central rank-two special fibre has now honestly become rank three at
the first positive total-deficit order.

---

## 8. Current live endpoint: first later opening of the missing coordinate

File:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitOppositeOpening.lean
```

The original carrier still contains both honest roof endpoints:

```lean
locked_yRoof_mem
highest_zRoof_mem
```

Therefore a first layer on one deficit axis cannot be the whole source.

The file selects the least later carrier monomial which opens the other
deficit coordinate.

The exact package is:

```lean
inductive FirstDeficitOppositeOpening
```

with two orientations.

For example, in the left constructor:

```text
first:
    first e1 = q
    first e2 = 0

opposite:
    opposite e2 > 0
    q < opposite.e1 + opposite.e2
    opposite is minimal in total deficit among all points with e2 > 0
```

and symmetrically on the right.

The endpoint theorem is:

```lean
firstDeficit_oppositeOpening
```

This is the **current live continuation point**.

There is currently no downstream `FirstDeficit...Closure` module consuming
this package.

---

## 9. The generic theorem that should consume the live endpoint

File:

```text
HC4/Valuation/StaggeredSingularFirstKernelBreakRankTwo.lean
```

This file was written for exactly the chronology now present.

Its header assumes:

```text
active 3x3 determinant:
    zero below q
    nonzero at q

remaining kernel row:
    zero below j

q < j

full 4x4 determinant:
    identically zero

actual kernel-row break:
    at order j
```

and packages this as:

```lean
StaggeredSingularFirstKernelBreakFourBlockData
```

The conclusions are:

```lean
kernelDiagonal_coeff_kernelOrder_eq_zero
mixed_coeff_ne_zero
exists_nonzero_principalMinor_at_kernelOrder
```

The determinant coefficient at order `q+j` is source-honest: quadratic
kernel-row terms start at order at least `2j`, so because `q<j` the only
linear contribution is

```text
activeThree_q * kernelDiagonal_j.
```

Since the full determinant is zero and `activeThree_q != 0`, the diagonal
kernel coefficient at `j` is zero.  Hence an actual kernel break at `j`
must be mixed and yields a concrete nonzero principal `2x2` Hessian minor.

### Immediate next module

Create a thin A19 adapter, suggested name:

```text
HC4/Valuation/
AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitStaggeredBreak.lean
```

Its job should be to construct

```lean
StaggeredSingularFirstKernelBreakFourBlockData
    (MvPolynomial (Fin 2) K)
```

or the equivalent coefficient ring naturally used by the existing
binary-parameter Hessian.

Do not reprove the staggered determinant algebra.

### Data mapping to establish

For each orientation of `FirstDeficitOppositeOpening`:

1. **block**  
   Build/reindex the complete honest `binaryParameterHessian G` as a
   `GeneralFourBlock` with the already-active three coordinates first and
   the missing coordinate as the last/kernel coordinate.

2. **activeOrder = q**  
   Use `G.firstDeficitOrder`.

3. **activeOrder_pos**  
   Use `firstDeficitOrder_pos`.

4. **active determinant lower zero**  
   Use the exact first-deficit gap theorem for the appropriate active roof
   determinant.

5. **active determinant coefficient nonzero at q**  
   Use:
   ```lean
   firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
   ```
   or
   ```lean
   firstDeficitRightActiveHessian_det_coeff_first_ne_zero.
   ```

6. **kernelOrder = j**  
   Use the total deficit of the selected `opposite` monomial:
   ```text
   j = opposite 1 + opposite 2.
   ```

7. **q < j**  
   This is stored directly as `order_strict`.

8. **kernel row lower zero below j**  
   This is the most important adapter obligation.  Prove it from:
   - minimality of the selected opposite-opening support point;
   - the exact layer-support theorem
     `centralDeficitFamily_layer_mem_iff`;
   - source-coordinate derivative semantics.

   Do not merely argue that the source polynomial lacks such monomials:
   state the precise coefficient-vanishing theorem for all four entries of
   the missing Hessian row.

9. **full determinant zero**  
   Use the complete source-honest family:
   ```lean
   centralDeficitFamily_hessian_zero
   ```
   transported through the parameter-first/binary specialisation and the
   chosen coordinate permutation.

10. **kernel break at j**  
    The actual opposite monomial has a positive exponent in the missing
    deficit coordinate and nonzero source coefficient.  Prove that at least
    one Hessian entry in the missing row is nonzero at order `j`.
    This is the second genuinely source-facing adapter obligation.

Then apply:

```lean
exists_nonzero_principalMinor_at_kernelOrder
```

to obtain an honest later coefficient-layer rank-two minor.

---

## 10. What happens after the staggered break?

Do not decide this by repair bookkeeping.

There are two legitimate possible exits, to be audited after the staggered
adapter compiles.

### Exit A — local staircase contradiction

Use the exact exponent/arithmetic data of the selected opposite monomial and
the new nonzero principal minor to force an exponent condition incompatible
with the finite-staircase chord/minimality.

This would be the cleanest local closure if available.

### Exit B — honest kernel inflation / strict restart

Recent infrastructure now includes:

```text
HC4/Valuation/KernelInflationHessianDefect.lean
HC4/Valuation/ExactKernelDefectDrop.lean
```

The latter proves, for a **whole polynomial family** satisfying the exact
integral kernel-blowup hypotheses:

```lean
hessianDeterminant_integralKernelBlowup_eq_zero
two_mul_slope_le_of_integralKernelBlowup
integralKernelBlowup_hasHessianDefect_sub
integralKernelBlowup_positiveKernelDefectDrop
integralKernelBlowup_exactDefect_and_strictRestart
```

This is a valid global progress route only if the A19 source package can
supply:

- the actual family, not a detached coefficient layer;
- positive kernel slope;
- integral kernel coefficient divisibility;
- exact collision;
- distinct transformed special points;
- the exact source/target defect equations.

Do **not** feed an auxiliary singular carrier layer into this theorem and call
it a global restart without these adapters.

---

## 11. Recent build regression and repair history

Several exploratory commits briefly made the branch red while this chain was
being assembled.  These were compiler/interface issues, not mathematical
counterexamples.

### Kernel-inflation duplicate ownership

`KernelInflationHessianDefect.lean` gained canonical declarations:

```lean
kernelInflateHom_monomial
coeff_kernelInflateHom
kernelInflateHom_injective
```

but `ExactKernelDefectDrop.lean` temporarily redeclared the same names.

That produced duplicate-declaration errors.

The duplicates have been removed from `ExactKernelDefectDrop.lean`; generated
inventory now assigns those names only to
`KernelInflationHessianDefect.lean`.

### `coeff_kernelInflateHom` negative-support proof

The source proof initially expanded `Q.as_sum` before using
`coeff d Q = 0`, leaving no literal `coeff d Q` occurrence to rewrite.

Commit:

```text
4d0dae6aa69a82147542bbbb853c872387658177
```

reordered the proof so the RHS is zeroed before the support expansion.

### Multiplication-order compatibility

The canonical coefficient theorem has the form

```text
coeff(inflate Q,d) = coeff(Q,d) * scale(d),
```

where an older duplicate used the commuting factor in the opposite order.

`SeparatedRightWallScaleDescent.lean` therefore had one stale
`mul_zero` rewrite.  Commit:

```text
f735921c6f994f1854e155056d55332de62ee165
```

changes it to `zero_mul`.

### Comment-only syntax accident

A comment-only CI trigger briefly closed a module doc comment too early.
Commit `a4b7c2ae...` repaired that syntax before the multiplication-order
compatibility fix above.

None of these changes alters the HC4 mathematics.

---

## 12. Hard prohibitions

The following remain binding.

1. **Do not identify clocks.**  
   Total-deficit Rees order, auxiliary ray order, Smith/blocker clock, and raw
   Hessian defect are distinct unless an explicit theorem identifies them.

2. **Do not use naked repair promotion as contradiction.**  
   `withRepairOnly` does not change the source family.

3. **Do not revive the generic stationary source/profile determinant
   implication.**  
   It is false in that generality.

4. **Do not revive the generic degree-`<=1` shortcut.**  
   The known `phi=(5+4T)^2` counterexample remains relevant.

5. **Do not make a sparse subpolynomial singular by deletion.**  
   Use an honest initial form, Rees layer, determinant coefficient, or other
   justified source operation.

6. **Do not collapse this branch to generic JC2.**  
   The live branch retains stronger source/contact/staircase provenance.

7. **Do not infer a superface is singular because a smaller face is singular.**

8. **Do not create another termination measure.**  
   The existing raw-defect rank-one termination architecture owns global
   recursion.

---

## 13. Final critical path to unrestricted HC4

The shortest currently justified route is:

```text
A. exact-head CI green
        |
B. FirstDeficitOppositeOpening
        |
C. source-facing adapter to
   StaggeredSingularFirstKernelBreakFourBlockData
        |
D. nonzero later principal Hessian minor
        |
E. consume that minor:
     local staircase contradiction
     OR honest strict restart
        |
F. eliminate left V>1 central survivor
        |
G. use already-landed finite-staircase/cross-roof/one-fibre closures
   and existing symmetry/orientation adapters
        |
H. strict-low presented terminal impossible
        |
I. gradient_injective_of_hessianDeterminant_one_of_
   reachablePresentedTerminal_impossible
        |
J. public unrestricted theorem in root assembly
        |
K. add final theorem to HC4/Audit.lean
        |
L. full exact-head:
     Build HC4
     + axiom audit
     + negative control
     + escape-hatch audit
```

Do not update the public claim to “unrestricted HC4 proved” before steps I–L
are literally present and certified.

---

## 14. Recommended immediate work order for a fresh session

1. Re-audit PR #34 head and current CI.
2. Search before adding any new generic determinant lemma.
3. Open:
   ```text
   ...FirstDeficitRankThreeRoof.lean
   ...FirstDeficitOppositeOpening.lean
   StaggeredSingularFirstKernelBreakRankTwo.lean
   ```
4. Implement only the source-facing staggered adapter.
5. Compile that module before adding another abstraction layer.
6. Once `exists_nonzero_principalMinor_at_kernelOrder` is available on the
   actual A19 source, audit the shortest honest consumer.
7. Only after local strict-low contradiction is green should final global/root
   assembly be edited.

A useful fresh-session prompt is:

> Continue unrestricted HC4 from
> `docs/HANDOFF_2026-09-18_HC4_FIRST_DEFICIT_STAGGERED_BREAK.md`.
> Re-audit the current PR #34 head and exact-head CI first.  Treat only
> certified builds as Lean verified.  The live local endpoint is
> `firstDeficit_oppositeOpening`; construct the source-facing adapter to
> `StaggeredSingularFirstKernelBreakFourBlockData`, using the existing
> first-deficit rank-three roof coefficient and the minimal later
> opposite-opening monomial.  Do not use repair bookkeeping, generic JC2,
> the failed stationary determinant comparison, or a singular-subpencil
> shortcut.

---

## 15. One-line status

The proof is no longer stuck at generic zero-defect rank-three bookkeeping.
The provenance-rich left nonunit finite staircase has been reduced to an
honest **rank-three-at-order-`q`, opposite-kernel-opening-at-later-order-`j`**
configuration.  The repository already contains the generic staggered
first-kernel-break theorem for exactly this situation.  The immediate
substantive task is therefore a narrow source-facing adapter, followed by
consumption of the resulting nonzero later principal Hessian minor and then
the final reachable-terminal/public HC4 splice.
