# Quadratic transverse-cap endpoint: source-honest paper derivation

**Date:** 2026-10-09  
**PR:** #36, `research/canonical-square-gap-obstruction`  
**Status:** **PAPER CANDIDATE — NOT A LEAN THEOREM OR TERMINAL CLOSURE**.

This note isolates a possible *direct contradiction* for the reachable pure-longitudinal E3 case
`r = topFace.degree - firstActualLayerOrder = 2`. It must not be used as a Lean
hypothesis, final-resolution constructor, or reason to mark JC2 ⇒ HC4 complete.

## 1. Source-honest statement to prove

Let K be a characteristic-zero field and let
`F ∈ K[x,y₁,y₂,y₃]` have transverse degree at most two. Suppose

1. `det Hess(F) = 1`, and
2. `∇F(0,0) = ∇F(1,0)`.

Then these conditions are inconsistent.

This applies to the **same represented source**
`T.topKernelReesSource`, not to a new quadratic approximant: the existing
`pureLongitudinal_markedAxis_firstActual_sourceWeightBound` supplies the
literal transverse cap 2, and the existing represented-source marked-axis
collision supplies (2). The first-actual quotient equality identifies the
lower face exactly, so no new endpoint-producer hypothesis is introduced.

The proof below is over K; the algebraic-closure hypothesis used by the E3
wrapper is not needed for the proposed local lemma.

## 2. Exact quadratic expansion

Write `x = x₀`, `y=(x₁,x₂,x₃)^T`, and

```text
F(x,y) = a(x) + b(x)^T y + (1/2) y^T C(x) y,
```

where `a ∈ K[x]`, `b ∈ K[x]^3`, and
`C ∈ Sym₃(K[x])`. The fractions are legitimate in characteristic zero.

Let `v=b'(x)`. The Hessian is

```text
H(F) = [ a''+b''·y+(1/2)yᵀ C'' y    vᵀ+yᵀ C' ]
       [     v+C' y                     C      ].
```

The collision is **exactly**

```text
a'(1)=a'(0),       b(1)=b(0).
```

The determinant identity is

```text
1 = det(C) (a''+b''·y+(1/2)yᵀ C'' y)
    - (v+C'y)ᵀ adj(C) (v+C'y).                 (★)
```

This identity is polynomial, uses no inverse, and should be the first Lean
target using the existing `GeneralFourBlock` and `GeneralThreeBlock`
determinant machinery.

## 3. Rank ≤ 1 is excluded

Over `K(x)`, if `rank C ≤ 1`, both `det C` and `adj C` vanish.
Then (★) gives `1=0`. Therefore the transverse block has generic rank
either 2 or 3. The new finite principal-pivot lemma is compatible with this,
but rank at an individual origin point is not being confused with generic rank.

## 4. Generic rank 2: a constant kernel forces nonzero drift

Assume `rank_{K(x)} C=2`. Over the rational-function field,
`adj C = λ u uᵀ` for a nonzero kernel vector `u` and `λ≠0`.

Since `det C=0`, (★) says

```text
-λ (uᵀ(v+C'y))² = 1.
```

Its constant coefficient gives `uᵀv≠0`; its terms linear in `y`,
using `char K ≠ 2`, force `uᵀ C'=0`. Symmetry gives `C'u=0`.
Differentiate `Cu=0` to get `Cu'=0`. The rational kernel is
one-dimensional, so `u'=μu`. Ratios of nonzero coordinates of `u`
therefore have zero derivative; in characteristic zero the constant field
of `K(x)` is K. Hence this kernel line is spanned by a **constant**
nonzero `u₀ ∈ K³`, with `C(x)u₀=0`.

Consequently `adj C = γ(x)u₀u₀ᵀ`. As `adj C` has entries in `K[x]`
and at least one coordinate of `u₀` is nonzero, `γ∈K[x]`.
The constant term of (★) becomes

```text
-γ(x) (u₀ᵀ b'(x))² = 1   in K[x].
```

The only units in `K[x]` are nonzero constants, so
`u₀ᵀ b'(x)=c∈K×`. Thus

```text
u₀ᵀ (b(1)-b(0)) = c ≠ 0,
```

contrary to the collision.

## 5. Generic rank 3: inverse Hessian is affine and drift is unipotent

Assume `det C≠0` in `K[x]`; work provisionally in `K(x)`.
Comparing quadratic and linear coefficients of `y` in (★) gives

```text
C'' = 2 C' C⁻¹ C',
b'' = 2 C' C⁻¹ b'.                              (†)
```

Set `M=C⁻¹`. Differentiation of the inverse yields

```text
M'' = 2M C' M C' M - M C'' M = 0.
```

In characteristic zero, each rational entry with second derivative zero
is affine. Hence `M=A+xB` for constant matrices `A,B∈M₃(K)`.
Since `M C=I` over `K[x]`, the two polynomial determinants multiply to 1:
`det C` is a nonzero constant and `A=M(0)` is invertible.

Let `N=A⁻¹B`. Then

```text
M=A(I+xN),    C=(I+xN)⁻¹ A⁻¹,
det(I+xN)=1.
```

Cayley–Hamilton gives `N³=0` (all nonconstant coefficients of the
characteristic polynomial of N vanish). Put `S=I+xN`.
Equation (†) implies

```text
v' = -2 S⁻¹ N v,
(S² v)' = 0.
```

Thus `S² v=v₀`, a constant vector; and, since `N³=0`,

```text
v=b'=(I-2xN+3x²N²)v₀.
```

Taking polynomial antiderivatives between 0 and 1 gives

```text
b(1)-b(0)=(I-N+N²)v₀.
```

The factor is invertible: `(I-N+N²)(I+N)=I+N³=I`.
Collision forces `v₀=0`, hence `b'=0`. Evaluating (★) at `y=0`
now gives `det(C)a''=1`. Since `det C∈K×`, `a''` is the nonzero
constant `1/det C`, contradicting `a'(1)=a'(0)`.

## 6. Formalisation milestones and hard boundaries

1. Prove the exact polynomial block identity (★) with its three
   coefficient consequences. Use a transverse-degree-`≤2`
   decomposition of the **represented source**, not an existential
   replacement potential.
2. Establish the generic-rank split over `K(x)` and the rank-2
   constant-kernel argument, including the `K[x]` unit step.
3. Establish `M''=0`, the nilpotent `3×3` matrix identity, and the
   polynomial-antiderivative drift contradiction for rank 3.
4. Expose `r=2 → False` on
   `PureLongitudinalMarkedE3Data` without any new extractor field.
5. **Separately** resolve the remaining `r≥3` pure-longitudinal cases,
   source-constant-three-by-three event, and exact-closing event before
   attempting the final JC2 ⇒ HC4 assembly.

**Verification:** This is presently a paper argument, not a Lean-certified
proof. The rank-one origin witness, the finite principal-pivot Lean adapter,
and the existing E3 fields are *inputs*; they do not by themselves establish
any of the three final-resolution constructors. The newly pushed Lean edits
require a local `lake build`; GitHub's documentation-only `generate`
workflow does not test Lean.

## 7. Follow-up formal algebra packet (2026-10-10; new commits unverified)

The rank-two case now has a shorter source-honest route than the square-factor
argument of §4. Set
`v=b'(x)`, `w=adj(C)v`. When `det C=0`, the constant term of
the exact four-block determinant equation gives **`v·w=-1`** and
the adjugate equation gives **`Cw=0`**. In addition the coefficient
linear in the transverse variables gives `C'w=0`. Differentiating
`Cw=0` therefore gives **`Cw'=0`**.

The already-proved actual transverse rank-two witness supplies a nonzero
2x2 minor; the new finite principal-pivot packet supplies one after at most
one transverse shear. The two-row domain identity then forces
`w_i w'_j=w_j w'_i`. Since `∑ w_i v_i=-1`, we may write

```text
s = ∑ v_i w'_i
w'_j = -s w_j.
```

Consequently `w_j` divides `w'_j` in `K[x]`. By the existing
mathlib `Polynomial.dvd_derivative_iff`, each `w'_j=0`.
Now `B=∑ w_j b_j` has derivative `B'=-1`, contrary to
`b_j(1)=b_j(0)`. **No rational kernel-vector constant-field
classification or square-factor argument is needed.**

New Lean declarations (subject to local verification):

- `quadraticTransverse_singularThreeBlock_unimodularKernel`:
  the exact commutative-ring `adj(C)v` Schur certificate.
- `quadraticTransverse_twoRowPrincipalKernel_wedges`:
  nonzero principal 2x2 pivot + two shared kernel rows ⇒ all
  three kernel wedges vanish over an integral domain.
- `polynomial_unimodularKernel_derivative_eq_zero`:
  unimodularity and wedge zero ⇒ the polynomial kernel vector is constant.
- `quadraticTransverseCap_rankTwo_principalKernelCollision_impossible`:
  assembles the latter two algebraic steps and exact marked collision.
- `cubicNilpotent_drift_smul_injective`:
  generic-rank-three interval drift factor is injective on any left module.

**Remaining source-honest extraction:** expand the *actual represented
source* to transverse quadratic normal form; transport the exact
determinant-one identity as a polynomial identity in the longitudinal
coordinate and three transverse variables; extract its constant/linear/
quadratic transverse coefficients. Show the marked collision gives exactly
`b_i(1)=b_i(0)`. In the rank-two branch, instantiate the adjugate
certificate and prove `C'w=0`, hence the differentiated kernel-row
conditions; combine with the previously proved rank-two witness and fixed
principal pivot. In the rank-three branch, prove `(C^{-1})''=0`, then
the nilpotent interval normal form and apply the module drift lemma.

The **quadratic case is not closed yet**. These algebraic lemmas do not
construct an `AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution`.
The `r≥3` pure branch and other E3 endpoint events remain open.
Both the targeted E3 build and the root `lake build` must pass at the
new commit before calling the edits Lean-certified.


## 8. Actual represented-source adapter and five-section rank-two endpoint (2026-10-10; unverified build)

New modules imported through `AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3FinalResolution`:

1. `QuadraticTransverseCapSourceMarkedCollision.lean` directly consumes
   `T.topKernelReesSource_exactCollision` and the **existing**
   `longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision`
   to obtain the three exact polynomial equalities
   `b_i(1)=b_i(0)` of the *original represented source*.
2. `QuadraticTransverseCapSourceSupport.lean` consumes the **same
   represented source's** quadratic marked-axis reverse-weight bound,
   and shows `longitudinalCoefficientPolynomial b c d F=0` whenever
   `b+c+d≥3`. This is the all-longitudinal-orders transverse cap,
   not merely a graded quadratic first face.
3. `QuadraticTransverseCapSchurOddCancellation.lean` gives an exact
   ring identity for the *difference* of the Schur determinant cores at
   opposite transverse sections. For `det C=0` and unit determinants
   at the two sections, the mixed pairing
   `(C'e_i)·adj(C)b'=0`. The two longitudinal Hessian entries need
   **not** be equal and cancel because they multiply `det C=0`.
4. `QuadraticTransverseCapRankTwoOppositeSections.lean` packages the
   **complete polynomial rank-two algebra** with only five Schur-unit
   equations (axis, ±e₁, ±e₂), generic transverse determinant zero,
   one actual leading principal 2x2 pivot, and the real marked
   collision. The theorem constructs `w=adj(C)b'`, derives
   `Cw=0`, `C'w=0`, differentiates to `Cw'=0`, invokes the
   principal-pivot wedge identity, and concludes the nonzero drift
   contradicts `b(1)=b(0)`. No generic rank-two endpoint is assumed.

Still open in the **actual E3 quadratic source**: provide the
canonical polynomial block `C(x)` and `b(x)` from longitudinal
coefficients; relate the five four-block Schur identities exactly to
`hessianDeterminant T.topKernelReesSource = 1`; transport one of the
six fixed principal pivot alternatives into the source coordinates
(with shear when required); split rank-two `det C=0` from rank-three
`det C≠0`; formalize the rank-three reciprocal-matrix ODE and
nilpotent polynomial drift. No producer-free JC2⇒HC4 theorem
is yet derived by these intermediate constructions.

New declarations remain **unverified until a local Lean build**.


## 9. Original-source longitudinal sections and singular principal pivot (2026-11-10; new code unverified)

The source-honest adapter has advanced in three distinct, formal targets:

- `QuadraticTransverseCapSourceAxisSchur.lean` constructs the actual
  four-block Hessian over `K[x]` by applying the pre-existing
  `longitudinalAxisRestrictionRingHom` to the actual source
  `hessian F`. Its `quadraticTransverseCapSource_axisSchur_unit`
  transports `hessianDeterminant F=1` and identifies the three
  mixed row entries **exactly** as `b_i'(x)`.
  This discharges the **axis** unit Schur equation, without a
  replacement source.
- `QuadraticTransverseCapSourceSections.lean` extends that
  ring-hom determinant transport to **any constant transverse
  section** `y\in K³`. In particular all four sections `±e₁, ±e₂`
  retain the exact determinant-one Hessian over `K[x]`.
  **Still to prove:** under the actual transverse degree cap,
  the 3x3 section Hessian is the same `C(x)` and the mixed entries
  become `b'(x)±C'(x)e_i`. The unit determinant equations for
  raw section blocks do not automatically discharge the normalized
  Schur identities of the opposite-section endpoint.
- `QuadraticTransverseCapSourceOriginPivot.lean` identifies the
  x=0 specialization of the six entries of the **polynomial**
  transverse block with the existing represented-source origin
  Hessian; hence the source-origin 2x2 witness lifts to a
  nonzero polynomial 2x2 minor of `C(x)`. The actual E3 wrapper
  is `quadratic_sourceAxisPolynomialRankTwo`.

**New algebraic simplification in the singular branch:**
For `det C=0` over a domain, every nonzero 2x2 minor of a
symmetric 3x3 block implies a nonzero **principal** 2x2 minor, with
no source shearing required. The three exact square identities are:

```text
(bf-ce)^2 = (af-c^2)(df-e^2) - f det(C)
(be-cd)^2 = (ad-b^2)(df-e^2) - d det(C)
(ae-bc)^2 = (ad-b^2)(af-c^2) - a det(C)
```

If all three principal minors vanished, these identities and `det C=0`
would force all mixed minors to vanish, contrary to source rank >=2.
This is isolated in
`QuadraticTransverseCapSingularPrincipalPivot.lean` and consumed
by `PureLongitudinalMarkedE3Data.quadratic_sourceSingularPrincipalPivot`.

**Important caveat:** The algebraic five-section rank-two endpoint
currently selects the principal `(0,1)` transverse pivot `ad-b²`.
The singular principal-pivot theorem gives a **three-way** alternative
`df-e² !=0 ∨ af-c² !=0 ∨ ad-b² !=0`. We must either permute
the transverse coordinates honestly or derive the derivative-kernel
rows at **all three pairs** `±e_i` (seven sections including the axis)
and use the appropriate two rows. Never treat a generic principal
pivot as if it were already the `ad-b²` pivot.

The rest of the source adapter, the generic rank-three analysis, the
higher transverse-cap branches, and a producer-free `JC2 → HC4`
conclusion remain open. The newly added code has **not yet been
Lean-compiled locally** as of this note.


## 10. New singular-quadratic source closure (2026-11-10; LOCAL BUILD REQUIRED)

A more substantial proof chain now lies on the **actual canonical E3
import path**. The newly written theorem

`PureLongitudinalMarkedE3Data.quadratic_sourceTransverseDet_ne_zero`

asserts that at the reachable pure quadratic relevel `r=2`, the
transverse Hessian three-block

```text
C(x) = Hessian_{transverse,transverse}
       (T.topKernelReesSource)(x,0,0,0)
```

has **nonzero polynomial determinant**. This is stronger than the previous
source-origin rank-two witness. It is derived without assuming a new
final-resolution constructor, abstract endpoint producer, or fabricated
source, but must **pass Lean compilation** before being called certified.

The source-honest singular branch follows this precise chain:

1. `QuadraticTransverseCapThreePrincipalKernel.lean` handles **all
   three original principal 2x2 pivots**, by finite index permutations
   of the already-green two-row kernel theorem.
2. `QuadraticTransverseCapSevenSectionEndpoint.lean` combines the axis
   and all six opposite-section Schur equations to give the exact
   rank-two drift contradiction independently of pivot placement.
3. `QuadraticTransverseCapSourceHessianFlat.lean` proves the real
   cap-two source has zero third transverse partials. Therefore the
   transverse Hessian block is the same **polynomial C(x)** on every
   constant transverse section; the proof uses source support and
   the existing characteristic-zero evaluation-independence lemma.
4. `QuadraticTransverseCapAffineSection.lean` proves the exact
   affine-evaluation identity for any polynomial whose second
   partial derivative in one coordinate vanishes, using
   `P-X_i ∂_iP` and the existing evaluation-independence lemma.
5. `QuadraticTransverseCapSourceMixedSections.lean` applies that
   identity to the actual mixed Hessian, whose second transverse
   derivative vanishes by the cap-two source condition and commuting
   longitudinal with transverse formal derivatives.
6. `QuadraticTransverseCapSourceSchurProfile.lean` identifies the
   source-axis coefficient vector `b(x)`, transverse Hessian
   matrix `C(x)`, and actual mixed section row:
   `H_{0i}(x,t e_j) = b_i'(x)+t C_{ij}'(x)`.
7. `QuadraticTransverseCapSourceSingularClosure.lean` now
   derives the **seven honest scalar Schur identities** from
   `hessianDeterminant F = 1`, the cap-two source, and its
   exact marked collision. With `det C=0`, the already-proved
   source-origin minor and the singular-principal-pivot theorem
   supply the rank-two endpoint. The endpoint yields `False`.
8. The canonical E3 wrapper
   `PureLongitudinalMarkedE3Data.quadratic_sourceSingularTransverse_impossible`
   consumes only the *actual* E3 source cap, its determinant-one
   theorem, and its marked collision. The next wrapper
   `quadratic_sourceTransverseDet_ne_zero` eliminates the
   singular transverse branch.

If this entire chain compiles, the `r=2` pure E3 obstruction is now
reduced to the **generic transverse rank-three case**,
`det C(x) ≠ 0` in `K[x]`. The candidate rank-three proof in
earlier sections proceeds through `M=C^{-1}=A+xB` over `K(x)`,
nilpotence of `N=A^{-1}B`, and the interval drift operator
`I-N+N²`. The last operator's injectivity is already isolated in
`cubicNilpotent_drift_smul_injective`, but the source-level
matrix reciprocal ODE, polynomiality/unimodularity, nilpotence
and longitudinal collision transport remain unformalised.

The broader `r≥3` pure branches and other E3 terminal events
also remain open; there is **no producer-free
`PlanarJC2Injectivity K → HC4(K)` theorem yet**.

**Compiling the new code is essential:** unlike the preceding green
head, the commits from `98fba367` through this note have not been
checked by Lean in the assistant environment.

```bash
lake build HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3FinalResolution
lake build
```


## 11. Generic transverse-rank-three algebra packet (2026-11-10; awaiting local Lean build)

The previous verified E3 head `4adebaf9` rigorously eliminated the
SINGULAR source-axis transverse 3x3 Hessian case:
`PureLongitudinalMarkedE3Data.quadratic_sourceTransverseDet_ne_zero`
is now green as reported by the user. Thus `D(x)=det C(x)` is
a nonzero polynomial in `K[x]`. The remaining r=2 case is
GENERICALLY invertible over `K(x)`, not necessarily over `K[x]`.
This distinction is mathematically important.

The following new Lean source modules isolate further rank-three
consequences without assuming a final-resolution producer:

- `QuadraticTransverseCapRankThreeAffineInverse.lean`:
  zero second derivative of a polynomial (or polynomial matrix)
  implies genuine affine form `A+xB`; also establishes the
  NONCOMMUTATIVE Leibniz rule for polynomial matrices.
- `QuadraticTransverseCapRankThreeReciprocalODE.lean`:
  if `C,M` are polynomial 3x3 matrices with `CM=MC=I`
  and `C''=2C'MC'`, then `M''=0` and thus `M=A+xB`.
  An inverse only over `K(x)` is NOT enough to invoke this
  polynomial-only theorem directly. The next adapter must carry
  rational derivatives or first prove polynomiality of M.
- `QuadraticTransverseCapRankThreeNilpotent.lean`:
  exact 3x3 determinant expansion
  `det(I+xN)=1+tr(N)x+sigma₂(N)x²+det(N)x³`,
  a concrete cubic Cayley-Hamilton identity, and
  `det(I+xN)=1 ⇒ N³=0`, without assuming nilpotence.
- `QuadraticTransverseCapRankThreeAffineDet.lean`:
  explicit factorisation `A+xB=A(I+xN)` when `B=AN`
  and hence cubic nilpotence of N from exact constant
  polynomial determinant and `det A != 0`.
- `QuadraticTransverseCapRankThreeDrift.lean`:
  from the concrete derivative formula
  `b'(x)=(I-2xN+3x²N²)v`, `N³=0`,
  and `b(1)=b(0)`, deduce `v=0`.
  This proves the marked interval integration algebra.
- `QuadraticTransverseCapRankThreeLongitudinalDrift.lean`:
  a polynomial matrix inverse forces its determinant to be a
  nonzero constant, and `a''=nonzero constant` is
  incompatible with `a'(1)=a'(0)`.
- `QuadraticTransverseCapSourceLongitudinalDrift.lean`:
  connects the final scalar contradiction to the ORIGINAL
  four-variable Hessian source via the actual axis restriction
  and exact longitudinal collision. E3 now imports this
  source-level scalar endpoint and provides
  `quadratic_sourceLongitudinalMarkedCollision` and
  `quadratic_rankThreeConstantDetZeroMixed_impossible`.

**The precise remaining rank-three mathematics** is source extraction
and rational-integrality transport, not more generic rank labels:

(1) Use transverse degree <= 2 and the represented-source
`det Hess F=1` to extract the exact coefficient identities

```text
D C'' = 2 C' adj(C) C' ,
D b'' = 2 C' adj(C) b' ,
D = det C != 0.
```

(2) Pass to `K(x)`. There `M=C^{-1}` exists, the first
equation yields `M''=0`, and characteristic zero implies
`M=A+xB` with A,B over K. Since
`det M * det C=1` and both determinants are now POLYNOMIALS,
`det M` and `det C` are nonzero constants. Hence M is a
polynomial inverse, A invertible, and N=A⁻¹B has N³=0.

(3) The second equation yields
`((I+xN)^2 b')'=0`, giving the explicit derivative normal
form already consumed by the nilpotent marked-drift theorem.
With b'=0 and D constant, the represented-source scalar endpoint
gives the contradiction to its original 0~e0 collision.

These are research dependencies, NOT facts yet proved in Lean.
No JC2=>HC4 theorem or unrestricted HC4 proof is claimed.
The new modules and E3 wrapper **need compilation**.

```bash
lake build HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3FinalResolution
lake build
```


## 12. Actual quadratic E3 rational inverse and rational Riccati integrality (2026-11-10; build pending)

**Last user-confirmed green head:** `4adebaf9b840f906c587a5478f28c327bbc1e24f`,
which established the actual source singular-transverse elimination and
`quadratic_sourceTransverseDet_ne_zero`. The subsequent rank-three
modules (starting with `dfd668f` and continuing here) still REQUIRE
local Lean compilation.

This continuation adds five genuinely mathematical interfaces:

1. `QuadraticTransverseCapSourceRationalInverse.lean`: constructs
   `C(x)^{-1}` as the actual TWO-SIDED inverse of the green E3
   polynomial transverse Hessian matrix over `RatFunc K`.
   No polynomial inverse or determinant constancy is presumed.
2. `QuadraticTransverseCapRankThreeFieldDerivation.lean`: proves
   `(C^{-1})''=0` from the matrix Riccati equation
   `C''=2C' C^{-1} C'` for **any differential coefficient field**,
   and proves entrywise affine form `A+xB` when the derivation's
   constant field is the ground field.
3. `QuadraticTransverseCapRankThreeAffineDescent.lean`: proves that
   if the field-valued inverse has entries `a+b x`, these are
   images of actual polynomials; two-sided invertibility DESCENDS
   through an injective polynomial embedding. In particular
   `det C\in K^×` is then a *conclusion*, not a hypothesis.
   The later `compatibleDerivation_integralInverse` theorem
   combines reciprocal Riccati, polynomial differentiation, field
   constants, and polynomial inverse descent without extra
   integrality assumptions.
4. `QuadraticTransverseCapRatFuncConstants.lean` and
   `QuadraticTransverseCapRatFuncDerivationX.lean`: if a
   `K`-derivation of `RatFunc K` satisfies `D(X)=1`,
   the pinned `Derivation.comp_aeval_eq` chain rule proves
   polynomial differentiation compatibility. The normalized
   coprime `RatFunc.num/denom` calculation proves its constants
   are exactly `K`. This removes an unproved constants-field
   hypothesis from the generic-rank-three algebra.
5. `QuadraticTransverseCapSourceRankThreeRiccatiBridge.lean`
   and the corresponding E3 theorem
   `PureLongitudinalMarkedE3Data.quadratic_sourceRiccati_constantDet`:
   instantiate that result on the SAME represented-source
   transverse Hessian, once its explicit Riccati identity is
   supplied. The output is a polynomial two-sided inverse and
   nonzero constant transverse determinant for the source.

**Remaining exact mathematical seams:**

A. Construct a `K`-derivation of `RatFunc K` with
   `D(RatFunc.X)=1`; `RatFunc.liftOn'` and the quotient rule
   are candidate routes. The polynomial compatibility and
   constants-field proof are now conditional consequences of this
   one construction.

B. Extract, WITHOUT NEW HYPOTHESES, the y-quadratic coefficient
   of the ACTUAL represented-source identity `det Hess F=1`:
   `(det C) C'' = 2 C' adj(C) C'`, then transport it via
   the rational derivation to the source Riccati equation.
   Existing source cap-two, fixed transverse Hessian,
   affine mixed-section, and all-section determinant-one
   lemmas provide the prerequisites; the coefficient comparison
   itself is **not yet formalised**.

C. Extract the y-linear coefficient
   `(det C) b'' = 2 C' adj(C) b'`. From the affine reciprocal
   form, solve this to obtain the already written nilpotent
   derivative model for `b'`, then use the marked transverse
   and longitudinal collisions to reach the scalar contradiction.

D. Complete any r>=3 and other E3 frontiers before claiming
   producer-free `PlanarJC2Injectivity K -> HC4(K)`.

No new axioms or `sorry` were deliberately introduced. However,
**source files contain unverified Lean proof scripts**. A zero-sorry
grep is NOT the same as a green Lean build.

```bash
lake build HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3FinalResolution
lake build
```
