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
