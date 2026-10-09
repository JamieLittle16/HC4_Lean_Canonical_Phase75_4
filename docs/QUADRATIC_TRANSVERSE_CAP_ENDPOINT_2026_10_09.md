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
