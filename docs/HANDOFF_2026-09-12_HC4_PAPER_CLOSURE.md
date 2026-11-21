# HC4 unrestricted closure handoff — 12 September 2026

This handoff supersedes `HANDOFF_2026-09-11_HC4_FINAL_CLOSURE.md` for current
status/TODO purposes. The older handoff remains useful for provenance and the
pre-closure audit trail.

## 1. Repository checkpoint

Repository:

```text
JamieLittle16/HC4_Lean_Canonical_Phase75_4
```

Live PR:

```text
#34 — final-assembly/a18-4-42-termination-frontier
```

The source-code checkpoint audited before the documentation pass was

```text
4f2181f879ac053b4c2c0e81aada6d41537c7726
```

The documentation commits after that point do not change Lean source code.

Important: the latest workflow observed at the pre-doc checkpoint was
`action_required` with no jobs created, so it was not evidence of a Lean
regression. Do not silently relabel paper claims as Lean verified on the basis
of documentation-only commits.

## 2. Status vocabulary

Use only:

- **LEAN VERIFIED** — formal theorem/code already compiled;
- **PAPER CANDIDATE** — current paper proof appears complete but is not yet
  formalised;
- **OPEN** — genuine mathematical/formal obligation remains.

## 3. What is Lean verified already

The global architecture is not the remaining problem. The repository already
contains the unrestricted entry/reduction machinery, canonical collision
normalisation, automatic degree cap, rank-one termination trace, positive Rees
restart edges, reached-rank-three global closure, and the producer-free
zero-clock strict-low terminal.

The local Lean chain reaches the A19.55 split on the actual singular maximal
ordinary top face:

```text
rank three on a coordinate facet
OR
same-carrier codimension two.
```

The existing family-parameter/Hessian coefficient bridge is also formal:

```lean
familyParameterHessianLayer P n =
  HC4.Polynomial.hessian (familyParameterLayer P n)
```

and the repository already has geometry-bearing rank-two consumers that store
an actual Hessian/Schur witness before attaching any repair/global transition.

## 4. Hard architectural rules

Carry these into every next session:

1. **Do not identify auxiliary Rees clocks with the zero blocker.**
2. **Do not use naked `withRepairOnly` progress as a contradiction.**
3. **Do not infer singularity of a larger carrier from a smaller singular ray.**
4. **Do not collapse the A19.55 codimension-two branch to generic JC2.**
5. **Do not use the four-monomial cross-ratio equation as a contradiction by
   itself.**
6. **Do not conflate A19.55 same-carrier codimension two with the later
   degree-one lower `.qs` endpoint eliminated by A19.91.**
7. **Do not add a second rank-one recursion.**
8. Geometry must exist before a rank-two progress interface is consumed.

## 5. Rank-three other-facet paper closure

### 5.1 Source-honest defect-neutral planar refinement

Starting from the locked source ray exposure `(W,L)`, use

```text
u = (1,1,0,0),
(W_t,L_t) = (W+t*u,L+t).
```

For any source exponent `e`, its gap changes by

```text
g_t(e) = g_0(e) - t((e0+e1)-1).
```

The locked ray has pair degree `e0+e1=1`; the retained strict-low source
witness has pair degree greater than one, so it reaches the ray face at finite
positive `t`.

The Hessian defect is exactly invariant:

```text
4(L+t)-2*sum(W+t*u) = 4L-2*sum W.
```

A sufficiently small independent neutral skew perturbation selects a generic
first normal-fan wall while preserving positive weights and strict positive
defect. Finite support permits an exact rational/integral choice. The resulting
planar carrier is an **exact source exposure**, so its singularity comes from
the positive determinant defect of that exposure, not from inherited ray
singularity.

**Status: PAPER CANDIDATE.**

### 5.2 Highest-slice singularity

Grade the planar carrier by pair degree

```text
p(e)=e0+e1.
```

Every determinant term in a `4 x 4` Hessian loses exactly four units of `p`.
If `N` is maximal occupied pair degree,

```text
[degree_p=4N-4] det Hess(G) = det Hess(G_N).
```

Since `det Hess(G)=0`, the highest slice is singular. Because the ray direction
has pair degree zero, a nonconstant highest slice is a finite affine line
parallel to the locked ray.

**Status: PAPER CANDIDATE.**

### 5.3 Line-supported rigidity

The completed recurrence/rational-first-integral calculation proves that a
nonconstant finite line-supported singular-Hessian polynomial in direction

```text
(1,-1,-alpha,-beta)
```

contains only two adjacent monomials. For the `V>1` branch the primitive
direction is

```text
(1,-1,-1,-V).
```

Owner note:

```text
docs/LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md
```

**Status: PAPER CANDIDATE.**

### 5.4 Full Hessian of the no-singleton carrier

If nonlinear quotient fibers are all nonconstant, the carrier takes the form

```text
F = x(Q(Y)+b H^ell) + z(P(Y)+a H^ell Y),
Y = y w^V,
H = z w^V.
```

The full Hessian determinant is

```text
V*ell*(V+1)*w^(V*ell+2V-2)*z^(ell-2) * A * B
```

with

```text
A = Y(x Q' + z P') + H^ell(b*ell*x + a*(ell+1)*z*Y)
```

and

```text
B = x( b(ell-1)(Q')^2 + b^2*ell*H^ell*Q'' )
  + z( a(ell+1)Y(Q')^2 - 2bP'Q'
       - 2ab(ell+1)H^ell Q' + b^2*ell*H^ell P'' ).
```

The locked lower ray makes `A != 0`. A primitive nonlinear slice gives
`Q' != 0`. Thus `B=0` forces

```text
ell = 1,
Q'' = 0.
```

Writing `Q'=c != 0`, the remaining equations give

```text
P'  = (a*c/b) Y,
P'' = 4*a*c/b,
```

while differentiating the first gives

```text
P'' = a*c/b,
```

contradiction in characteristic zero.

This full determinant calculation subsumes the older four-monomial test. The
cross-ratio equation by itself is not contradictory.

**Status: PAPER CANDIDATE.**

### 5.5 Singleton/developable escape

Bare singularity admits developable staircase families, so the retained A19
contact data is essential.

After the standard `(X,Y,H)` substitution, the actual contact inequality gives
an ordinary-degree bound and pins the unique top homogeneous part to

```text
R_(ell+2) = A * Y * H^(ell+1).
```

For a ternary characteristic-zero singular-Hessian polynomial of Hessian rank
two, the de Bondt--van den Essen small-dimensional classification leaves a
constant-kernel alternative or a developable normal form

```text
g(L) + M p(L) + N q(L).
```

The constant-kernel alternative is forced to the `X` direction by the unique
top piece, but the locked ray contains `X H^ell`, contradiction. In the
developable alternative every degree-`d >= 2` piece is divisible by
`L^(d-1)`. Unique factorisation of the top term forces `L ~ H`, hence every
nonlinear monomial has pair degree at most one, contradicting the retained
strict planar source support with pair degree greater than one.

For Lean, first attempt a tailored A19 proof of this special classification;
formalising the entire external theorem is a fallback.

**Status: PAPER CANDIDATE.**

### 5.6 `V=1`

Same orientation is killed by the full determinant factorisation. Mixed
orientations are killed by extremal coefficient equations, ultimately

```text
2 AD = BC,
AD = 2 BC,
```

with nonzero endpoints.

**Status: PAPER CANDIDATE.**

### Rank-three conclusion

No known paper-local branch remains in the rank-three other-facet route.

## 6. Same-carrier codimension-two paper closure

### 6.1 Primitive departure algebra

Normalise

```text
H0 = x^p y^(D-p),
Hz = A x^a y^(D-m-a) z^m,
Hw = B x^c y^(D-n-c) w^n.
```

The first extremal determinant coefficient is

```text
-A*B*p*(D-p)*m*n*(m-1)*(n-1)*(D-1),
```

so `m=1` or `n=1`.

If `m=n=1`, the next surviving coefficient is

```text
A^2*B^2*(D-1)^2*(a-c)^2,
```

so `a=c`; a transverse constant shear removes one coordinate.

If `m=1<n`, the next channels force `a=0` or `a=D-1`. The first case then
forces `(p,c)=(1,0)`; the second forces `(p,c)=(D-1,D-n)`. Again a constant
collision-preserving shear gives a literal constant coordinate kernel. The
case `n=1<m` is symmetric.

Thus the local branch reaches immediate rank-two geometry, the existing
all-minors-zero rigid route, or a constant-kernel cone.

**Status: PAPER CANDIDATE.**

### 6.2 Filtered first-kernel-break theorem

Precise owner:

```text
docs/FILTERED_FIRST_KERNEL_BREAK_LEMMA.md
```

For

```text
P(t,x)=sum t^n P_n(x),
det Hess(P)=t^Delta,
```

assume the special Hessian has kernel `e3` and complementary `3 x 3`
determinant `J != 0`. Let `q` be the first positive layer breaking that kernel
and assume `q < Delta`.

At determinant order `q`, any permutation that moves coordinate `3` must use
both a row-3 and column-3 positive-order entry, costing at least `2q`. Hence

```text
[t^q] det Hess(P) = J * Hess(P_q) 3 3.
```

The left side is zero, so `Hess(P_q) 3 3 = 0`. Since the kernel breaks, some
mixed entry is nonzero. Therefore an actual principal minor is

```text
-(Hess(P_q) i 3)^2 != 0.
```

**Status: PAPER CANDIDATE.**

### 6.3 Ordinary reverse-Rees

For the actual represented determinant-one source with homogeneous pieces
`H_m` and maximal degree `D`, define

```text
R_F(t,x)=sum_{q=0}^D t^q H_(D-q)(x)=t^D F(x/t).
```

Then

```text
det Hess(R_F)=t^(4D-8).
```

The original gradient collision is transported to the exact moving sections
`t*a` and `t*b`.

If `q` is the first homogeneous layer breaking the top constant kernel, then

```text
q <= D-2 < 4(D-2),
```

so the filtered first-kernel-break theorem applies strictly before determinant
closure and gives genuine rank-two Hessian geometry.

This is a new ordinary-degree filtration. It is not the zero blocker or the
old ray clock.

**Status: PAPER CANDIDATE.**

### Codimension-two conclusion

No generic JC2 projection is needed on the current paper route.

## 7. Formalisation plan

Preferred order:

```text
1. HC4/Valuation/FirstKernelBreakRankTwo.lean
2. HC4/Valuation/FourOrdinaryReverseRees.lean
3. A19 codim-two primitive-departure theorem
4. A19 codim-two closure/splice
5. source-honest defect-neutral planar refinement
6. highest-slice singularity adapter
7. Lean line-supported rigidity
8. rank-three no-singleton + singleton/developable closure
9. V=1 branch
10. eliminate both A19.55 constructors
11. splice into reachable-terminal HC4 reduction
12. full root build and axiom/proof audits
```

Detailed theorem decomposition is in
`docs/FORMALISATION_PLAN_2026-09-12.md`.

## 8. Current claim level

The correct statement is:

> The unrestricted HC4 project now has a complete **paper candidate** closure
> of both remaining A19.55 local branches. The global entry/termination
> architecture and the relevant geometry-bearing consumers already exist in
> Lean. The next phase is formalisation and final splice.

Do **not** state that unrestricted HC4 is proved until the new paper lemmas and
adapters compile and the public theorem passes the full audited root build.
