# Nilpotent linear characteristic: basis-free source-square pullback

**Status:** The nilpotent linear-characteristic source pullback is now
formalised in Lean 4.24; the targeted [GitHub Actions run](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44815620085) succeeded.
The broader rational-characteristic classification remains open.
**Scope:** The *polynomial* characteristic branch of the cap-three, full
transverse-rank argument. This note does not classify arbitrary rational
velocities or solve the pole branch.

## Source-level lemma

Let \(K\) be a commutative ring, \(x\) a longitudinal indeterminate,
\(y=(y_1,y_2,y_3)^T\), and \(L\in K[x,y]\). Fix \(a\in K\), a
constant \(3\times3\) matrix \(N\), two constant vectors \(d,\ell\in
K^3\), and \(c\in K\). Write
\[
 C(y):=L(a,y),\qquad T(t):=I+tN.
\]
Assume
\[
 N^3=0,\quad \ell^TN=0,\quad
 \nabla_y L(a+t,T(t)y)=\nabla_y C(y),\quad
 d^T\nabla_y C(y)=c(\ell^Ty)^2. \tag{1}
\]
Then, **as an identity on the actual source**, not merely the
reference slice,
\[
 \boxed{d^T\nabla_y L(x,y)=c(\ell^Ty)^2.} \tag{2}
\]
The transport argument itself does not require \(d\) to lie in
\(\ker N\), although \(Nd=0\) is supplied by the rank-one-power
construction upstream. Nor does it require characteristic zero.

### Algebraic proof

Define the homomorphism
\[
 \Phi:K[x,y]\longrightarrow K[y][t],\qquad
 x\mapsto a+t,\quad y\mapsto T(t)y.
\]
Since \(N^3=0\),
\[
 U(t):=I-tN+t^2N^2,\qquad T(t)U(t)=U(t)T(t)=I.
\]
There is therefore an explicit left inverse
\[
 \Psi:K[y][t]\longrightarrow K[x,y],\qquad
 t\mapsto x-a,\quad
 y\mapsto U(x-a)y.
\]
Both are ordinary polynomial homomorphisms (no localization or
formal exponential). On the generators \(x,y_i\), one checks
\(\Psi\circ\Phi=\mathrm{id}\). Consequently \(\Phi\) is injective.

Apply the constant row \(d^T\) to the gradient identity (1):
\[
 \Phi(d^T\nabla_yL)=d^T\nabla_yC
     =c(\ell^Ty)^2.
\]
Since \(\ell^TN=0\), \(\Phi(\ell^Ty)=\ell^TT(t)y=\ell^Ty\).
Therefore
\[
 \Phi\big(d^T\nabla_yL-c(\ell^Ty)^2\big)=0.
\]
Injectivity proves (2).

This proof is **basis-free**: no explicit Jordan normal form or
particular coordinates for \(d,\ell\) are needed. A constant
coordinate change may subsequently choose \(u\) in the \(d\)
direction and \(v\) representing \(\ell\), giving
\(L_u=cv^2\) (up to harmless nonzero constant rescaling), the
normal form consumed by the fibre determinant calculations.

## Exact dependencies already present in Lean

* `RankThreeCubicCharacteristics.lean` constructs gradient
  transport for the actual cubic grade at a regular longitudinal
  slice.
* `RankThreeCubicLinearTransport.lean` derives the Hessian
  transport from the gradient transport, proves
  \(\det(I+tN)=1\), and obtains \(N^3=0\).
* `RankThreeCubicNilpotentSquare.lean` obtains a nonzero rank-one
  power \(N^r=d\ell^T\), \(Nd=0\), \(\ell^TN=0\), and a
  square directional derivative on the reference cubic, once the
  self-adjointness hypothesis is supplied.
* `RankThreeCubicJordanSquare.lean` has an injective
  characteristic substitution in a *chosen* Jordan chart. The
  argument here replaces that chart-dependent transport by a
  polynomial inverse valid for every nilpotent \(N\).

No new closing assumption enters the proposed source theorem:
\(N^3=0\), the fixed row, the reference square, and the gradient
transport all have prior mathematical provenance. The *general*
linear-to-reference-square assembly still requires wiring the
self-adjointness of \(H(C)N^r\) from that of \(H(C)N\).

## Lean-verified implementation

The module `HC4/Polynomial/RankThreeCubicLinearSourcePullback.lean` proves:

* `linearLineEval_injective_of_cube_zero`: in characteristic zero,
  a constant matrix with `N ^ 3 = 0` defines an injective
  characteristic substitution. This is established by evaluating
  at arbitrary points using `I-tN+(tN)^2` and polynomial extensionality;
  the proof does not need an explicit global inverse algebra homomorphism.
* `square_pullback_of_transport`: an invariant reference square
  pulls back through the injective substitution.
* `linearLineEval_invariant_transverseForm`: a covector
  satisfying `l ᵥ* N = 0` defines an invariant linear form.
* `source_square_of_linear_characteristic`: from `N^3=0`,
  the actual cubic gradient-transport equation, `l ᵥ* N=0`, and
  the reference square, obtain the square directional derivative
  identity on the **original source polynomial**.

The source theorem's explicit hypotheses are data to be constructed
from the upstream characteristic argument, not extra terminal
assumptions proving HC4. An arbitrary rational velocity has not yet
been shown to enter the nilpotent linear chart; the pole branch remains
open. The cap-three injectivity proof also still requires the
fibre-coefficient assembly and low-dimensional applications.

The linked targeted Lean build succeeded. A full repository
`lake build` after root import has not yet been verified.

## Strengthened result: reference square supplied by gradient transport

The companion module
`HC4/Polynomial/RankThreeCubicLinearSquareAssembly.lean` proves
`exists_source_square_of_nonzero_linear_characteristic` in Lean 4.24.
It assumes only a nonzero constant matrix `N`, the actual linear
characteristic's transverse gradient transport, regularity of the
reference transverse Hessian, and homogeneity of the reference cubic.

The theorem derives `det(I+tN)=1` from Hessian transport, obtains
`N³=0`, and factors the last nonzero power as `N^r=dℓᵀ`.
Its Hessian-self-adjointness lemma, together with
`(HN)ᵀ=HN` and `Hᵀ=H`, shows `HN^r` is symmetric for both
`r=1,2`. The existing rank-one-square theorem then supplies
`d·∇C=c(ℓ·y)²` with `c≠0`. The already verified source-pullback
theorem concludes the corresponding identity on the actual cubic `L`.
The resulting `d,ℓ` are nonzero and satisfy `Nd=0, ℓᵀN=0`.

The [targeted Lean run](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44819572594)
succeeded. This does not imply the whole HC4 root or updated audit
has been rebuilt, nor does it establish the classification of arbitrary
rational velocities.

## What this does *not* settle

The constructed characteristic initially lives in the rational
function field \(K(y)\). It need not have the form \(Ny\).
A separate dichotomy must show either that it has no denominator
prime and, by homogeneity, is linear in \(y\); or that a denominator
prime yields the singular-point/pole branch. The latter remains
unformalised. The cap-three conclusion and higher caps also remain
outside this lemma.
