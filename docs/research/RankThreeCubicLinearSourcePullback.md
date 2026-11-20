# Nilpotent linear characteristic: basis-free source-square pullback

**Status:** Complete algebraic proof on paper; not yet a Lean declaration.
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

## Suggested Lean implementation (not yet compiled)

1. In a new module importing `RankThreeCubicNilpotentSquare`,
   define the two polynomial algebra homomorphisms above. Keep the
   matrix-vector calculations at dimension three but the
   substitution on `Unit ⊕ Fin 3`.
2. Prove
   `linearLineEval_leftInverse_of_cube_zero`: the inverse
   `Polynomial (MvPolynomial (Fin 3) K) →ₐ[K]
   MvPolynomial (Unit ⊕ Fin 3) K` composed with
   `linearLineEval a N` is the identity. Prove equality of
   algebra homomorphisms by the \(x\)-generator and three
   transverse generators, using \((I+tN)U(t)=I\).
3. Derive `linearLineEval_injective_of_cube_zero` from the
   left inverse.
4. Show that `linearLineEval a N` sends
   `∑ i, C (d i) * pderiv (.inr i) L` to the constant
   polynomial of the reference directional derivative, by
   `hgrad`. Show that the transverse linear form \(\ell^Ty\)
   is invariant under the substitution using \(\ell^TN=0\).
5. Cancel the injective substitution to obtain (2).
6. Wire `selfAdjoint_of_linearCharacteristic` into the rank-one
   power using \(H(C)N=N^TH(C)\), hence
   \(H(C)N^r=(N^T)^rH(C)\). Pass that result to
   `reference_directional_eq_square_of_rankOne`, then the
   source pullback theorem.
7. Run `lake build HC4.Polynomial.RankThreeCubicLinearSourcePullback`,
   `lake build HC4`, and `#print axioms` on the actual
   source-level theorem before importing it into the main closure.

## What this does *not* settle

The constructed characteristic initially lives in the rational
function field \(K(y)\). It need not have the form \(Ny\).
A separate dichotomy must show either that it has no denominator
prime and, by homogeneity, is linear in \(y\); or that a denominator
prime yields the singular-point/pole branch. The latter remains
unformalised. The cap-three conclusion and higher caps also remain
outside this lemma.
