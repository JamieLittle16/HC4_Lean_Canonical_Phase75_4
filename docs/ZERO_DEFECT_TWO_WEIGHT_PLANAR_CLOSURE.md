# Zero-defect two-weight planar closure

> **Status: PAPER CANDIDATE — NOT YET LEAN VERIFIED.**
>
> This note records a no-JC2 **consumer theorem** for an honest first-contact
> terminal **provided that the terminal lattice is retained on the same blocker
> whose Hessian defect is zero**.  It must not be cited as a compiled theorem.
> More importantly, the current A19 zero-clock strict-low packet does **not**
> automatically supply the positive family-parameter contact required by this
> hypothesis.  Constructing such a balanced first-contact lattice, or replacing
> it by an equivalent source-honest geometric argument, remains substantive.

## 1. Why this is different from the generic JC2 endpoint

The generic first-contact endpoint eventually has a terminal cocharacter with
standard two-zero weight

\[
(0,0,d,d), \qquad d>0,
\]

so, after a coordinate permutation fixing the marked longitudinal coordinate,
its terminal fibre has the exact doubling form

\[
F=zA(x,y)+wC(x,y).
\]

At that point the Monge--Ampere identity gives a nonzero constant planar
Jacobian for `(A,C)`, and a terminal gradient collision gives a genuine planar
Keller collision.  If all earlier provenance is forgotten, this is the real
JC2 seam.

However, an honest first-contact terminal also carries an *earlier exposure
weight* and a positive contact monomial.  At zero blocker defect that second
weight is strong enough to force the planar pair triangular.  Thus **once such
an endpoint exists on the same zero-defect blocker**, no general JC2 theorem is
needed to consume it.

## 2. Retained first-contact data

Let `B` be the blocker used by an honest first-contact lattice `L`, and assume

\[
\Delta:=B.aligned.endpoint.defect=0.
\]

Write

- `R>0` for the ramification index;
- `W : Fin 4 -> Nat` for the first-contact exposure weight;
- `M` for the divided common level;
- `q(e)` for the exact parameter order of a source coefficient.

The existing first-contact package gives

\[
L.defect=R\Delta+2\sum_i W_i-4M,
\]

and at a terminal first contact this defect is zero.  Since `Delta=0`,

\[
2M=\sum_i W_i. \tag{2.1}
\]

The marked moving point forces

\[
W_0=0. \tag{2.2}
\]

For every coefficient that survives in the terminal special fibre, exact
first-contact factorisation gives

\[
R q(e)+W\cdot e=M, \tag{2.3}
\]

so in particular

\[
W\cdot e\le M. \tag{2.4}
\]

The distinguished contact exponent has positive exact parameter order, hence

\[
W\cdot e_{\rm contact}<M. \tag{2.5}
\]

A theorem of the form (2.3) is already proved in the direct-closing square
module as `sourceContactLevel_of_coeff_ne_zero`; the generic first-contact
version should be the same coefficient-factorisation proof.

## 3. Standardise the independent terminal cocharacter

The terminal source cocharacter is **not** `W`.  The existing unique-zero
elimination supplies a second zero for that terminal cocharacter, and the
other two terminal-cocharacter weights equal its degree.  Use the existing
coordinate permutation, which fixes coordinate `0`, to put it into

\[
(0,0,d,d).
\]

Apply the same permutation to the earlier exposure weight `W`.  Because the
permutation fixes the marked coordinate, write

\[
W=(0,s,u,v).
\]

Equation (2.1) becomes

\[
2M=s+u+v. \tag{3.1}
\]

The terminal fibre has exact form

\[
F=zA(x,y)+wC(x,y), \tag{3.2}
\]

with both `A` and `C` nonzero (indeed their planar Jacobian is a nonzero
constant).

## 4. The second base weight cannot vanish

Assume first that `s=0`.

Choose any nonzero monomial `x^a y^b` in `A`.  Then
`x^a y^b z` occurs in `F`, and (2.4) gives

\[
u\le M.\]

Similarly a nonzero monomial in `C` gives

\[
v\le M.\]

Together with (3.1) and `s=0`,

\[
u+v=2M,
\]

so necessarily

\[
u=v=M. \tag{4.1}
\]

But every supported monomial of the two-zero fibre has exactly one of `z,w`.
Thus, when `s=0` and (4.1) holds, **every** terminal support monomial has
`W`-weight exactly `M`.  In particular the distinguished positive contact
monomial has weight `M`, contradicting (2.5).

Therefore

\[
\boxed{s>0}. \tag{4.2}
\]

This is the key point at which positive first-contact provenance makes the
zero-defect endpoint smaller than a generic planar Keller endpoint.

## 5. Planar y-degree collapse

Let

\[
p=\deg_y A,\qquad q=\deg_y C.
\]

Choose a supported top-y monomial of each component.  The corresponding
monomials `x^a y^p z` and `x^c y^q w` occur in `F`.  Applying (2.4) gives

\[
sp+u\le M,
\]

\[
sq+v\le M.
\]

Adding and using (3.1),

\[
s(p+q)+u+v\le2M=s+u+v.
\]

Since `s>0`,

\[
\boxed{p+q\le1}. \tag{5.1}
\]

Thus either

\[
\deg_yA=0,\quad \deg_yC\le1,
\]

or the symmetric alternative.

The case in which both have y-degree zero has zero planar Jacobian and is
impossible.  Hence, up to swapping the target coordinates,

\[
A=a(x),\qquad C=c_0(x)+c_1(x)y. \tag{5.2}
\]

## 6. Keller condition makes the pair triangular-invertible

For (5.2),

\[
J(A,C)=a'(x)c_1(x).
\]

The terminal Monge--Ampere equation gives `J(A,C)` a nonzero constant value.
Since `K[x]` is a domain whose units are the nonzero constants,

\[
a'(x)\in K^\times,\qquad c_1(x)\in K^\times.
\]

In characteristic zero, `a'(x)` constant and nonzero forces `a(x)` affine
linear.  Therefore `(A,C)` has the explicit triangular polynomial inverse

\[
x=a^{-1}(A),\qquad
 y=\frac{C-c_0(x)}{c_1}.
\]

It is injective, contradicting the distinct planar collision inherited from
the terminal gradient collision.

Hence:

> **Paper consumer theorem candidate.**  An honest first-contact terminal
> built on a blocker of Hessian defect zero is impossible, without invoking
> planar JC2.

## 7. Where the JC2 hardness actually moved

The exact planar doubling embedding proves that unrestricted HC4 contains the
full planar JC2 problem.  The live A19 reduction is stronger than older
producer-based descriptions: positive reached rank-three states are consumed
as global progress, and the only local terminal retained by the current proof
architecture is the literal zero-clock strict-low terminal.

Therefore an unconditional theorem eliminating **every** current zero-clock
strict-low terminal would prove unrestricted HC4 and, through the exact
embedding, planar JC2 as a consequence.  The hardness cannot simply be said to
"route through a positive-defect terminal".

The missing hypothesis in the consumer theorem above identifies where that
hardness can hide.  `AdaptiveAlignedSmithLayerSensitiveFirstContactData`
requires a supported source coefficient at a **positive family-parameter
order** and an integral supporting lattice.  By contrast, A19.51--52 only
force a later **spatial/longitudinal** monomial in the determinant-one special
fibre.  A zero-defect polynomial family may even be parameter-constant, so
positive family-parameter contact cannot be inferred merely from determinant
one plus collision.

Thus the present logical status is:

\[
\text{zero-clock strict-low geometry}
\quad\stackrel{?}{\Longrightarrow}\quad
\text{same-blocker balanced positive first contact}
\quad\Longrightarrow\quad
\text{triangular planar contradiction}.
\]

The second implication is the new paper result.  The first implication (or a
replacement argument extracting the same degree collapse directly from the
codimension-two geometry) is the genuine remaining mathematical seam.

## 8. A useful equivalence check on the balanced weight

For a generic doubling form

\[
F=zA(x,y)+wC(x,y)
\]

with `p = deg_y A` and `q = deg_y C`, a collision-preserving weight has the
form

\[
W=(0,s,u,v).
\]

If the full top `y`-layers of both components survive at a zero-defect balanced
level, the same inequalities used above give `p+q <= 1`.  Conversely, solving

\[
2\max(u+sp,\,v+sq)=s+u+v
\]

shows that for `p+q >= 2` no such positive balanced presentation can retain
those two top layers.  This is a useful warning: existence of the balanced
lattice is already essentially equivalent to the desired degree collapse in a
generic planar presentation.  It must be forced by the extra HC4/strict-low
geometry, not assumed as a harmless normalization.

## 9. Lean / mathematics checklist

1. **Do not reintroduce the old producer as an assumption.**  The live A19.53
   object is producer-free; any new lattice must be constructed from its actual
   retained source geometry.
2. **Zero-clock transport is already green.**
   `zeroStrictLow_zeroClockPacket` already proves the presented and blocker
   defects are literally zero.
3. **Separate spatial departure from parameter departure.**  The A19.52
   `HasFirstExactSmithExponentLongitudinalDeparture` is a supported monomial in
   the special fibre; it is not a positive parameter-order witness.
4. **If an honest lattice is constructed, keep the same blocker.**  Then the
   two-weight consumer applies without a generic JC2 assumption.
5. **Generic terminal contact level.**  Generalise/reuse the existing
   direct-closing theorem proving every nonzero terminal coefficient has exact
   source contact level `R*q + weight = commonLevel`.
6. **Permute both weights.**  Reuse the first-contact terminal permutation
   fixing coordinate `0`; transport the earlier exposure weight with it.
7. **Two-zero support.**  Reuse
   `standardTwoZero_support_positivePairDegree_one`.
8. **Triangular planar lemma.**  Keep the final `deg_y A + deg_y C <= 1`
   injectivity statement state-free.
9. **Alternative route.**  If balanced lattice construction is as hard as the
   generic planar problem, use the codimension-two exposed top vertex directly:
   the mixed determinant coefficients force unit departures / fixed-kernel
   cone normal forms, which may feed the existing longitudinal/kernel-opening
   infrastructure without ever constructing a planar endpoint.

## 10. Relation to the current codimension-two attack

The mixed Hessian calculations around a codimension-two exposed vertex force
cone/one-direction behaviour.  For the exactly-two-positive-coordinate model,
two independent departures satisfy

\[
-ABmn(m-1)(n-1)(D-1)=0,
\]

so one departure is primitive.  In the doubly primitive case the next
coefficient gives proportional transverse exponents; in the asymmetric case
the remaining coefficients force one active exponent of the vertex to be one
and again produce a three-linear-form cone.

This suggests the most promising unconditional continuation is to use the
canonical exposed-vertex provenance to promote that local constant kernel to a
source-honest top-face/kernel statement.  If that succeeds, the existing
kernel-opening / longitudinal top-degree machinery can replace the missing
balanced-lattice construction.  If it fails precisely because further support
breaks the kernel, the first kernel-breaking support is the next canonical
contact to analyse.