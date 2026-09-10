# Zero-defect two-weight planar closure

> **Status: PAPER CANDIDATE — NOT YET LEAN VERIFIED.**
>
> This note records a no-JC2 closure mechanism for an honest first-contact
> terminal **provided that the terminal lattice is retained on the same blocker
> whose Hessian defect is zero**.  It must not be cited as a compiled theorem
> until the support/contact lemmas and same-blocker adapter below are checked in
> Lean.

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

However, an honest first-contact terminal still carries an *earlier exposure
weight* and a positive contact monomial.  At zero source defect that second
weight gives an additional grading which is strong enough to force the planar
pair triangular.

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

> **Paper theorem candidate.**  An honest first-contact terminal built on a
> blocker of Hessian defect zero is impossible, without invoking planar JC2.

## 7. Why this does not prove JC2

The exact planar doubling embedding shows that unrestricted HC4 contains the
full planar JC2 problem.  The argument above only closes the branch in which
an honest first-contact terminal is tied to a **zero-defect** blocker while
retaining the positive first-contact exposure grading.

An arbitrary embedded planar Keller counterexample need not enter this
zero-defect first-contact branch; it may be routed through a positive-defect
branch.  Thus the argument can remove JC2 from the current zero-clock
strict-low residual without claiming a solution of JC2 itself.

## 8. Lean checklist

1. **Same-blocker API.**  Do not return an unrelated existential endpoint from
   the zero-strict-low producer.  Retain the actual presented blocker `D.blocker`
   (or at minimum an equality identifying the endpoint blocker with it).
2. **Zero-clock transport.**  Use pure-presentation `raw_eq` plus
   `D.defect_eq` to derive `D.blocker.aligned.endpoint.defect = 0` from the
   incoming `state.rawDefect = 0`.
3. **Generic terminal contact level.**  Generalise/reuse the existing
   direct-closing theorem proving that every nonzero terminal coefficient has
   exact source contact level `R*q + weight = commonLevel`.
4. **Permute both weights.**  Reuse the A19.38 permutation fixing coordinate
   `0`; transport terminal support and the earlier exposure weight together.
5. **Two-zero support.**  Reuse the standard two-zero doubling/support theorem
   to get `e_2 + e_3 = 1` for every terminal support exponent after
   standardisation.
6. **Exclude `s=0`.**  Use nonemptiness of both planar components and the
   strict inequality for `contactExponent`.
7. **Layer bound.**  Derive `b_A+b_C <= 1` directly on supported exponents;
   this may be easier in Lean than introducing `degreeOf` immediately.
8. **Triangular planar lemma.**  Prove that a two-variable Keller pair whose
   y-support satisfies the bound is injective.  Keep this state-free.
9. **Splice locally.**  Use this theorem only for the zero-defect
   same-blocker endpoint.  Do not alter the generic A19.38 JC2 endpoint until
   the positive-defect branches are separately understood.

## 9. Relation to the current codimension-two attack

The mixed Hessian calculations around a codimension-two exposed vertex were
already forcing cone/one-direction behaviour.  The two-weight proof explains
that phenomenon globally: once that branch is routed source-honestly into a
zero-defect first-contact terminal, the retained exposure grading leaves room
for total planar y-degree at most one.  The resulting Keller map is therefore
triangular rather than a genuine arbitrary JC2 configuration.
