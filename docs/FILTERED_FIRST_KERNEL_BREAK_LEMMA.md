# Filtered first-kernel-break lemma

**Status: PAPER CANDIDATE (12 September 2026).**

This note owns the elementary algebraic lemma that closes the final A19.55
same-carrier codimension-two paper branch once that branch has been reduced to
a rank-three constant Hessian kernel. It is deliberately state-free and does
not identify any auxiliary Rees parameter with the zero-defect blocker clock.

The intended Lean owner is a small reusable file such as
`HC4/Valuation/FirstKernelBreakRankTwo.lean`.

## 1. Statement

Let `K` be a field of characteristic zero and let

\[
  \mathcal P(t,x)=\sum_{n\ge0} t^n P_n(x)
  \in K[t][x_0,x_1,x_2,x_3].
\]

Write

\[
  M_n=\operatorname{Hess}(P_n).
\]

Assume that for some integer \(\Delta>0\),

\[
  \det \operatorname{Hess}_x \mathcal P=t^\Delta. \tag{1}
\]

Assume that the special fibre has a constant Hessian kernel in the fourth
coordinate and generic rank exactly three:

\[
  M_0 e_3=0, \tag{2}
\]

and

\[
  J:=\det((M_0)_{ij})_{0\le i,j\le2}\ne0. \tag{3}
\]

Let \(q\) satisfy

\[
  0<q<\Delta, \tag{4}
\]

and suppose that it is the first parameter order at which this constant kernel
breaks:

\[
  M_n e_3=0 \qquad (0<n<q), \tag{5}
\]

but

\[
  M_q e_3\ne0. \tag{6}
\]

Then

\[
  (M_q)_{33}=0, \tag{7}
\]

and therefore there is an \(i\in\{0,1,2\}\) with

\[
  (M_q)_{i3}\ne0. \tag{8}
\]

For such an `i`, the principal `2 x 2` Hessian minor of the actual coefficient
potential `P_q` is

\[
\det\begin{pmatrix}
(M_q)_{ii} & (M_q)_{i3}\\
(M_q)_{3i} & (M_q)_{33}
\end{pmatrix}
= -((M_q)_{i3})^2\ne0. \tag{9}
\]

Thus the first **preclosing** source layer that breaks a rank-three constant
Hessian kernel necessarily carries genuine rank-two Hessian geometry.

## 2. Proof

Take the coefficient of \(t^q\) in (1).

For every `n < q`, equations (2) and (5), together with Hessian symmetry, say
that row `3` and column `3` of `M_n` vanish.

Expand

\[
  \det\left(\sum_{n\ge0}t^nM_n\right)
\]

by permutations. Consider a determinant monomial of total parameter order
`q`.

If the permutation does **not** fix coordinate `3`, one selected entry lies in
row `3` and another selected entry lies in column `3`. Every nonzero such
entry has parameter order at least `q`, by minimality of the kernel break.
Hence that determinant monomial has order at least `2q`, so it cannot
contribute at order `q`.

Therefore every order-`q` contribution fixes coordinate `3`. The selected
`(3,3)` entry must have order exactly `q`; all lower coefficients there vanish.
The remaining three entries must all have order zero. Their determinant is
exactly `J`. Consequently

\[
 [t^q]\det\operatorname{Hess}_x\mathcal P
   = J(M_q)_{33}. \tag{10}
\]

Because `q < Delta`, equation (1) makes the left-hand side zero. Since
`J != 0`, we obtain (7).

Now (6) says some entry of column `3` of `M_q` is nonzero. The bottom entry is
zero by (7), so some `(M_q)_{i3}` with `i < 3` is nonzero. Hessian symmetry
then gives (9). Characteristic zero is more than enough here; the final
nonvanishing uses only that the polynomial ring is a domain.

## 3. Ordinary reverse-Rees corollary

Let

\[
  F=\sum_{m=0}^{D} H_m
\]

be the ordinary homogeneous decomposition of a four-variable polynomial with

\[
  D\ge3, \qquad \det\operatorname{Hess}F=1.
\]

Assume, after an invertible determinant-preserving linear source change, that

\[
  \operatorname{Hess}(H_D)e_3=0
\]

and that the complementary `3 x 3` Hessian determinant is nonzero.

Define the ordinary reverse-Rees family

\[
  \mathcal R_F(t,x)
   :=\sum_{q=0}^{D}t^qH_{D-q}(x)
   = t^D F(x/t). \tag{11}
\]

Then

\[
  \operatorname{Hess}_x\mathcal R_F(t,x)
   =t^{D-2}\operatorname{Hess}F(x/t),
\]

so

\[
  \det\operatorname{Hess}_x\mathcal R_F=t^{4D-8}. \tag{12}
\]

The constant kernel cannot persist through every homogeneous layer, because
that would put the same vector in the kernel of `Hess(F)`, contradicting
`det Hess(F)=1`. Let `q > 0` be the first index with

\[
  \operatorname{Hess}(H_{D-q})e_3\ne0. \tag{13}
\]

A homogeneous polynomial of degree at most one has zero Hessian, hence

\[
  q\le D-2 < 4(D-2)=4D-8. \tag{14}
\]

The filtered first-kernel-break lemma therefore applies. The actual homogeneous
source layer `H_{D-q}` has an explicit nonzero minor

\[
\partial_i^2H_{D-q}\,\partial_3^2H_{D-q}
-(\partial_i\partial_3H_{D-q})^2
=-(\partial_i\partial_3H_{D-q})^2\ne0. \tag{15}
\]

## 4. Collision preservation

The reverse-Rees family is source-honest. If

\[
  \nabla F(a)=\nabla F(b),
\]

then the polynomial sections `t a` and `t b` satisfy

\[
\nabla_x\mathcal R_F(t,ta)
=t^{D-1}\nabla F(a)
=t^{D-1}\nabla F(b)
=\nabla_x\mathcal R_F(t,tb). \tag{16}
\]

Thus (11) is a genuine moving-collision family. Its parameter is an ordinary
homogeneous-degree filtration parameter. It is **not** the A19 auxiliary ray
clock and it must never be identified with the zero blocker defect.

## 5. A19.55 use

The A19 same-carrier codimension-two branch is first reduced, by its own
primitive-departure coefficient equations, to one of three geometric cases:

1. an honest nonzero `2 x 2` Hessian minor is already present;
2. all relevant `2 x 2` minors vanish, giving the existing rigid/linear-power
   route;
3. after a collision-preserving constant shear, the top homogeneous carrier
   has a literal constant coordinate kernel and complementary Hessian rank
   three.

Case 3 invokes the reverse-Rees corollary above and therefore reaches an
actual lower homogeneous source layer with the nonzero minor (15).

The conclusion is geometry, not a progress tag. Only after the minor exists may
existing rank-two progress machinery consume it.

## 6. Lean shape

The generic formal theorem should be stated over

```lean
P : MvPolynomial (Fin 4) (Polynomial K)
```

using the existing `familyParameterHessianLayer`. The central helper is:

```lean
theorem det_coeff_firstKernelBreak
    ...
    : (HC4.Polynomial.hessianDeterminant P).coeff q =
        activeThreeDet * familyParameterHessianLayer P q 3 3
```

under the zero-column hypotheses at all lower layers.

Do **not** use a general adjugate perturbation API unless the finite `4 x 4`
coefficient proof becomes materially harder. The permutation expansion above
is finite, transparent, and exposes exactly why mixed kernel-breaking entries
cost order `2q`.

The repository already has the coefficient/Hessian bridge
`familyParameterHessianLayer_eq_hessian` and geometry-bearing rank-two
consumers. Reuse those owners rather than creating a second parameter-layer
or repair interface.
