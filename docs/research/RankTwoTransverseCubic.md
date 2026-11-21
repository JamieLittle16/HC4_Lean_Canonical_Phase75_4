# The cap-three rank-two transverse cubic

## Statement and scope

Let \(K\) be a field of characteristic zero, \(x\) one longitudinal
coordinate and \(y\) three transverse coordinates. Let \(F\in K[x,y]\)
have transverse degree at most three and constant nonzero Hessian
determinant \(\delta\). Write \(L=[F]_3\). If \(H_yL\) has rank two over
\(K(x,y)\), then \(\nabla F\) is injective on \(K^4\).

This closes the rank-two cubic branch on paper, even without the singular
transverse-axis hypothesis. No planar Jacobian conjecture is used.
The determinant identities in the accompanying Lean module are checked.
The geometric reductions and the use of low-dimensional Hessian
injectivity have not been formalised end to end.

## The cubic is independent of a constant transverse direction

Put \(k=K(x)\), taking transverse derivatives over \(k\). First,
\(L\) is a binary cubic after a linear change over \(k\). Here is a
direct argument for this degree. Choose \(y_0\in k^3\) where \(H_yL\)
has rank two, and choose coordinates in which \(H_yL(y_0)\) has an
invertible binary block and a zero third row and column. Since its
entries are linear in \(y\), the coefficient of \(t\) in
\(\det(H_yL(y_0)+tH_yL(y))\) is the determinant of that binary block
times the third diagonal entry of \(H_yL(y)\). The pencil determinant
vanishes identically, so the cubic is affine in this third direction.

Write \(L=P(v,w)+uQ(v,w)\) in that chart. If \(Q=0\) we are done.
Otherwise the coefficient of \(u\) in the transverse determinant is
\(-2Q\det H(Q)\), by Euler's identity \(\nabla Q=H(Q)(v,w)^T\).
Thus \(H(Q)\) has rank one. Make a binary linear change with
\(Q=\kappa v^2\), \(\kappa\ne0\). The determinant then gives
\(-4\kappa^2v^2 P_{ww}=0\), so \(P=\alpha v^3+\beta v^2w\).
In particular \(L=v^2(\alpha v+\beta w+\kappa u)\) is binary.

Let \(m(x)\in k^3\) span the resulting transverse kernel. In the
original coordinates \(\det H(L)=0\), since it is the transverse
degree-six part of \(\det H(F)\). A nonzero mixed pairing
\(m^T L_{xy}\) would make \(H(L)\) invertible. In a basis adapted to
the transverse kernel, the bordered determinant is minus the square
of that mixed pairing times the nonzero binary minor.
Therefore \(m^TL_{xy}=0\). Differentiating \(m^T\nabla_y L=0\) in \(x\)
now gives \(m'^T\nabla_y L=0\), and then \(H_yL\,m'=0\).
Normalize one nonzero coordinate of \(m\) to one. Its derivative is
zero there, so \(m'\) proportional to \(m\) implies \(m'=0\).
A rational function in \(K(x)\) with zero derivative lies in \(K\).
We have obtained a *constant* kernel direction, so it is now legitimate
to make a constant transverse coordinate change in the original source.

Write \(u\) for that direction and \(z=(v,w)\) for its complement.
The original source has the form
\[
 F=R(x,z)+u(b(x)+e(x)^Tz)+\frac12 a(x)u^2 .
\]
The binary Hessian of the cubic part of \(R\) has nonzero determinant.
Constant coordinate changes can rescale \(\delta\), but keep it a
nonzero scalar.

## Nonzero quadratic fibre coefficient

Suppose \(a\ne0\). Over \(K(x)\), use the fibre output
\(s=F_u=b+e^Tz+au\). The partial Legendre transform at fixed \(s\) is
\[
 G(x,z,s)=R(x,z)-\frac{(s-b-e^Tz)^2}{2a}.
\]
Its \((x,z)\) Hessian has determinant \(\delta/a\), by the Schur
complement identity. Its transverse binary Hessian \(D=H_zG\) is
independent of \(s\) and has degree-two leading determinant equal
to \(\det H_zL\ne0\). Its mixed row is at most linear in \(s\),
and its longitudinal entry has \(s^2\) coefficient
\(-\tfrac12(1/a)''\). If \(v=(e/a)'\), the \(s^2\) coefficient
of \(\det H_{x,z}G\) is
\[
 -\tfrac12(1/a)''\,\det D-v^T\operatorname{adj}(D)v.
\]
The second summand has transverse degree at most one. The first
has a nonzero degree-two factor, so \((1/a)''=0\).
The reciprocal of the polynomial \(a\) is affine and hence both
are constant. In particular the partial Legendre transform is
polynomial over \(K\), not merely rational.

At each fixed \(s\in K\), \(G\) is a three-variable potential with
constant nonzero Hessian determinant. Its gradient is injective by
[de Bondt's low-dimensional Hessian theorem](https://arxiv.org/abs/1203.6605).
Two points with equal \(\nabla F\) have the same fibre output \(s\)
and the same \((x,z)\) gradient of \(G\), since differentiating
\(G=F-su\) at fixed \(s\) cancels the derivatives of \(u\).
Thus they have the same \((x,z)\), and the common \(s\) determines \(u\).

## Zero quadratic fibre coefficient

Suppose \(a=0\) and write \(f=b+e^Tz=F_u\). The \(u^2\) coefficient
of \(\det H(F)\) is \((e_1 e'_2-e_2 e'_1)^2\). Hence \(e\) has
constant projective direction if it is nonzero. If \(e=0\), the
determinant is \(-(b')^2\det H_zR\), which cannot be a nonzero scalar
because \(\det H_zR\) has nonzero transverse leading degree two.
We may therefore take \(f=b(x)+c(x)v\), with \(c\ne0\), after a
constant change in \(z\).

The coefficient of \(u\) in the determinant is
\[
 -R_{ww}\bigl(c^2(b''+c''v)-2cc'(b'+c'v)\bigr).
\]
If \(R_{ww}\ne0\), it follows that \(cc''=2(c')^2\) and then
\(b''=0\). The first identity makes \(c\) constant by leading-degree
comparison. Thus \(f\) is affine with nonzero \(v\) coefficient.
Replace \(v\) by \(f\), an invertible affine source change. The source
becomes \(u v+\widetilde R(x,v,w)\). The gradient recovers \(v\)
from the fibre component, recovers \((x,w)\) from the Hessian
injectivity theorem in two variables at that fixed \(v\), and then
recovers \(u\). The binary Hessian determinant at fixed \(v\) is a
nonzero constant because the full determinant is its negative.

If \(R_{ww}=0\), the source is jointly affine in \(u,w\). Its
two fibre outputs are \((f,g)\), where \(g=R_w(x,v)\). Their
planar Jacobian determinant \(J\) satisfies \(J^2=\det H(F)\),
so \(J\) is a nonzero constant. This planar pair is injective by
elementary triangular recovery. If \(g\) has positive \(v\)-degree
\(m\) and leading coefficient \(\mu(x)\), the highest coefficient in
\(J=(b'+c'v)g_v-cg_x\) is \(m c'\mu-c\mu'=0\).
Thus \((\mu/c^m)'=0\), and subtracting \(\lambda f^m\) from \(g\)
for \(\lambda=\mu/c^m\in K\) lowers its \(v\)-degree while preserving
its Jacobian with \(f\). Iterate until \(g\) depends only on \(x\).
Then \(-cg'=J\) makes both \(c\) and \(g'\) nonzero constants.
One recovers \(x\) from the transformed \(g\), then \(v\) from \(f\).
The original fibre variables \(u,w\) are then recovered from the
two remaining gradient components using the invertible transpose
of \(D(f,g)\).

## Formalisation boundary

The named module checks the ternary kernel-diagonal first jet,
the ternary affine cubic determinant identity, the affine and
partial-Legendre fibre determinant differences, and the polynomial
reciprocal second-derivative rigidity. The next source-level tasks are
to connect those identities to the actual cubic grade, and to supply
the low-dimensional injectivity bridge in Lean without adding a new
axiom or final endpoint hypothesis. The cap-three transverse-rank-three
branch and all higher transverse caps are outside this proof.
