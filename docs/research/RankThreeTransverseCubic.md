# The cap-three full-rank transverse cubic

## Statement

Let \(K\) be a field of characteristic zero, let \(y\) consist of three
variables, and let \(F\in K[x,y]\) have transverse degree at most three
and nonzero constant Hessian determinant \(\delta\). Put \(L=[F]_3\).
If \(M=H_yL\) is invertible over \(K(x,y)\), then \(\nabla F\) is
injective. No singular-axis hypothesis or planar Jacobian conjecture
is used. This is a paper proof, not an end-to-end Lean theorem.

We may pass to an algebraic closure, since injectivity there implies
injectivity over \(K\). The degree-six transverse part of \(\det H(F)\)
is \(\det H(L)\). Indeed each summand has upper degree \(4\cdot3-2\cdot3=6\),
and only the cubic enters that grade. Therefore \(\det H(L)=0\).

## Straight characteristics

Choose the longitudinal origin so that \(M(0,y)\) is invertible
generically. Put \(C(y)=L(0,y)\). With \(r=L_{yx}\), write
\[
v=-M^{-1}r,\qquad V=(1,v),\qquad D=V\cdot\nabla.
\]
The Schur identity gives \(H(L)V=0\). Differentiating
\(V^TH(L)V=0\) with respect to each variable \(z_i\) gives
\(V^T(\partial_iH(L))V=0\), since the terms differentiating \(V\)
vanish. By third-derivative symmetry these are exactly the entries
of \((D H(L))V\). Differentiating \(H(L)V=0\) by \(D\) now gives
\(H(L)DV=0\). The longitudinal entry of \(DV\) is zero, so invertibility
of \(M\) gives \(DV=0\).

Thus the gradient is constant along the straight characteristic. To
see this purely algebraically, use the formal exponential of the
derivation \(D\) on \(K(x,y)[[t]]\). The Leibniz formula makes this a
homomorphism on \(K(x,y)\) into \(K(x,y)[[t]]\). Since \(DV=0\), it maps
the coordinates to \((x+t,y+t v(x,y))\). Since \(D\nabla L=0\), it
fixes the gradient. Specialize the resulting polynomial-in-\(t\)
identity at the chosen origin, where \(M(0,y)\) is generically
invertible. Denote \(v(0,y)\) by \(W(y)\). Then
\[
 \nabla_y L(x,y+xW(y))=\nabla C(y). \tag{1}
\]
The substitution \(T_x(y)=y+xW(y)\) is polynomial in \(x\) over
\(K(y)\), and \(W\) is homogeneous rational of degree one in \(y\).

## A fixed square derivative or a stationary cubic

If \(W=0\), (1) and transverse homogeneity give \(L=C\). We show that
in every other case, in constant transverse coordinates \(y=(u,v,w)\),
\[
             L_u=c v^2,\qquad c\in K^\times. \tag{2}
\]

### Polynomial characteristic direction

If \(W\) is polynomial, its homogeneity makes it \(Ny\) for a
constant matrix \(N\). Differentiating (1) in \(y\) gives
\(M(x,T_xy)(I+xN)=M(0,y)\). Taking determinants shows that
\(\det(I+xN)=1\), since it is a polynomial factor of a nonzero
constant in \(K(y)[x]\) and has constant coefficient one. Hence \(N\)
is nilpotent. Comparing the coefficient of \(x\) in the matrix
identity shows \(M(0,y)N\) is symmetric: the coefficient of \(x\)
of \(M(x,T_xy)\) is symmetric.

For \(N\ne0\), take a Jordan basis. If \(N\) has rank one, use
\(N e_v=e_u\) and \(N e_u=N e_w=0\). Symmetry gives
\(C_{uu}=C_{uw}=0\), so \(C_u=c v^2\), where \(c\ne0\) by
invertibility of \(M(0,y)\). The \(v\) coordinate is invariant under
\(I+xN\), and (1) gives (2). If \(N\) has rank two, take
\(N e_w=e_v\), \(N e_v=e_u\), \(N e_u=0\). Symmetry gives
\(C_{uu}=C_{uv}=0\), so \(C_u=c w^2\), \(c\ne0\). The \(w\)
coordinate is invariant, and swapping the names \(v,w\) gives (2).

### A pole in the characteristic direction

If \(W\) is not polynomial, take a prime polynomial \(p(y)\) at which
it has a pole, of maximum component order \(m>0\). Use the
\(p\)-adic valuation on \(K(y)\), extended to \(K(y)(x)\) with \(x\)
an independent residue indeterminate. Multiplying (1) by \(p^{2m}\)
and reducing proves
\[
                   \nabla_y L(x,\overline{p^m W})=0.
\]
The residue vector is nonzero and represents a common projective
singular point of all the cubics. This point is defined over \(K\):
the reduced plane cubic \(C\) has only finitely many singular points,
all defined over the algebraically closed ground field. Here \(C\)
is reduced because a ternary cubic with a repeated factor is a
product of the square of a linear form with a linear form, whose
transverse Hessian has rank at most two. Finiteness also follows
directly since, in characteristic zero, the partials of a squarefree
homogeneous form have no common curve component, by Euler's identity
and the product rule.

Choose constant coordinates taking the common singular point to the
\(u\)-axis, and write \(z=(v,w)\). Then
\[
                  L=u Q(x,z)+P(x,z)
\]
with \(Q\) binary quadratic and \(P\) binary cubic. Let
\(U=u+xW_u\), \(Z=z+xW_z\). The order of \(U\) is \(-m\), and the
minimum order \(t\) of the two entries of \(Z\) is strictly greater
than \(-m\). If the binary Hessian of \(Q\) were invertible over
\(K(x)\), then \(U\nabla_z Q(x,Z)\) would have minimum order \(t-m\),
while \(\nabla_z P(x,Z)\) has minimum order at least \(2t\).
For \(t<m\), the former would be a pole of strictly lower order,
contrary to (1). Thus \(t\ge m\). Both entries of \(Z\) would vanish
modulo \(p\). Since \(Z=z+xW_z\) is linear in \(x\) and \(x\) is
residue-transcendental, this would make \(p\) divide both coordinate
polynomials \(v,w\), which is impossible. The binary Hessian of \(Q\)
therefore has rank one, since \(Q=0\) would contradict rank three.

Write \(Q=a(x)\ell(x,z)^2\) with \(a\in K[x]\setminus\{0\}\) and
\(\ell\) a binary linear form with primitive coefficients in \(K[x]\).
This follows by factoring the rank-one form over \(K(x)\) and
clearing denominators in its linear factor. The primitive square
has no common denominator in its coefficients. The \(u\) component
of (1) says
\[
      a(x)\ell(x,z+xW_z)^2=a(0)\ell(0,z)^2\ne0.
\]
Both factors are polynomials in \(x\) over \(K(y)\), so \(a=c\in
K^\times\) and \(\ell(x,z+xW_z)=\ell(0,z)\).

If the coefficient covectors of \(\ell(x,\cdot)\) span dimension two,
comparing coefficients in
\[
       \ell(x,W_z)=\frac{\ell(0,z)-\ell(x,z)}{x}
\]
shows \(W_z\) is linear in \(z\), in particular independent of \(u\).
Differentiate the two \(z\) components of (1) in \(u\). The \(P\)
terms are independent of \(u\) and the common factor \(2c\ell(0,z)\)
cancels. The result is
\[
             (1+x\partial_u W_u)\ell(x,\cdot)=\ell(0,\cdot),
\]
contradicting dimension two. Hence all those covectors are
proportional, and primitivity makes \(\ell\) constant in \(x\).
Changing constant coordinates in \(z\) gives (2).

The pole case is not vacuous for the top equation. For instance,
\(L=u v^2+(w-xv)^3\) has an invertible transverse Hessian
over the function field and satisfies (1) with
\(W=(3w^2/(2v),0,v)\). This is an example of the top equation,
not a claim that such a cubic extends to a constant-Hessian-determinant
source.

## Stationary cubic

Write
\[
 F=C(y)+\tfrac12 y^TB(x)y+b(x)^Ty+d(x).
\]
Let \(M_F=H_yC+B\), \(q=B'y+b'\), and \(D_3=\det H_yC\ne0\).
The block determinant identity is
\[
  \delta=\big(\tfrac12 y^TB''y+b''\cdot y+d''\big)\det M_F
                -q^T\operatorname{adj}(M_F)q .
\]
The adjugate term has transverse degree at most four. Degree five
therefore gives \(B''=0\). In degree four the identity is
\[
    (b''\cdot y)D_3=(B'y)^T\operatorname{adj}(H_yC)(B'y).
\]
The right side and \(D_3\) are independent of \(x\), so \(b''\) is
constant. In transverse degree three the terms other than \(d''D_3\)
are at most affine in \(x\): the degree-two term of \(\det M_F\)
and degree-one term of its adjugate are linear in entries of \(B\),
and \(b'\) is affine. Thus \(d''\) has degree at most one. Together
these bounds show that \(F\) has total degree at most three.

For a polynomial gradient of degree at most two,
\(\nabla F(P)-\nabla F(Q)=H(F)((P+Q)/2)(P-Q)\) by the midpoint
identity for quadratic polynomials. The Hessian is everywhere
invertible, so the gradient is injective.

## Square fibre derivative

In coordinates (2) the original potential has the exact form
\[
 F=R(x,v,w)+u f(x,v,w)+\tfrac12 a(x)u^2,\qquad
 f=c v^2+e(x)v+k(x)w+b(x).
\]
Write \(P=[R]_3\). Then
\(\det H_yL=-(2cv)^2P_{ww}\) in these coordinates, so \(P_{ww}\ne0\).
In particular \(R_{ww}\) has nonzero transverse degree-one part.
Constant transverse coordinate changes may rescale \(\delta\)
but preserve its being a nonzero scalar and preserve injectivity.

### Nonzero \(a\)

The partial Legendre transform at fixed \(s=F_u\) is
\(G=R-(s-f)^2/(2a)\) over \(K(x)\), with
\(\det H_{x,v,w}G=\delta/a\) by the Schur complement. In this
Hessian the \(s\)-dependence of the transverse block is only the
\(v,v\) term \((2c/a)s\). The \(s^2\) coefficient of \(G_{xx}\)
is \(-\tfrac12(1/a)''\), and the coefficient of \(s\) in \(G_{xw}\)
is \((k/a)'\). The \(s^3\) coefficient of the determinant is thus
\[
  \frac{2c}{a}
     \left(-\frac12(1/a)''\,G_{ww}-((k/a)')^2\right).
\]
It vanishes. The transverse degree-one part of \(G_{ww}\) is
\(P_{ww}\ne0\), forcing \((1/a)''=0\). Clearing denominators gives
\(a a''=2(a')^2\). If \(a\) had positive degree \(d\), the leading
coefficient comparison would give \(d(d-1)=2d^2\), impossible in
characteristic zero. Thus \(a\) is a nonzero constant. At every
fixed \(s\) the resulting polynomial \(G\) has constant nonzero
Hessian determinant and injective gradient by
[de Bondt's theorem in dimension three](https://arxiv.org/abs/1203.6605).
The original gradient outputs are \(s\) and the three gradient
outputs of \(G\) at that \(s\), as the chain rule on \(F-su\)
cancels the derivatives of the solved fibre. This recovers \(x,v,w\)
and then \(u\).

### Zero \(a\), nonzero \(k\)

The coefficient of \(u^2\) in \(\det H(F)\) is
\[
 -(2c)k^2 f_{xx}+(k f_{xv}-k'f_v)^2+2(2c) k k'f_x.
\]
Its coefficient of \(w\) is \(2c k(2(k')^2-kk'')\). Since
\(k\ne0\), the same leading coefficient argument gives \(k\in
K^\times\).

Fix the original outputs \(s=F_u\) and \(t=F_w\). Solve
\(w=(s-cv^2-e v-b)/k\) and \(u=(t-R_w)/k\) polynomially.
The double partial Legendre transform \(G=F-su-tw\) at these
solutions is a polynomial in \(x,v\) at each \((s,t)\), and its
gradient is the remaining pair of original outputs. The eliminated
fibre block is
\(\left(\begin{smallmatrix}0&k\\ k&R_{ww}\end{smallmatrix}\right)\),
of determinant \(-k^2\), so \(\det H_{x,v}G=-\delta/k^2\).
The same low-dimensional Hessian theorem in dimension two recovers
\(x,v\), and the solved formulas recover \(w,u\).

### Zero \(a\), zero \(k\)

The coefficient of \(u\) in the full determinant is now
\[
 -R_{ww}\big( (2c)f_x^2-2 f_{xv}f_xf_v+f_{xx}f_v^2\big).
\]
Since \(R_{ww}\ne0\), the bracket vanishes identically. At
\(v=-e(x)/(2c)\) we have \(f_v=0\), so \(f_x=0\) there too.
But \(f_w=0\) and \(F_{uu}=0\), so the \(u\) Hessian row vanishes
at those points, contradicting the nonzero constant determinant.

## Consequence for the marked singular-axis problem

For the marked collision \(\nabla F(0,0)=\nabla F(1,0)\) with
\(\det H_yF(x,0)=0\) identically, scale one coordinate over the
algebraic closure to normalise the nonzero scalar determinant to one.
For example, scaling a transverse coordinate preserves both marked
points and the singular-axis hypothesis. The
[singular-axis cubic correction](TransverseAxisCubicCorrection.md)
rules out ranks zero and one in cap three. The
[rank-two result](RankTwoTransverseCubic.md) and the theorem above
rule out ranks two and three. Thus no such marked collision exists
at transverse cap three. This corollary, too, is presently a paper
result. It does not rule out a nonsingular-axis collision whose
top cubic has rank one, or give a reduction from unrestricted HC4.

## Formalisation boundary

The characteristics module proves the straight characteristic identity (1)
for the **actual** cubic grade of a constant Hessian determinant source of
transverse degree at most three. It derives the singular full Hessian from
weight six, chooses a longitudinal ground-field basepoint with generically
invertible transverse Hessian, and constructs the characteristic by
localizing at the transverse determinant. Instead of a formal exponential,
it proves the substitution identity by induction on polynomial coefficients.

The Jordan square module checks the self-adjointness calculation from
a linear-characteristic transport equation and extracts the square in
either constant Jordan chart. It also checks that transport in these
charts carries the square back to the source. The pole residue module
checks the homogeneous quadratic residue calculation at a pole. The
square lock module checks constancy of the scalar and the primitive binary
covector once the rank-one pivot and transport identities are available.

The linear transport and nilpotent square modules remove the need to
construct a Jordan basis for the reference-square calculation. Lean
differentiates the gradient transport to get the Hessian transport,
forces the determinant of the linear velocity pencil to be one, and
uses Cayley–Hamilton to obtain nilpotence. In dimension three the
last nonzero power is square-zero, so rank-nullity makes it rank one.
Its outer-product factors give a fixed direction and invariant
covector. Euler's homogeneous identity then gives a nonzero square
derivative on the reference cubic.

The basis-free square pullback is now Lean-compiled in
`RankThreeCubicLinearSourcePullback.lean`. It proves the nilpotent
characteristic substitution injective via the finite polynomial inverse,
then uses gradient transport and the invariant covector to derive the
square derivative on the **actual** source. The named theorem
`source_square_of_linear_characteristic` assumes a linear velocity,
its transport identity, and the already proved reference-square data;
it is not a classification of arbitrary rational characteristics.
See [the source-pullback proof](RankThreeCubicLinearSourcePullback.md).

The subsequent `RankThreeCubicLinearSquareAssembly.lean` module now
composes the earlier results **without assuming a reference square**.
A nonzero linear velocity with a regular reference transverse Hessian,
a homogeneous reference cubic, and the actual gradient-transport equation
forces a nilpotent `N`, a nonzero rank-one power `N^r=dℓᵀ`
(with `r=1` or `r=2`), and an actual-source identity
`d·∇ᵧ L=c(ℓ·y)^2` with `d,ℓ,c` nonzero.
The matrix self-adjointness required by the reference-square theorem is
derived from the transported Hessian, and its propagation to `N²`
is checked directly. The
[targeted Lean CI run](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44819572594)
passed. This closes the **nonzero linear-characteristic square step**,
not the general rational-characteristic classification or the
remaining determinant-fibre injectivity proof.

It remains to extract the linear velocity from an arbitrary pole-free
rational characteristic. In the pole case, one must construct the local
ring at a denominator prime, descend the residue singular point to the
ground field after extending scalars, exclude a nonsingular binary
quadratic there, and derive the two transport identities used for the
square lock.

The fibre pencils module verifies the subsequent cubic coefficient for
the single partial Legendre transform, the two affine-fibre determinant
differences, and the kernel acceleration identity. The rank-two companion
module verifies polynomial reciprocal rigidity. The coefficient assembly
for the source and low-dimensional injectivity applications are not
formalised here.
