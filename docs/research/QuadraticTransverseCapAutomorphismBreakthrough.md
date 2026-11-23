# Quadratic transverse cap: a polynomial-automorphism breakthrough test

**Date:** 2026-11-23.  
**Status:** SELF-CONTAINED PAPER PROOF; NOT YET LEAN-CERTIFIED.  
**Scope:** transverse cap TWO, not a complete cubic-cap or HC4 theorem.

## Theorem

Let K be a characteristic-zero field and n >= 1. If a potential
F in K[x,y_1,...,y_n] has degree <= 2 in the y variables and

    det Hess(F) = delta in K^times,

then its full gradient is a polynomial automorphism of K^(n+1).
There is no bound on degree in x, no algebraic-closure assumption,
and no planar Jacobian conjecture assumption.

The proof directly constructs the polynomial inverse in both
generic transverse-rank cases.

## Single source identity

Since char K = 0, write the **actual potential**

    F(x,y) = a(x) + b(x)^T y + (1/2)y^T C(x)y,

with a in K[x], b in K[x]^n, C in Sym_n(K[x]).
Let v = b' + C'y, D = det C, and prime denote d/dx.

The full Hessian is

    [ a''+b''^T y+(1/2)y^T C''y    v^T ]
    [                 v            C  ].

Its division-free bordered determinant gives the polynomial identity

    delta = D*(a''+b''^T y+(1/2)y^T C''y)
                  - v^T adj(C) v.                         (1)

This identity is valid whether D vanishes or not.

## Case I: det C != 0

Work over K(x), and set M=C^(-1). The quadratic-in-y coefficient
of (1), by symmetry and char K != 2, gives

    C'' = 2 C' M C'.                                       (2)

Differentiate MC = I twice. From M'=-MC'M and (2),

    M'' = 2 M C' M C' M - M C'' M = 0.

A rational function in characteristic zero with zero second derivative
is affine over K. Entrywise,

    M = A + x B,   A,B in Mat_n(K).

Therefore M is already a POLYNOMIAL inverse of C. Taking
determinants in K[x] shows D*det M=1; so D=d is a nonzero
constant. This unimodularity is DERIVED, not assumed.

Given a full gradient output (s,p), p in K^n, define

    y_p(x) = M(x) (p-b(x)).

This is polynomial in x and p, and F_y(x,y_p(x))=p.
Its x derivative satisfies y_p'=-M (b'+C'y_p).
Consequently, with g_p(x)=F_x(x,y_p(x)),

    g_p' = F_xx - F_xy M F_yx
         = (det Hess F)/(det C)
         = delta/d.

The right side is an actual nonzero constant. Therefore

    g_p(x) = g_p(0) + (delta/d)x,

and the polynomial inverse is explicitly

    x = (d/delta) (s-g_p(0)),
    y = M(x) (p-b(x)).

The quantity g_p(0) is polynomial in p.
No nilpotent Jordan form, time-series expansion, or analytic
integration was needed.

## Case II: det C = 0

Putting y=0 in (1) gives

    b'^T adj(C) b' = -delta != 0.                          (3)

In particular adj(C) != 0 and rank C over K(x) is exactly n-1.
Define

    w = adj(C) b'  in K[x]^n.

Then b'^T w=-delta, so w != 0, and Cw=0.
The linear-in-y coefficient of (1) gives C'w=0.
Differentiating Cw=0 therefore yields Cw'=0.

The kernel of C over K(x) is one-dimensional, hence

    w' = lambda*w, lambda in K(x).

But b'^T w' = lambda*b'^T w = -delta*lambda.
Since b' and w' are polynomial, actually

    lambda = -(b'^T w')/delta in K[x].

Thus every nonzero polynomial coordinate w_i divides its own
derivative w_i'. In characteristic zero this forces w_i constant
(the derivative has smaller degree whenever w_i is nonconstant).
The zero coordinates are constant too. Therefore

    w in K^n \ {0}, C(x)w=0, b'(x)^T w=-delta.             (4)

This is a constant kernel and **nonzero affine gradient drift**,
not merely a vanishing cofactor condition.

Choose a constant T in GL_n(K) with T e_n=w, and let y=Tz.
The transformed transverse block is

    Ctilde = [ E(x) 0 ]
             [   0   0 ],

because C is symmetric and Cw=0.
The last transformed coefficient btilde_n(x) satisfies
btilde_n'=w^T b'=-delta=:k != 0. Hence

    btilde_n(x)=k*x+beta.

The full Hessian determinant after the constant coordinate
change is (det T)^2*delta. Expanding along the last row/column
gives

    (det T)^2*delta = -k^2 det E(x).

Therefore det E is a nonzero constant, and E^-1 is polynomial.
The potential is

    Ftilde=a(x)+bperp(x)^T zperp+(kx+beta)z_n
                 +(1/2) zperp^T E(x) zperp.

For any full gradient output (s,pperp,p_n), recover

    x=(p_n-beta)/k,
    zperp=E(x)^(-1)(pperp-bperp(x)),
    z_n=(s-a'(x)-bperp'(x)^T zperp
              -(1/2)zperp^T E'(x)zperp)/k.

All components are polynomials. Undoing T is polynomial too.

**Both cases supply an explicit two-sided polynomial inverse. QED.**

## Strong conceptual invariant

The constant full Hessian determinant and a quadratic transverse
cap force the following exhaustive alternatives, without auxiliary
source assumptions:

1. The transverse Hessian C is unimodular in K[x]; along a fibre
   of the transverse gradient, the longitudinal gradient has
   exactly constant nonzero slope delta/det C.
2. The transverse Hessian has a constant one-dimensional kernel
   direction w with w^T b'=-delta; this makes one combination of
   transverse gradient outputs exactly affine in x.

In either case the nonlinear longitudinal coordinate is recovered
**polynomially**. This is the mechanism to formalize.

## Adversarial test families

(A) Arbitrarily high total degree, cap two:

    F_N(x,u,v,w)=x*u+v*w+x^N*v^2,  N >= 1.

det Hess(F_N)=1 and total degree N+2. The polynomial inverse
of the gradient (s,p_u,p_v,p_w) is

    x=p_u; v=p_w;
    u=s-N*p_u^(N-1)*p_w^2;
    w=p_v-2*p_u^N*p_w.

(B) Nonconstant invertible transverse block:

    F=-(1/2)x^2+u*v-(1/2)x*v^2+(1/2)w^2.

Here det Hess F=1, and

    C=[[0,1,0],[1,-x,0],[0,0,1]], det C=-1.

(C) OUTSIDE the theorem: unbounded-degree cubic-cap rank two:

    G_N=x*u+v*w+u*v^2+x^N*v^3.

It has det Hess G_N=1, transverse cubic Hessian of generic
rank two, and polynomial inverse

    v=p_w; x=p_u-v^2;
    u=p_x-N*x^(N-1)*v^3;
    w=p_v-2*u*v-3*x^N*v^2.

(D) OUTSIDE the theorem: genuine rank-three cubic cap:

    G=x*u+v*w+u^2*w+v^3.

It has det Hess G=1, and the Hessian of its transverse cubic
part has determinant -24*u^2*v != 0. Its inverse is

    u=p_x; v=p_w-u^2;
    w=p_v-3*v^2; x=p_u-2*u*w.

Exact symbolic spot checks of the determinant were carried out
for N=7 in (A), N=7 in (C), and examples (B) and (D).
These checks are independent smoke tests, NOT a substitute for
the proof covering all coefficients.

## Literature and novelty caution

- M. de Bondt, *Polynomials with constant Hessian determinants in
  dimension three* (2015), https://arxiv.org/abs/1203.6605:
  its dimensional hypothesis does not alone cover general n here.
- Ni, *The Quartic Hessian Conjecture in Dimension Four*
  (2026), https://arxiv.org/abs/2608.14217, and
  https://hexagonmath.org/2611.00161v1 describe bounded-total-degree
  results; this theorem is unbounded in x.
- Meng--Yang, *A five-variable counterexample to the Hessian
  conjecture* (2026), https://arxiv.org/abs/2607.22198:
  the unrestricted assertion is false in dimension >= 5, while
  the quadratic-fibre theorem is a special structured class.
- This search does NOT prove the theorem is unpublished or novel.
  A fuller expert review of classical structured Keller/Hessian
  maps remains necessary before claiming priority.

## Exact Lean and cubic milestones

**Not Lean verified.** The next certification milestone is one
public theorem on the original F, assuming only transverse cap two
and nonzero constant full Hessian determinant and concluding
polynomial two-sided inverse (or at least bijective gradient).
Do not install an assumed Riccati equation, principal pivot,
or endpoint producer in the statement.

The proposed full cubic-cap theorem in
RankTwoTransverseCubic.md / RankThreeTransverseCubic.md is harder:
those notes cover only generic transverse-Hessian ranks two and
three on paper, and the singular-axis treatment of ranks zero/one
does not solve the unrestricted low-rank cubic case.
A genuine rational characteristic pole remains a conceptual
challenge. The complete cubic theorem must cover all ranks
without a marked singular-axis assumption. Another cofactor
calculation without that closure is not the next milestone.
