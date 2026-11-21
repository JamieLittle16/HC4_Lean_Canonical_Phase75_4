# Line-supported Hessian recurrence closure

> **Status:** PAPER CANDIDATE — not yet Lean verified.
>
> This note records a complete paper-level classification of the one-variable
> finite recurrence arising from a line-supported slice of the twice-refined
> `.pr` carrier. It does **not** claim unrestricted HC4 is proved.

## 1. Setup

Fix positive integers

\[
\alpha,\beta,n,p,q>0
\]

and let

\[
d=(1,-1,-\alpha,-\beta),\qquad r=(0,n,p,q).
\]

A polynomial whose exponent support lies on the lattice line
\(r+\mathbb Z d\) can be written

\[
H(x,y,z,w)=y^n z^p w^q\,b(T),
\qquad
T=\frac{x}{y z^\alpha w^\beta},
\]

where \(b(T)\in K[T]\), \(b(0)\neq0\), and polynomiality of \(H\)
means that every supported exponent

\[
(j,n-j,p-\alpha j,q-\beta j)
\]

is nonnegative.

Assume throughout that \(K\) has characteristic zero and

\[
\det \operatorname{Hess} H=0.
\]

The purpose of this note is to classify all possible finite polynomials
\(b\).

## 2. Euler-scaled Hessian reduction

Let

\[
E=T\frac{d}{dT},\qquad
Z=\frac{Eb}{b}=T\frac{b'}{b}.
\]

Then

\[
\frac{E^2b}{b}=Z^2+EZ.
\]

For a line-supported profile, the Euler-scaled Hessian has the general form

\[
\frac{1}{H}
\operatorname{diag}(x,y,z,w)\,
\operatorname{Hess}(H)\,
\operatorname{diag}(x,y,z,w)
=
rr^T+Z(rd^T+dr^T)+(Z^2+EZ)dd^T
-\operatorname{diag}(r+Zd).
\]

Set

\[
\lambda=r+Zd
=
\bigl(Z,n-Z,p-\alpha Z,q-\beta Z\bigr).
\]

Since

\[
rr^T+Z(rd^T+dr^T)+Z^2dd^T=\lambda\lambda^T,
\]

we obtain the key rank-one perturbation form

\[
M(Z,EZ)
=
\lambda\lambda^T-\operatorname{diag}(\lambda)
+(EZ)dd^T.
\tag{2.1}
\]

For any four-vector \(\lambda\),

\[
\det\bigl(\lambda\lambda^T-\operatorname{diag}\lambda\bigr)
=
\lambda_0\lambda_1\lambda_2\lambda_3
\left(1-\sum_i\lambda_i\right).
\]

Hence, with

\[
\rho=\frac{n+p+q-1}{\alpha+\beta},
\]

the unperturbed determinant is

\[
C(Z)
=
-Z(Z-n)(\alpha Z-p)(\beta Z-q)
\bigl((\alpha+\beta)Z-(n+p+q-1)\bigr).
\tag{2.2}
\]

The inverse of
\(\lambda\lambda^T-\operatorname{diag}\lambda\), in the rational function
field where the displayed factors are invertible, is obtained by the
Sherman--Morrison formula:

\[
\bigl(\lambda\lambda^T-\operatorname{diag}\lambda\bigr)^{-1}
=
-\operatorname{diag}(\lambda_i^{-1})
-\frac{\mathbf 1\mathbf 1^T}{1-\sum_i\lambda_i}.
\]

Therefore

\[
-d^T
\bigl(\lambda\lambda^T-\operatorname{diag}\lambda\bigr)^{-1}d
=S(Z),
\]

where

\[
S(Z)
=
\frac1Z-
\frac1{Z-n}-
\frac{\alpha}{Z-p/\alpha}-
\frac{\beta}{Z-q/\beta}+
\frac{\alpha+\beta}{Z-\rho}.
\tag{2.3}
\]

Applying the matrix determinant lemma to (2.1) gives

\[
\det M(Z,EZ)=C(Z)\bigl(1-S(Z)EZ\bigr).
\tag{2.4}
\]

Since the coordinate diagonal factors and \(H^4\) are nonzero in the
function field, Hessian singularity is equivalent to (2.4) vanishing.

If \(b\) is nonconstant, then \(Z=T b'/b\) is nonconstant. Thus the nonzero
polynomial \(C\) cannot satisfy \(C(Z)=0\) identically. Consequently

\[
S(Z)EZ=1.
\tag{2.5}
\]

This is the complete one-variable recurrence in autonomous form.

## 3. Rational first integral

Define the rational map

\[
\Phi(Z)
=
\frac{Z(Z-\rho)^{\alpha+\beta}}
{(Z-n)(Z-p/\alpha)^\alpha(Z-q/\beta)^\beta}.
\tag{3.1}
\]

Up to an irrelevant nonzero scalar, (2.3) says exactly

\[
\frac{\Phi'(Z)}{\Phi(Z)}=S(Z).
\]

Applying \(E=T\,d/dT\) and using (2.5),

\[
E\bigl(\Phi(Z(T))\bigr)=\Phi(Z(T)).
\]

A rational function \(R(T)\in K(T)\) satisfying \(ER=R\) in characteristic
zero has the form

\[
R(T)=cT
\]

for some constant \(c\). Hence

\[
\Phi(Z(T))=cT.
\tag{3.2}
\]

For nonconstant \(b\), both \(Z(T)\) and \(\Phi\) are nonconstant rational
maps. Degree multiplicativity for rational maps applied to (3.2) gives

\[
\deg\Phi\cdot\deg Z=1.
\]

Thus

\[
\boxed{\deg\Phi=1.}
\tag{3.3}
\]

This converts the entire finite recurrence into a finite root-multiplicity
problem.

## 4. Degree-one classification of the rational map

Before cancellation, the numerator of \(\Phi\) has roots

- \(0\) with multiplicity \(1\);
- \(\rho\) with multiplicity \(\alpha+\beta\).

The denominator has roots

- \(n\) with multiplicity \(1\);
- \(p/\alpha\) with multiplicity \(\alpha\);
- \(q/\beta\) with multiplicity \(\beta\).

Since \(n,p,q>0\), no denominator root is zero. Therefore the numerator root
at zero never cancels. For the reduced map to have degree one, at least
\(\alpha+\beta\) denominator multiplicities must cancel at the *single* other
numerator root \(\rho\).

There are only three possibilities.

### Case I: both large blocks cancel

If

\[
\frac p\alpha=\rho,
\qquad
\frac q\beta=\rho,
\]

then

\[
p=\alpha\rho,\qquad q=\beta\rho.
\]

Using

\[
(\alpha+\beta)\rho=n+p+q-1
\]

gives immediately

\[
\boxed{n=1}.
\]

After cancellation, \(\Phi\) is a nonzero scalar multiple of

\[
\frac Z{Z-1}.
\]

### Case II: the \(p/\alpha\) block is absent from the cancellation

Then the largest possible cancellation multiplicity is \(1+\beta\), so

\[
1+\beta\ge\alpha+\beta.
\]

Hence \(\alpha=1\), and equality forces

\[
n=\rho,
\qquad
\frac q\beta=\rho.
\]

Substituting into the defining equation for \(\rho\) gives

\[
\boxed{p=1}.
\]

Again the reduced map is a nonzero scalar multiple of

\[
\frac Z{Z-1}.
\]

### Case III: the \(q/\beta\) block is absent

Symmetrically, one gets

\[
\beta=1,
\qquad
n=\rho,
\qquad
\frac p\alpha=\rho,
\qquad
\boxed{q=1},
\]

and the same reduced map.

Thus every possible degree-one degeneration has the universal form

\[
\boxed{
\Phi(Z)=\lambda\frac Z{Z-1}
}
\tag{4.1}
\]

for some \(\lambda\neq0\).

## 5. The profile is affine

Combining (3.2) and (4.1), after absorbing constants,

\[
\frac{Z}{Z-1}=\mu T.
\]

Hence

\[
Z=\frac{\nu T}{1+\nu T}
\]

for some nonzero \(\nu\). Recalling

\[
Z=T\frac{b'}b,
\]

we obtain

\[
(1+\nu T)b'=\nu b.
\tag{5.1}
\]

Equation (5.1) is now an ordinary polynomial identity. Comparing coefficients
shows

\[
b_j=0\qquad(j\ge2).
\]

Therefore

\[
\boxed{\deg b\le1.}
\tag{5.2}
\]

If \(b\) is nonconstant then

\[
\boxed{b(T)=c_0+c_1T,\qquad c_0c_1\neq0.}
\]

There is no longer any all-depth finite recurrence: the only allowed
nonconstant line-supported singular slice has exactly two adjacent lattice
monomials.

## 6. Final theorem, paper form

### Line-supported Hessian rigidity

Let \(K\) be a characteristic-zero field. Let
\(\alpha,\beta,n,p,q\in\mathbb N_{>0}\), and let \(b\in K[T]\) satisfy
\(b(0)\neq0\). Suppose

\[
H(x,y,z,w)=y^n z^p w^q
b\!\left(\frac{x}{y z^\alpha w^\beta}\right)
\]

is a polynomial and

\[
\det\operatorname{Hess}H=0.
\]

Then

\[
\boxed{\deg b\le1.}
\]

Equivalently, every nontrivial singular line slice supported in the direction

\[
(1,-1,-\alpha,-\beta)
\]

consists of exactly two adjacent monomials.

The three possible nonconstant parameter patterns are precisely:

1. \(p/\alpha=q/\beta=\rho\), forcing \(n=1\);
2. \(\alpha=1\), \(n=q/\beta=\rho\), forcing \(p=1\);
3. \(\beta=1\), \(n=p/\alpha=\rho\), forcing \(q=1\).

Thus one of the three decreasing endpoint coordinates is already primitive.

## 7. Relation to the `.pr` HC4 seam

For the locked `.pr` ray the line direction is

\[
(1,-1,-sU,-sV),
\qquad s=k-\ell>0,
\]

so

\[
\alpha=sU>0,\qquad\beta=sV>0.
\]

The defect-neutral double refinement discussed in the preceding paper work
reduces every fixed pair-degree slice of the resulting planar exponent carrier
to precisely the line-supported situation above.

Therefore its highest nonzero nonlinear slice is not an arbitrary finite
staircase. It has at most two adjacent monomials, and one of its decreasing
coordinates is forced to be primitive in the exact sense of the three cases
above.

This is the correct next interface for the HC4 proof: feed the resulting
primitive two-monomial top slice into the existing weighted rank-three
boundary-pencil / cyclic endpoint machinery, rather than developing another
all-depth profile recurrence.

## 8. Lean plan

The paper proof is intentionally arranged to minimize new formal machinery.
A Lean implementation can be split into:

1. a state-free Euler-scaled Hessian identity for a line-supported polynomial;
2. the rank-one determinant update giving (2.4);
3. the factorisation (2.2) and logarithmic-derivative identity (2.3);
4. an algebraic rational-function lemma: `E R = R -> R = C * X`;
5. rational-map degree-one cancellation arithmetic over the integer exponent
   parameters;
6. the final polynomial identity `(1 + nu*X) * derivative b = nu*b` implying
   `natDegree b <= 1`;
7. a source-facing adapter from the twice-refined planar carrier to the
   state-free line theorem.

No JC2 hypothesis is used anywhere in this line-supported closure.
