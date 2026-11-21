# Singular transverse axis and the cubic determinant correction

This is a local calculation on the original determinant-one potential, with
marked gradient equality at $(0,0)$ and $(1,0)$. The separate nonsingular-axis
case is not resolved here.

## Lean-checked first determinant jet

Write $x$ for the longitudinal variable and $y$ for the three transverse
variables. Let $b(x)=\partial_y F(x,0)$, $C(x)=\partial_y^2 F(x,0)$,
and let $A(x)=H(F)(x,0)$. The upper right block of $A$ is $b'(x)^T$.
If $\det C=0$, the longitudinal column of $\operatorname{adj} A$ has
the form $(0,n)$, with $Cn=0$ and $b'^T n=1$.

The cubic correction, as a linear form in $y$, has coefficient vector
$$
\rho=-2 C'n.
$$
Indeed, the first derivative of the determinant on the axis is the
adjugate/jet trace pairing. Its mixed entries contribute $2 C'n$, its
longitudinal-longitudinal entry contributes nothing, and its
transverse-transverse entries are exactly the third transverse derivatives
of $F$, hence depend only on $L=[F]_3$.

If $C'n=0$, differentiation gives $Cn'=0$. The vector
$n'-(b'^Tn')n$ is killed by both $C$ and $b'^T$, so invertibility of
$A$ gives $n'=(b'^Tn')n$. Comparing polynomial degrees in a nonzero
component of $n$ makes $b'^Tn'=0$. Then $n$ is constant and
$(b^Tn)'=1$, in conflict with the marked equality $b(0)=b(1)$.
Therefore $\rho\ne0$ and $L\ne0$. Symmetry and differentiation
of $Cn=0$ also give $n^T\rho=0$.

## Paper consequence for cap three

If $F$ has transverse degree at most three, the transverse Hessian
of $L$ has rank at least two over $K(x,y)$. This consequence is
not yet formalised.

Suppose first that $L=a(x)(\ell(x)^Ty)^3$ over $k=K(x)$. Put
$B=(\operatorname{adj} A)_{yy}$. Its contribution to the linear
determinant jet is $6a(\ell^T B\ell)(\ell^T y)$. Since this contribution
is nonzero and orthogonal to $n$, $\ell^T n=0$. The full transverse
Hessian $C+6a(\ell^T y)\ell\ell^T$ therefore kills $n$ for all $y$.

Work over $k[y]$, retaining the source derivatives computed before
localisation. Let $H=H(F)$, $e=(0,n)$ and $s=H_{xy}n$. Then
$H e=s e_0$, so $e=s\operatorname{adj}(H)e_0$ by $\det H=1$.
A nonzero component of $e$ is a unit in $k[y]$. Thus $s$ is a
unit, i.e. constant in $y$. Its degree-one component is
$n^T C'y$, which is nonzero. This contradiction excludes the single
linear-form power.

Finally, a nonzero homogeneous cubic $L$ whose transverse Hessian has
rank one is a cube of a linear form up to scalar over $k$. Euler's
identity makes its gradient a nonzero vector in the image of its Hessian.
Every transverse derivative of that gradient is proportional to it, so
ratios of gradient entries are independent of $y$ in characteristic zero.
Consequently the gradient has fixed direction over $k$, and $L$ depends
only on one $k$-linear form. Rank zero would force $L=0$, which was
already excluded.
