# Two successive extremal equations in a rank-three model

This is progress on a restricted source calculation, not terminal impossibility.
The scalar elimination has a Lean proof in
`HC4/Newton/RayKernelExtremalElimination.lean`. Full Lean CI #1591 passed
at `d7467cc39d36aefe5e0ff40e3b67fdba68b6ca51` (8268 build jobs, axiom
audit, negative control and escape-hatch checks).
The Hessian coefficient calculations below are exact symbolic checks, not yet
Lean-certified source adapters.

## Resolution of the omitted first-layer term

The omitted `k*y*u^2` term is eliminated **before** the lower coefficients are
used. The previously unexamined highest longitudinal coefficient is

```
[t^4*x^4] det Hess = 14580*k^2*w^4*z^4.
```

It forces `k=0` in characteristic zero. The symbolic check in
`tools/research/ray_kernel_top_coefficient_probe.py` enumerates all 27
weight-7 monomials in the kernel coordinates `(u,y,z,w)` with kernel-coordinate
degree at most one. It includes all permitted later corrections and uses the
full Hessian without first specializing `y=0`. The earlier six coefficient
checks then apply. This settles the omitted-term issue in this model; it is
not an arbitrary-terminal source theorem.

`HC4/Newton/LongitudinalRankTwoInitialCoefficient.lean` gives the finite
four-block coefficient identity with arbitrary polynomial tails. Full CI #1603
passed at `9ae6f26accca2d8d871630a19fd7e4b6fa819c30`: 8271 build jobs,
axiom audit, negative control and escape-hatch checks; no new-module warnings.
The first two rows start at order two, the `(0,0)` entry is zero, and the
constant transverse block has nonzero determinant. The order-four coefficient
is exactly minus the square of the `(0,1)` departure times that determinant.
Its specialization gives the displayed factor 14580. For the preceding
longitudinal extraction, Mathlib already supplies
`Matrix.coeff_det_X_add_C_card`; no new determinant-degree infrastructure is
needed. The source-identification hypotheses are not yet derived for arbitrary
terminal rays, whose longitudinal degrees and endpoint exponents can differ.

## Historical scope correction: the additional first-layer kernel term

The order-2 calculation below is restricted to a zero coefficient of `y*u^2`.
The earlier version incorrectly described its first-layer ansatz as exhaustive.
The full weight-7 kernel solution also includes `k*y*u^2`. This term changes
both the outer quadratic equations and the higher equations. The existing
Lean scalar lemmas remain correct under their stated equations; those equations
have not been obtained for this extra branch.

`tools/research/ray_kernel_missing_term_probe.py` checks the corrected coefficients.
In particular,

```
[t^4*x^3] det Hess =
  1944*k*w^4*z^4*(Q3 - 8*w*z*(A*z+B*w))
[t^4*x^2*z^10*w^4] det Hess = 648*(q0^2 - 3*k*[z^6]Q6).
```

Thus the outer coefficient is not a pure square for general `k`. If `k` is
nonzero, the first equation instead forces `Q3=8*w*z*(A*z+B*w)`; subsequent
coefficients still couple to the affine terms. No unrestricted order-2 model
exclusion follows from the old six equations.

## Model and permitted corrections

Use weights `(3,1,1,1)`, level 9, clock 24, and

```
h = z*w
F0 = x*h^3 + y*h^4
u = 3*x + 4*h*y
D = 4*h*partial_x - 3*partial_y
```

The initial Hessian has rank three and kernel `(4*h,-3,0,0)`.
Assume the globally first nonzero positive Hessian layer has order 2.
The first determinant equation implies `D^2 G2 = 0`.
The polynomial coordinate change from `(x,y)` to `(u,y)` gives the full
weight-7 solutions as

```
G2 = (A*z+B*w)*u^2 + k*y*u^2 + y*u*Q3 + u*P4 + P7 + y*Q6
Q3 = q0*z^3 + q1*z^2*w + q2*z*w^2 + q3*w^3.
```

Here `Pj,Qj` are arbitrary homogeneous binary polynomials of degree `j`.
The remainder of this order-2 subsection assumes `k=0`.
Order 3 similarly imposes the kernel equation on the weight-6 layer `G3`.
The script `tools/research/ray_kernel_extremal_probe.py` includes **every**
kernel-compatible `G3`, **every** weight-5 correction `G4`, **every** weight-3
correction `G6`, and all displayed first-layer terms with `k=0`. `G5` cannot occur in a
determinant coefficient of order 4 or 6, since the order-1 Hessian is zero.
Higher layers cannot contribute. Restricting to `y=0` after differentiating
selects exactly the coefficients displayed below.

## Coefficients surviving all these corrections

The determinant coefficients of `t^4*x^2*z^10*w^4` and
`t^4*x^2*z^4*w^10` are `648*q0^2` and `648*q3^2`.
Their vanishing forces `q0=q3=0` over a characteristic-zero field.
After these substitutions, the following four coefficients are:

| Monomial | Coefficient |
|---|---|
| `t^4*x^2*z^8*w^6` | `-2592*A*q1` |
| `t^4*x^2*z^6*w^8` | `-2592*B*q2` |
| `t^6*x^3*z^6*w^3` | `972*A*(64*A^2+8*A*q1+q1^2)` |
| `t^6*x^3*z^3*w^6` | `972*B*(64*B^2+8*B*q2+q2^2)` |

All these parameter orders are below clock 24. Their required vanishing
forces `A=B=0`. Thus a nonlinear quadratic first layer of this specified form
cannot be completed to the determinant clock by the allowed later corrections.
This is stronger than checking an isolated deformation with corrections set
to zero. It does not exclude a nonlinear term first appearing later.

## General-exponent scalar elimination

For `F0=x*h^m+y*h^(m+1)` the corresponding candidate equations, after removing
nonzero numerical and monomial factors, take the form

```
q*((m-3)*q - 4*(m+1)*A) = 0
A*(8*(m+1)^2*A^2 + 4*(m+1)*A*q + (m-1)*q^2) = 0.
```

The Lean theorem `HC4.Newton.ray_kernel_extremal_elimination` proves that these
imply `A=0` whenever `m+1` and `m-1` are nonzero, including every integer `m>=3`.
It does not assume orderability or divide by `m-3`.
Writing `T` for the bracket in the second equation and

```
Q = 8*A*m^2 - 8*A*m - 16*A + q*(m^2-4*m+3),
```

the certificate is

```
(m-3)^2*T - Q*((m-3)*q-4*(m+1)*A)
  = 8*(m+1)^2*(m-1)^2*A^2.
```

If `q=0`, the second equation directly eliminates `A`. Otherwise the first
equation and this certificate eliminate it. This finite algebra is independent
of the unresolved geometric adapters.

## Remaining coverage

### First-order extension in the same weight system

`tools/research/ray_kernel_order_one_probe.py` also treats the entire
kernel-compatible weight-8 first layer, with arbitrary weight-7 and weight-6
corrections. Its highest longitudinal part is

```
u^2*(a*z^2+b*z*w+c*w^2) + y*u^2*(d*z+e*w).
```

All lower longitudinal terms are included. At order 2, the coefficient of
`x^4` is `729*w^4*z^4*(17*d^2*z^2+30*d*e*w*z+17*e^2*w^2)`.
The extreme coefficients force `d=e=0`. Write the remaining `y*u` term as
`y*u*sum(qi*z^(4-i)*w^i)`. The outer coefficients then force `q0=q4=0`,
and the next pair gives, up to nonzero constants,

```
q1*(q1-32*a) = 0
a*(64*a^2-8*a*q1+q1^2) = 0,
```

with the symmetric pair for `c,q3`. Hence `a=c=0`.
The new `ray_kernel_order_one_extremal_elimination` Lean theorem proves
this scalar step using the more general
`quadratic_cubic_extremal_elimination` (full CI #1593 passed at
`9cd89d77c5a81c550cc966bdd567ae8c73545e10`, including all proof audits).
The latter needs only a field and two explicitly nonzero elimination scalars.

The middle coefficient `b` survives this calculation. Its `x^2*z*w` monomial
has three supported coordinates, whereas the eliminated `x^2*z^2` and
`x^2*w^2` terms have two. The surviving term can affect later layers, so
this first-order calculation and the order-2 calculation cannot simply be
combined into a complete model exclusion.

### Conditional endpoint if all layers depend on the same monomial

If the **entire** source is `F=f(x,y,h)` with `h=z*w`, direct Hessian expansion
gives

```
det Hess_(x,y,z,w) F
  = -f_h * (f_h * det Hess_(x,y) f + 2*h * det Hess_(x,y,h) f).
```

Thus determinant one forces the substituted polynomial `f_h(x,y,z*w)` to
be a unit, hence constant over a field. This is incompatible with the displayed
leading rank-three ray. The displayed Hessian calculation is checked
at the end of `ray_kernel_extremal_probe.py`. The new owner
`HC4/Newton/ProductCoordinateHessian.lean` now supplies the actual polynomial
substitution, chain rule, Hessian equality, determinant factorization and
constant-unit consequence (full CI #1596 passed at
`fb223970a284a82ca64634fb11c6c451c30cfe64`). The follow-up coefficient
exclusion and actual-terminal adapter passed full CI #1601 at
`8cab1f3d01147470d687db6fa6802ae228fb1f3c`, including all proof audits. Crucially, the actual later source layers
have **not** been shown to depend only on `x,y,z*w`. This is a conditional
endpoint for a possible support argument, not an exclusion of those layers.

An actual terminal has not been reduced to this model. Arbitrary common
monomials, endpoint power gaps, weights, higher longitudinal degree, and the
possibility of earlier affine Hessian layers require further work. In particular,
globally first Hessian order and first transverse Schur order cannot be silently
identified. No new global-progress constructor or unrestricted HC4 theorem is
asserted here.


## Actual terminal adapter

`AdaptiveAlignedSmithCanonicalZeroStrictLowRayProductCoordinateExclusion`
uses the retained `.qs` ray monomial on the actual determinant-one source.
`QsOtherFacetRayReverseReesPackage.source_ne_productCoordinateLift` rules out
any equality of that source with `productCoordinateLift f`. Its proof uses
source coefficient membership obtained through the actual initial-form equality,
not an identification of the source with the ray. The source coefficient theorem
permits only the pure `z*w` monomial among supported monomials involving `z`;
the retained ray monomial has positive `y` and `z` exponents.

Thus the whole-source common-product branch, including `x^2*z*w` and all later
common-product terms, has an exact contradiction consumer. The open branch is
an actual later source layer outside this form. This patch does not show that
such a layer is impossible or supplies a certified global transition.


The product-coordinate owner has 14 transitive HC4 modules in its local import
closure and no JC2 module dependencies. No unrestricted HC4 theorem has been
added. The scope correction above concerns symbolic source-equation coverage;
it does not invalidate any of the compiled scalar or source-level theorems.


## Mixed quadratic boundary: unrestricted lower polynomials

The next calculation uses the entire source, without choosing a Rees layer:

```
F = (b*z*w + g + k*y)*x^2 + B(y,z,w)*x + C(y,z,w).
```

The terms linear in `z,w` in the coefficient of `x^2` can be removed by
translations when `b` is nonzero. This observation does not bound the
longitudinal degree of an arbitrary terminal; that reduction remains open.
No product-coordinate hypothesis is imposed on `B` or `C`.

The exact full-Hessian coefficients are

```
[x^6] det Hess F = 4*b^2*k^2
[x^5] det Hess F (after k=0) = 2*b^2*(3*b*z*w-g)*B_yy.
```

In a characteristic-zero polynomial domain, `b != 0` and determinant one
therefore give `k=0` and `B_yy=0`. Write `B=y*p(z,w)+q(z,w)`. Then

```
[x^4] det Hess F =
  2*b^2*(3*b*z*w-g)*C_yy
  + b*(4*b*w^2*p_w^2 - 4*b*w*z*p_w*p_z - 4*b*w*p*p_w
       + 4*b*z^2*p_z^2 - 4*b*z*p*p_z + b*p^2 + 4*g*p_w*p_z).
```

The second summand is independent of `y`. Differentiating this equation
in `y` forces `C_yyy=0`, so this conditional source branch becomes quadratic
in both `x` and `y`. This last polynomial-derivative inference and the source
identification are not yet formalized. Quadraticity alone is not terminal
impossibility, and no change of carrier or nonzero minor is assumed.

`HC4/Newton/QuadraticLongitudinalHessianBoundary.lean` formalizes the three
coefficient identities and the first two scalar elimination consumers with
all lower jets arbitrary (CI pending). The independently differentiated
source calculation is checked by
`tools/research/quadratic_longitudinal_boundary_probe.py`.
