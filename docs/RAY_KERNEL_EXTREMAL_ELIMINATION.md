# Two successive extremal equations in a rank-three model

This is progress on a restricted source calculation, not terminal impossibility.
The scalar elimination has a Lean proof in
`HC4/Newton/RayKernelExtremalElimination.lean` (CI pending at introduction).
The Hessian coefficient calculations below are exact symbolic checks, not yet
Lean-certified source adapters.

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
The polynomial coordinate change from `(x,y)` to `(u,y)` classifies its
weight-7 solutions as

```
G2 = (A*z+B*w)*u^2 + y*u*Q3 + u*P4 + P7 + y*Q6
Q3 = q0*z^3 + q1*z^2*w + q2*z*w^2 + q3*w^3.
```

Here `Pj,Qj` are arbitrary homogeneous binary polynomials of degree `j`.
Order 3 similarly imposes the kernel equation on the weight-6 layer `G3`.
The script `tools/research/ray_kernel_extremal_probe.py` includes **every**
kernel-compatible `G3`, **every** weight-5 correction `G4`, **every** weight-3
correction `G6`, and all displayed first-layer terms. `G5` cannot occur in a
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

An actual terminal has not been reduced to this model. Arbitrary common
monomials, endpoint power gaps, weights, higher longitudinal degree, and the
possibility of earlier affine Hessian layers require further work. In particular,
globally first Hessian order and first transverse Schur order cannot be silently
identified. No new global-progress constructor or unrestricted HC4 theorem is
asserted here.
