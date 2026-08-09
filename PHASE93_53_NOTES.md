# Phase 93.53 — Kernel blow-up evaluation covariance

Built on the green Phase 93.52.2 integral blow-up constructor.

## Main theorem

`eval_integralKernelBlowupFamily_kernelBlowupSection`

proves, for four source variables,

    eval (kernelBlowupSection kernel slope a)
      (integralKernelBlowupFamily kernel slope P hdiv)
      =
    eval a P.

Thus the coefficientwise construction from Phase 93.52 now has the exact
evaluation meaning of the formal substitution

    Ptilde(X, tau^q T) = P(X,T).

## Monomial identity

`fin4_kernelBlowupSection_monomialProduct` proves that the transformed
kernel coordinate contributes exactly

    tau^(slope * d(kernel))

to a source monomial of exponent `d`.

## Equality transport

`eval_integralKernelBlowupFamily_eq_of_eq` immediately transports equality
of evaluations at two source sections through the integral blow-up.

## Next theorem

The remaining derivative step is now isolated:
- for a non-kernel source derivative, evaluation covariance is unchanged;
- for the kernel derivative, both sides acquire the same cancellable
  `tau^slope` factor.

Once that derivative theorem compiles, exact family-gradient collision
transport follows, and the green Phase 93.51 special-fibre restart theorem
can be invoked directly.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
